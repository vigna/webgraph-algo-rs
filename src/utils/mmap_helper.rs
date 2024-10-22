use anyhow::{ensure, Context, Result};
use common_traits::UnsignedInt;
use core::fmt::Debug;
use mmap_rs::{Mmap, MmapMut, MmapOptions};
use std::{
    fs::File,
    mem::size_of,
    ops::{Deref, DerefMut},
    path::*,
    sync::Arc,
};
use tempfile::{tempfile, tempfile_in};

#[doc(hidden)]
pub use mmap_rs::MmapFlags;

/// Helper struct providing convenience methods and type-based [`AsRef`] access
/// to an [`Mmap`] or [`MmapMut`] instance.
///
/// The parameter `W` defines the type of the slice used to access the [`Mmap`]
/// or [`MmapMut`] instance. Usually, this will be a unsigned type such as
/// `usize`, but per se `W` has no trait bounds.
///
/// If the length of the file is not a multiple of the size of `W`, the behavior
/// of [`mmap`](MmapHelper::mmap) is platform-dependent:
/// - on Linux, files will be silently zero-extended to the smallest length that
///   is a multiple of  the size of `W`;
/// - on Windows, an error will be returned; you will have to pad manually the
///   file using the `pad` command of the `webgraph` CLI.
///
/// On the contrary, [`mmap_mut`](MmapHelper::mmap_mut) will always refuse to
/// map a file whose length is not a multiple of the size of `W`.
///
/// If you need clonable version of this structure, consider using
/// [`ArcMmapHelper`].
#[derive(Clone)]
pub struct MmapHelper<W, M = Mmap> {
    /// The underlying memory mapping, [`Mmap`] or [`MmapMut`].
    mmap: M,
    /// The length of the mapping in `W`'s.
    len: usize,
    _marker: core::marker::PhantomData<W>,
}

impl<W: Debug> Debug for MmapHelper<W, Mmap> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("MmapHelper")
            .field("mmap", &self.mmap.as_ptr())
            .field("len", &self.len)
            .finish()
    }
}

impl<W: Debug> Debug for MmapHelper<W, MmapMut> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("MmapHelper")
            .field("mmap", &self.mmap.as_ptr())
            .field("len", &self.len)
            .finish()
    }
}

impl<W> TryFrom<Mmap> for MmapHelper<W> {
    type Error = anyhow::Error;

    fn try_from(value: Mmap) -> std::prelude::v1::Result<Self, Self::Error> {
        ensure!(
            value.len() % size_of::<W>() == 0,
            "The size of the mmap is not a multiple of the size of W"
        );
        let len = value.len() / size_of::<W>();
        Ok(Self {
            len,
            mmap: value,
            _marker: core::marker::PhantomData,
        })
    }
}

impl<W> MmapHelper<W> {
    /// Returns the size of the memory mapping in `W`'s.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns whether the memory mapping is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        // make clippy happy
        self.len == 0
    }

    /// Maps a file into memory (read-only).
    ///
    /// # Arguments
    /// - `path`: The path to the file to be memory mapped.
    /// - `flags`: The flags to be used for the mmap.
    pub fn mmap(path: impl AsRef<Path>, flags: MmapFlags) -> Result<Self> {
        let file_len: usize = path
            .as_ref()
            .metadata()
            .with_context(|| format!("Cannot stat {}", path.as_ref().display()))?
            .len()
            .try_into()
            .with_context(|| "Cannot convert file length to usize")?;
        // Align to multiple of size_of::<W>
        let mmap_len = file_len.align_to(size_of::<W>());
        #[cfg(windows)]
        {
            ensure!(
                mmap_len == file_len,
                "File has insufficient padding for word size {}. Use \"webgraph run pad BASENAME u{}\" to ensure sufficient padding.", size_of::<W>() * 8, size_of::<W>() * 8
            );
        }
        let file = std::fs::File::open(path.as_ref())
            .with_context(|| "Cannot open file for MmapHelper")?;

        let mmap = unsafe {
            // Length must be > 0, or we get a panic.
            mmap_rs::MmapOptions::new(mmap_len.max(size_of::<W>()))
                .with_context(|| format!("Cannot initialize mmap of size {}", mmap_len))?
                .with_flags(flags)
                .with_file(&file, 0)
                .map()
                .with_context(|| {
                    format!(
                        "Cannot mmap {} (size {})",
                        path.as_ref().display(),
                        mmap_len
                    )
                })?
        };

        Ok(Self {
            len: mmap_len / core::mem::size_of::<W>(),
            mmap,
            _marker: core::marker::PhantomData,
        })
    }
}

impl<W> MmapHelper<W, MmapMut> {
    /// Maps a file into memory (read/write).
    ///
    /// # Arguments
    /// - `path`: The path to the file to be mapped.
    /// - `flags`: The flags to be used for the mmap.
    pub fn mmap_mut(path: impl AsRef<Path>, flags: MmapFlags) -> Result<Self> {
        let file_len: usize = path
            .as_ref()
            .metadata()
            .with_context(|| format!("Cannot stat {}", path.as_ref().display()))?
            .len()
            .try_into()
            .with_context(|| "Cannot convert file length to usize")?;
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(path.as_ref())
            .with_context(|| {
                format!(
                    "Cannot open {} for mutable MmapHelper",
                    path.as_ref().display()
                )
            })?;

        // Align to multiple of size_of::<W>
        let mmap_len = file_len.align_to(size_of::<W>());

        ensure!(mmap_len == file_len, "File has insufficient padding for word size {}. Use \"webgraph pad BASENAME u{}\" to ensure sufficient padding.", size_of::<W>(), size_of::<W>() * 8);

        let mmap = unsafe {
            mmap_rs::MmapOptions::new(mmap_len.max(1))
                .with_context(|| format!("Cannot initialize mmap of size {}", file_len))?
                .with_flags(flags)
                .with_file(&file, 0)
                .map_mut()
                .with_context(|| {
                    format!(
                        "Cannot mutably mmap {} (size {})",
                        path.as_ref().display(),
                        file_len
                    )
                })?
        };

        Ok(Self {
            len: mmap.len() / core::mem::size_of::<W>(),
            mmap,
            _marker: core::marker::PhantomData,
        })
    }

    /// Creates and maps a file into memory (read/write), overwriting it if it exists.
    ///
    /// # Arguments
    /// - `path`: The path to the file to be created.
    /// - `flags`: The flags to be used for the mmap.
    /// - `len`: The length of the file in `W`'s.
    pub fn new(path: impl AsRef<Path>, flags: MmapFlags, len: usize) -> Result<Self> {
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(path.as_ref())
            .with_context(|| format!("Cannot create {} new MmapHelper", path.as_ref().display()))?;
        let file_len = len * size_of::<W>();
        #[cfg(windows)]
        {
            // Zero fill the file as CreateFileMappingW does not initialize everything to 0
            file.set_len(
                file_len
                    .try_into()
                    .with_context(|| "Cannot convert usize to u64")?,
            )
            .with_context(|| "Cannot modify file size")?;
        }
        let mmap = unsafe {
            mmap_rs::MmapOptions::new(file_len as _)
                .with_context(|| format!("Cannot initialize mmap of size {}", file_len))?
                .with_flags(flags)
                .with_file(&file, 0)
                .map_mut()
                .with_context(|| format!("Cannot mutably mmap {}", path.as_ref().display()))?
        };

        Ok(Self {
            len: mmap.len() / core::mem::size_of::<W>(),
            mmap,
            _marker: core::marker::PhantomData,
        })
    }
}

impl<W> AsRef<[W]> for MmapHelper<W> {
    #[inline(always)]
    fn as_ref(&self) -> &[W] {
        unsafe { std::slice::from_raw_parts(self.mmap.as_ptr() as *const W, self.len) }
    }
}

impl<W> AsRef<[W]> for MmapHelper<W, MmapMut> {
    #[inline(always)]
    fn as_ref(&self) -> &[W] {
        unsafe { std::slice::from_raw_parts(self.mmap.as_ptr() as *const W, self.len) }
    }
}

impl<W> AsMut<[W]> for MmapHelper<W, MmapMut> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut [W] {
        unsafe { std::slice::from_raw_parts_mut(self.mmap.as_mut_ptr() as *mut W, self.len) }
    }
}

/// A clonable version of a read-only [`MmapHelper`].
///
/// This newtype contains a read-only [`MmapHelper`] wrapped in an [`Arc`],
/// making it possible to clone it.
#[derive(Clone)]
pub struct ArcMmapHelper<W>(pub Arc<MmapHelper<W>>);

impl<W: Debug> Debug for ArcMmapHelper<W> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ArcMmapHelper")
            .field("mmap", &self.0.mmap.as_ptr())
            .field("len", &self.0.len)
            .finish()
    }
}

impl<W> AsRef<[W]> for ArcMmapHelper<W> {
    fn as_ref(&self) -> &[W] {
        unsafe { std::slice::from_raw_parts(self.0.mmap.as_ptr() as *const W, self.0.len) }
    }
}

/// Options for [`MmapSlice`].
/// This determines where data is stored.
#[derive(Debug, Clone)]
pub enum TempMmapOptions {
    /// Data is stored in RAM with options aiming to emulate the behavior of a [`Vec`].
    Default,
    /// Data is stored in RAM with the provided [`MmapFlags`].
    InMemory(MmapFlags),
    /// Data is stored in a tempfile created with [`tempfile::tempfile`] and is memory mapped
    /// using the provided [`MmapFlags`].
    TempDir(MmapFlags),
    /// Data is stored in a tempfile created with [`tempfile::tempfile_in`] using the provided
    /// path and is memory mapped using the provided [`MmapFlags`].
    CustomDir(PathBuf, MmapFlags),
}

/// A utility struct to reduce RAM consumption by allowing storing data in persistent memory and
/// memory mapping it.
///
/// This still allows to choose to keep everything in ram by using [`TempMmapOptions::Default`]
///
/// # Examples
///
/// You can create a [`MmapSlice`] from a value.
/// Note that all constructors return a [`Result`].
///
/// ```
/// use webgraph_algo::utils::*;
/// # use anyhow::Result;
///
/// #
/// # fn main() -> Result<()> {
/// // Create a slice of 100 elements initialized to 42 (type is usually inferred) stored in RAM
/// let mmap_slice: MmapSlice<usize> = MmapSlice::from_value(42, 100, TempMmapOptions::Default)?;
/// # assert_eq!(mmap_slice.as_slice(), vec![42; 100].as_slice());
///
/// // Create a slice of 100 elements initialized to the type's default (type can be inferred
/// // but usually isn't) stored in RAM
/// let mmap_slice: MmapSlice<usize> = MmapSlice::from_default(100, TempMmapOptions::Default)?;
/// # assert_eq!(mmap_slice.as_slice(), vec![0; 100].as_slice());
///
/// // Create a slice from a vec stored in a temporary file created in the default temporary
/// // directory with the SHARED and RANDOM_ACCESS flags (types are explicit only for clarity)
/// let v: Vec<usize> = (0..100).collect();
/// # let c = v.clone();
///
/// let mut flags = MmapFlags::empty();
/// flags.set(MmapFlags::SHARED, true);
/// flags.set(MmapFlags::RANDOM_ACCESS, true);
///
/// let mmap_slice: MmapSlice<usize> = MmapSlice::from_vec(v, TempMmapOptions::TempDir(flags))?;
/// # assert_eq!(mmap_slice.as_slice(), c.as_slice());
/// # Ok(())
/// # }
///
/// ```
pub type MmapSlice<T> = MmapHelper<T, MmapMut>;

impl<T: Default> MmapSlice<T> {
    /// Creates a new slice of length `len` with the provided [`TempMmapOptions`] and with all
    /// the elements initialized to the type's default value.
    ///
    /// # Examples
    ///
    /// ```
    /// use webgraph_algo::utils::*;
    ///
    /// # use anyhow::Result;
    /// # fn main() -> Result<()> {
    /// let slice: MmapSlice<usize> = MmapSlice::from_default(100, TempMmapOptions::Default)?;
    /// # assert_eq!(slice.as_slice(), vec![0usize; 100].as_slice());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Note how the type is not often inferred with this constructor.
    ///
    /// The type may also be specified with the turbofish syntax.
    ///
    /// ```
    /// use webgraph_algo::utils::*;
    ///
    /// # use anyhow::Result;
    /// # fn main() -> Result<()> {
    /// let slice = MmapSlice::<usize>::from_default(100, TempMmapOptions::Default)?;
    /// # assert_eq!(slice.as_slice(), vec![0usize; 100].as_slice());
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn from_default(len: usize, options: TempMmapOptions) -> Result<Self> {
        Self::from_closure(T::default, len, options)
    }
}

impl<T: Clone> MmapSlice<T> {
    /// Creates a new slice of length `len` with the provided [`TempMmapOptions`] and with all
    /// the elements initialized to `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use webgraph_algo::utils::*;
    ///
    /// # use anyhow::Result;
    /// # fn main() -> Result<()> {
    /// let slice = MmapSlice::from_value(0, 100, TempMmapOptions::Default)?;
    /// # assert_eq!(slice.as_slice(), vec![0; 100].as_slice());
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_value(value: T, len: usize, options: TempMmapOptions) -> Result<Self> {
        let mut mmap_slice = match options {
            TempMmapOptions::Default => {
                let mut flags = MmapFlags::empty();
                flags.set(MmapFlags::SHARED, true);
                flags.set(MmapFlags::RANDOM_ACCESS, true);
                Self::from_file_and_len(None, flags, len)
                    .with_context(|| format!("Cannot create mmap of len {} in memory", len))?
            }
            TempMmapOptions::InMemory(flags) => Self::from_file_and_len(None, flags, len)
                .with_context(|| format!("Cannot create mmap of len {} in memory", len))?,
            TempMmapOptions::TempDir(flags) => Self::from_file_and_len(
                Some(tempfile().with_context(|| "Cannot create tempfile in temporary directory")?),
                flags,
                len,
            )
            .with_context(|| format!("Cannot create mmap of len {} in temporary directory", len))?,
            TempMmapOptions::CustomDir(dir, flags) => Self::from_file_and_len(
                Some(tempfile_in(dir.as_path()).with_context(|| {
                    format!("Cannot create tempfile in directory {}", dir.display())
                })?),
                flags,
                len,
            )
            .with_context(|| {
                format!(
                    "Cannot create mmap of len {} in directory {}",
                    len,
                    dir.display()
                )
            })?,
        };
        mmap_slice.fill(value);
        Ok(mmap_slice)
    }
}

impl<T> MmapSlice<T> {
    /// The number of bytes required to store a single element of the slice.
    const BLOCK_SIZE: usize = size_of::<T>();

    fn from_file_and_len(file: Option<File>, flags: MmapFlags, len: usize) -> Result<Self> {
        let mmap_bytes = std::cmp::max(1, len * Self::BLOCK_SIZE);

        if let Some(f) = file.as_ref() {
            f.set_len(
                mmap_bytes
                    .try_into()
                    .with_context(|| format!("Cannot convert {} into u64", mmap_bytes))?,
            )
            .with_context(|| format!("Cannot set file len to {} bytes", mmap_bytes))?;
        }

        let mmap_builder = MmapOptions::new(mmap_bytes)
            .with_context(|| format!("Cannot initialize mmap of size {}", mmap_bytes))?
            .with_flags(flags);

        let mmap = if let Some(f) = file.as_ref() {
            unsafe { mmap_builder.with_file(f, 0) }
        } else {
            mmap_builder
        }
        .map_mut()
        .with_context(|| "Cannot muatbly mmap")?;

        assert!(
            (mmap.as_ptr() as *const T).is_aligned(),
            "mmap pointer is not aligned for {} ({} bytes)",
            std::any::type_name::<T>(),
            std::mem::size_of::<T>()
        );

        Ok(Self {
            mmap,
            len,
            _marker: std::marker::PhantomData,
        })
    }

    /// Creates a new slice from a [`Vec`] with the provided [`TempMmapOptions`].
    ///
    /// # Examples
    ///
    /// ```
    /// use webgraph_algo::utils::*;
    ///
    /// # use anyhow::Result;
    /// # fn main() -> Result<()> {
    /// let v = vec![0; 100];
    /// let slice = MmapSlice::from_vec(v, TempMmapOptions::Default)?;
    /// # assert_eq!(slice.as_slice(), vec![0; 100].as_slice());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Note how this consumes the [`Vec`].
    /// As such the following is illegal and should not compile.
    ///
    /// ```compile_fail
    /// use webgraph_algo::utils::*;
    ///
    /// # use anyhow::Result;
    /// # fn main() -> Result<()> {
    /// let v = vec![0; 100];
    /// let slice = MmapSlice::from_vec(v, TempMmapOptions::Default)?;
    /// assert_eq!(slice.as_slice(), v.as_slice());
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_vec(v: Vec<T>, options: TempMmapOptions) -> Result<Self> {
        match options {
            TempMmapOptions::Default => {
                let mut flags = MmapFlags::empty();
                flags.set(MmapFlags::SHARED, true);
                flags.set(MmapFlags::RANDOM_ACCESS, true);
                Ok(Self::from_file_and_vec(None, flags, v)
                    .with_context(|| "Cannot create mmap in memory")?)
            }
            TempMmapOptions::InMemory(flags) => Ok(Self::from_file_and_vec(None, flags, v)
                .with_context(|| "Cannot create mmap in memory")?),
            TempMmapOptions::TempDir(flags) => Ok(Self::from_file_and_vec(
                Some(tempfile().with_context(|| "Cannot create tempfile in temporary directory")?),
                flags,
                v,
            )
            .with_context(|| "Cannot create mmap in temporary directory")?),
            TempMmapOptions::CustomDir(dir, flags) => Ok(Self::from_file_and_vec(
                Some(tempfile_in(dir.as_path()).with_context(|| {
                    format!("Cannot create tempfile in directory {}", dir.display())
                })?),
                flags,
                v,
            )
            .with_context(|| format!("Cannot create mmap in directory {}", dir.display()))?),
        }
    }

    /// Creates a new slice of length `len` with the provided [`TempMmapOptions`] and with all
    /// the elements initialized to the value returned by `closure`.
    ///
    /// # Examples
    ///
    /// ```
    /// use webgraph_algo::utils::*;
    /// use std::sync::atomic::{AtomicUsize, Ordering};
    ///
    /// # use anyhow::Result;
    /// # fn main() -> Result<()> {
    /// let slice = MmapSlice::from_closure(|| AtomicUsize::new(0), 100, TempMmapOptions::Default)?;
    /// # slice.as_slice().iter().for_each(|n| assert_eq!(n.load(Ordering::Relaxed), 0));
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_closure(
        closure: impl FnMut() -> T,
        len: usize,
        options: TempMmapOptions,
    ) -> Result<Self> {
        let mut mmap_slice = match options {
            TempMmapOptions::Default => {
                let mut flags = MmapFlags::empty();
                flags.set(MmapFlags::SHARED, true);
                flags.set(MmapFlags::RANDOM_ACCESS, true);
                Self::from_file_and_len(None, flags, len)
                    .with_context(|| format!("Cannot create mmap of len {} in memory", len))?
            }
            TempMmapOptions::InMemory(flags) => Self::from_file_and_len(None, flags, len)
                .with_context(|| format!("Cannot create mmap of len {} in memory", len))?,
            TempMmapOptions::TempDir(flags) => Self::from_file_and_len(
                Some(tempfile().with_context(|| "Cannot create tempfile in temporary directory")?),
                flags,
                len,
            )
            .with_context(|| format!("Cannot create mmap of len {} in temporary directory", len))?,
            TempMmapOptions::CustomDir(dir, flags) => Self::from_file_and_len(
                Some(tempfile_in(dir.as_path()).with_context(|| {
                    format!("Cannot create tempfile in directory {}", dir.display())
                })?),
                flags,
                len,
            )
            .with_context(|| {
                format!(
                    "Cannot create mmap of len {} in directory {}",
                    len,
                    dir.display()
                )
            })?,
        };
        mmap_slice.fill_with(closure);
        Ok(mmap_slice)
    }

    fn from_file_and_vec(file: Option<File>, flags: MmapFlags, v: Vec<T>) -> Result<Self> {
        let mut mmap = Self::from_file_and_len(file, flags, v.len())
            .with_context(|| "Cannot create mmap from tempfile")?;

        let v = std::mem::ManuallyDrop::new(v);
        let src = v.as_ptr();
        let dst = mmap.as_mut_ptr();

        unsafe {
            // Safety: regions are non-overlapping and src is dropped by this method so
            // only dst can be read
            std::ptr::copy_nonoverlapping(src, dst, v.len());
        }

        Ok(mmap)
    }

    /// Extracts a slice containing the entire data.
    ///
    /// Equivalent to `&s[..]`
    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        self.as_ref()
    }

    /// Extracts a mutable slice containing the entire data.
    ///
    /// Equivalent to `&mut s[..]`
    #[inline(always)]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.as_mut()
    }
}

impl<T> Deref for MmapSlice<T> {
    type Target = [T];

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<T> DerefMut for MmapSlice<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut()
    }
}
