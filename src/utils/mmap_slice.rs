use anyhow::{ensure, Context, Result};
use common_traits::UnsignedInt;
use mmap_rs::{MmapFlags, MmapMut, MmapOptions};
use std::{fs::File, marker::PhantomData, mem::size_of, path::Path};
use tempfile::tempfile;

pub struct MmapSlice<T> {
    _file: File,
    mmap: Option<MmapMut>,
    len: usize,
    _marker: PhantomData<T>,
}

impl<T: Clone> MmapSlice<T> {
    pub fn new(file: File, flags: MmapFlags) -> Result<Self> {
        let file_len: usize = file
            .metadata()
            .with_context(|| "Cannot retrieve file metadata")?
            .len()
            .try_into()
            .with_context(|| "Cannot convert to usize")?;
        let mmap_len = file_len.align_to(size_of::<T>());

        if mmap_len == 0 {
            return Ok(MmapSlice {
                _file: file,
                mmap: None,
                len: 0,
                _marker: PhantomData,
            });
        }

        ensure!(
            mmap_len == file_len,
            "file len is not of the correct length for element of size {}",
            size_of::<T>()
        );

        let mmap = unsafe {
            MmapOptions::new(mmap_len)
                .with_context(|| format!("Cannot initialize mmap of size {}", mmap_len))?
                .with_file(&file, 0)
                .with_flags(flags)
                .map_mut()
                .with_context(|| "Cannot mutably mmap")?
        };

        Ok(Self {
            _file: file,
            mmap: Some(mmap),
            len: mmap_len / size_of::<T>(),
            _marker: PhantomData,
        })
    }

    pub fn with_path(path: impl AsRef<Path>, flags: MmapFlags) -> Result<Self> {
        let file = File::open(path.as_ref()).with_context(|| "Cannot open file for mmap")?;
        Self::new(file, flags)
    }

    pub fn new_tempfile(len: usize, flags: MmapFlags) -> Result<Self> {
        let file = tempfile().with_context(|| "Cannot create tempfile")?;
        let expected_len = size_of::<T>() * len;
        file.set_len(
            expected_len
                .try_into()
                .with_context(|| "Cannot convert file len")?,
        )
        .with_context(|| "Cannot set file length")?;
        Self::new(file, flags)
    }

    pub fn from_vec(v: Vec<T>, flags: MmapFlags) -> Result<Self> {
        let len = v.len();
        let mut mmap = Self::new_tempfile(len, flags)
            .with_context(|| format!("Cannot create tempfile mmap of len {}", len))?;
        mmap.as_mut().clone_from_slice(&v);
        Ok(mmap)
    }
}

impl<T> AsRef<[T]> for MmapSlice<T> {
    fn as_ref(&self) -> &[T] {
        if let Some(mmap) = self.mmap.as_ref() {
            unsafe { std::slice::from_raw_parts(mmap.as_ptr() as *const T, self.len) }
        } else {
            &[]
        }
    }
}

impl<T> AsMut<[T]> for MmapSlice<T> {
    fn as_mut(&mut self) -> &mut [T] {
        if let Some(mmap) = self.mmap.as_mut() {
            unsafe { std::slice::from_raw_parts_mut(mmap.as_mut_ptr() as *mut T, self.len) }
        } else {
            &mut []
        }
    }
}
