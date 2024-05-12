use anyhow::{ensure, Context, Result};
use mmap_rs::{MmapFlags, MmapMut, MmapOptions};
use std::{
    fs::File,
    mem::size_of,
    ops::{Deref, DerefMut},
    path::PathBuf,
};
use tempfile::{tempfile, tempfile_in};

#[derive(Debug, Clone)]
pub enum TempMmapOptions {
    None,
    TempDir(MmapFlags),
    CustomDir((PathBuf, MmapFlags)),
}

pub struct MmapSlice<T> {
    mmap: Option<(File, MmapMut, usize)>,
    in_memory_vec: Vec<T>,
}

impl<T: Clone> MmapSlice<T> {
    const BLOCK_SIZE: usize = size_of::<T>();

    pub fn new(file: File, flags: MmapFlags) -> Result<Self> {
        let file_len: usize = file
            .metadata()
            .with_context(|| "Cannot retrieve file metadata")?
            .len()
            .try_into()
            .with_context(|| "Cannot convert to usize")?;
        let mmap_len =
            file_len + (Self::BLOCK_SIZE - (file_len % Self::BLOCK_SIZE)) % Self::BLOCK_SIZE;

        if mmap_len == 0 {
            return Ok(MmapSlice {
                mmap: None,
                in_memory_vec: Vec::new(),
            });
        }

        ensure!(
            mmap_len == file_len,
            "file len is not of the correct length for element of size {}",
            Self::BLOCK_SIZE
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
            mmap: Some((file, mmap, mmap_len / Self::BLOCK_SIZE)),
            in_memory_vec: Vec::new(),
        })
    }

    pub fn from_vec(v: Vec<T>, options: TempMmapOptions) -> Result<Self> {
        match options {
            TempMmapOptions::None => Ok(Self {
                mmap: None,
                in_memory_vec: v,
            }),
            TempMmapOptions::TempDir(flags) => Ok(Self::from_tempfile_and_vec(
                v,
                tempfile().with_context(|| "Cannot create tempfile in temporary directory")?,
                flags,
            )
            .with_context(|| "Cannot create mmap in temporary directory")?),
            TempMmapOptions::CustomDir((dir, flags)) => Ok(Self::from_tempfile_and_vec(
                v,
                tempfile_in(dir.as_path()).with_context(|| {
                    format!("Cannot create tempfile in directory {}", dir.display())
                })?,
                flags,
            )
            .with_context(|| format!("Cannot create mmap in directory {}", dir.display()))?),
        }
    }

    fn from_tempfile_and_vec(v: Vec<T>, file: File, flags: MmapFlags) -> Result<Self> {
        let expected_len = v.len() * Self::BLOCK_SIZE;
        file.set_len(
            expected_len
                .try_into()
                .with_context(|| "Cannot convert file len")?,
        )
        .with_context(|| format!("Cannot set file len to {} bytes", expected_len))?;

        let mut mmap =
            Self::new(file, flags).with_context(|| "Cannot create mmap from tempfile")?;

        mmap.as_mut().clone_from_slice(v.as_slice());

        Ok(mmap)
    }
}

impl<T> AsRef<[T]> for MmapSlice<T> {
    fn as_ref(&self) -> &[T] {
        if let Some((_, mmap, len)) = self.mmap.as_ref() {
            unsafe { std::slice::from_raw_parts(mmap.as_ptr() as *const T, *len) }
        } else {
            self.in_memory_vec.as_slice()
        }
    }
}

impl<T> AsMut<[T]> for MmapSlice<T> {
    fn as_mut(&mut self) -> &mut [T] {
        if let Some((_, mmap, len)) = self.mmap.as_mut() {
            unsafe { std::slice::from_raw_parts_mut(mmap.as_mut_ptr() as *mut T, *len) }
        } else {
            self.in_memory_vec.as_mut_slice()
        }
    }
}

impl<T> Deref for MmapSlice<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<T> DerefMut for MmapSlice<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut()
    }
}
