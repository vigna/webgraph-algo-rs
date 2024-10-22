use anyhow::Result;
use webgraph_algo::utils::{MmapFlags, MmapSlice, TempMmapOptions};

#[test]
fn test_from_vec_in_memory() -> Result<()> {
    let v: Vec<usize> = (0..100).collect();
    let mmap_slice = MmapSlice::from_vec(v.clone(), TempMmapOptions::None)?;

    assert_eq!(mmap_slice.as_slice(), v.as_slice());

    Ok(())
}

#[test]
fn test_from_vec_tempfile() -> Result<()> {
    let v: Vec<usize> = (0..100).collect();
    let mmap_slice = MmapSlice::from_vec(v.clone(), TempMmapOptions::TempDir(MmapFlags::empty()))?;

    assert_eq!(mmap_slice.as_slice(), v.as_slice());

    Ok(())
}

#[test]
fn test_from_value_in_memory() -> Result<()> {
    let value: usize = 42;
    let v = vec![value; 100];
    let mmap_slice = MmapSlice::from_value(value, 100, TempMmapOptions::None)?;

    assert_eq!(mmap_slice.as_slice(), v.as_slice());

    Ok(())
}

#[test]
fn test_from_value_tempfile() -> Result<()> {
    let value: usize = 42;
    let v = vec![value; 100];
    let mmap_slice =
        MmapSlice::from_value(value, 100, TempMmapOptions::TempDir(MmapFlags::empty()))?;

    assert_eq!(mmap_slice.as_slice(), v.as_slice());

    Ok(())
}

#[test]
fn test_new_in_memory() -> Result<()> {
    let v = vec![usize::default(); 100];
    let mmap_slice = MmapSlice::<usize>::from_default(100, TempMmapOptions::None)?;

    assert_eq!(mmap_slice.as_slice(), v.as_slice());

    Ok(())
}

#[test]
fn test_new_tempfile() -> Result<()> {
    let v = vec![usize::default(); 100];
    let mmap_slice =
        MmapSlice::<usize>::from_default(100, TempMmapOptions::TempDir(MmapFlags::empty()))?;

    assert_eq!(mmap_slice.as_slice(), v.as_slice());

    Ok(())
}

#[test]
fn test_mutability_in_memory() -> Result<()> {
    let v: Vec<usize> = (0..100).collect();
    let mut mmap_slice = MmapSlice::from_default(100, TempMmapOptions::None)?;

    for (i, value) in mmap_slice.as_mut_slice().iter_mut().enumerate() {
        *value = v[i];
    }

    assert_eq!(mmap_slice.as_slice(), v.as_slice());

    Ok(())
}

#[test]
fn test_mutability_tempfile() -> Result<()> {
    let v: Vec<usize> = (0..100).collect();
    let mut mmap_slice =
        MmapSlice::from_default(100, TempMmapOptions::TempDir(MmapFlags::empty()))?;

    for (i, value) in mmap_slice.as_mut_slice().iter_mut().enumerate() {
        *value = v[i];
    }

    assert_eq!(mmap_slice.as_slice(), v.as_slice());

    Ok(())
}

#[test]
fn test_slice_tempfile() -> Result<()> {
    let mut v: Vec<usize> = (0..100).collect();
    let mut mmap_slice =
        MmapSlice::from_vec(v.clone(), TempMmapOptions::TempDir(MmapFlags::empty()))?;

    assert_eq!(mmap_slice.as_slice(), &mmap_slice[..]);
    assert_eq!(mmap_slice.as_mut_slice(), &mut v[..]);
    assert_eq!(&mut mmap_slice[..], &mut v[..]);

    Ok(())
}
