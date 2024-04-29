#[inline(always)]
pub fn closure_vec<T>(mut closure: impl FnMut() -> T, length: usize) -> Vec<T> {
    (0..length).map(|_| closure()).collect()
}
