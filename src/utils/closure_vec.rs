/// Creates a [`Vec`] where each value is created calling the passed closure.
///
/// # Arguments
/// * `closure`: the closure called to initialize each value of the [`Vec`].
/// * `length`: the length of the created [`Vec`].
///
/// # Examples
/// ```
/// # use webgraph_algo::utils::closure_vec;
/// let v = closure_vec(|| 42, 5);
/// assert_eq!(v, vec![42, 42, 42, 42, 42]);
/// ```
#[inline(always)]
pub fn closure_vec<T>(mut closure: impl FnMut() -> T, length: usize) -> Vec<T> {
    (0..length).map(|_| closure()).collect()
}
