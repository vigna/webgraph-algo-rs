/// Returns the index of the minimum value in the slice `vec` if found, [`None`] otherwise.
/// If several elements are equally minimum, the first element is returned.
///
/// # Arguments
/// * `vec`: the slice of elements.
///
/// # Examples
/// ```
/// # use webgraph_algo::utils::math::argmin;
/// let v = vec![4, 3, 1, 0, 5];
/// let index = argmin(&v);
/// assert_eq!(index, Some(3));
/// ```
pub fn argmin<T: std::cmp::PartialOrd + Copy>(vec: &[T]) -> Option<usize> {
    vec.iter()
        .enumerate()
        .min_by(|a, b| a.1.partial_cmp(b.1).unwrap())
        .map(|m| m.0)
}

/// Returns the index of the minimum value approved by `filter` in the slice `vec` if found, [`None`] otherwise.
///
/// In case of ties, the index for which `tie_break` is minimized is returned.
/// If several elements are equally minimum, the first element is returned.
///
/// # Arguments
/// * `vec`: the slice of elements.
/// * `tie_break`: in case two elements of `vec` are the same, the index that minimizes this slice is used.
/// * `filter`: a closure that takes as arguments the index of the element and the element itself and returns
///   `true` if the element may be selected.
///
/// # Examples
/// ```
/// # use webgraph_algo::utils::math::filtered_argmin;
/// let v = vec![3, 2, 5, 2, 3];
/// let tie = vec![5, 4, 3, 2, 1];
/// let index = filtered_argmin(&v, &tie, |_, element| element > 1);
/// assert_eq!(index, Some(3));
/// ```
pub fn filtered_argmin<
    T: std::cmp::PartialOrd + Copy,
    N: std::cmp::PartialOrd + Copy,
    F: Fn(usize, T) -> bool,
>(
    vec: &[T],
    tie_break: &[N],
    filter: F,
) -> Option<usize> {
    vec.iter()
        .zip(tie_break.iter())
        .enumerate()
        .filter(|v| filter(v.0, *v.1 .0))
        .min_by(|a, b| {
            let (value_a, tie_a) = a.1;
            let (value_b, tie_b) = b.1;
            let mut cmp = value_a.partial_cmp(value_b).unwrap();
            if cmp == std::cmp::Ordering::Equal {
                cmp = tie_a.partial_cmp(tie_b).unwrap();
            }
            cmp
        })
        .map(|m| m.0)
}
