use itertools::Itertools;

/// Returns the index of the maximum value in the slice `vec` if found, [`None`] otherwise.
/// If several elements are equally maximum, the first element is returned.
///
/// # Arguments
/// * `vec`: the slice of elements.
///
/// # Examples
/// ```
/// # use webgraph_algo::utils::math::argmax;
/// let v = vec![1, 2, 5, 2, 1];
/// let index = argmax(&v);
/// assert_eq!(index, Some(2));
/// ```
pub fn argmax<T: std::cmp::PartialOrd + Copy>(vec: &[T]) -> Option<usize> {
    vec.iter()
        .rev()
        .position_max_by(|x, y| unsafe { x.partial_cmp(y).unwrap_unchecked() })
}

/// Returns the index of the maximum value approved by `filter` in the slice `vec` if found, [`None`] otherwise.
///
/// In case of ties, the index for which `tie_break` is maximized is returned.
/// If several elements are equally maximum, the first element is returned.
///
/// # Arguments
/// * `vec`: the slice of elements.
/// * `tie_break`: in case two elements of `vec` are the same, the index that maximizes this slice is used.
/// * `filter`: a closure that takes as arguments the index of the element and the element itself and returns
///   `true` if the element may be selected.
///
/// # Examples
/// ```
/// # use webgraph_algo::utils::math::filtered_argmax;
/// let v = vec![1, 2, 5, 2, 1];
/// let tie = vec![1, 2, 3, 4, 5];
/// let index = filtered_argmax(&v, &tie, |_, element| element < 4);
/// assert_eq!(index, Some(3));
/// ```
pub fn filtered_argmax<
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
        .rev()
        .filter(|v| filter(v.0, *v.1 .0))
        .max_by(|a, b| {
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
