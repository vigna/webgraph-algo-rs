/// Returns the index of the minimum value in the slice `vec` if found, [`None`] otherwise.
///
/// # Arguments
/// - `vec`: the slice of elements.
///
/// # Examples
/// ```
/// use webgraph_algo::utils::math::argmin;
///
/// let v = vec![4, 3, 1, 0, 5];
/// let index = argmin(&v);
/// assert_eq!(index, Some(3));
/// ```
pub fn argmin<T: common_traits::FiniteRangeNumber>(vec: &[T]) -> Option<usize> {
    let mut min = T::MAX;
    let mut argmin = None;
    for (i, &elem) in vec.iter().enumerate() {
        if elem < min {
            argmin = Some(i);
            min = elem;
        }
    }
    argmin
}

/// Returns the index of the minimum value approved by `filter` in the slice `vec` if found, [`None`] otherwise.
///
/// In case of ties, the index for which `tie_break` is minimized is returned.
///
/// # Arguments
/// - `vec`: the slice of elements.
/// - `tie_break`: in case two elements of `vec` are the same, the index that minimises this slice is used.
/// - `filter`: a closure that takes as arguments the index of the element and the element itself and returns
/// `true` if the element may be selected.
///
/// # Examples
/// ```
/// use webgraph_algo::utils::math::filtered_argmin;
///
/// let v = vec![3, 2, 5, 2, 3];
/// let tie = vec![5, 4, 3, 2, 1];
/// let index = filtered_argmin(&v, &tie, |_, element| element > 1);
/// assert_eq!(index, Some(3));
/// ```
pub fn filtered_argmin<
    T: common_traits::FiniteRangeNumber,
    N: common_traits::FiniteRangeNumber,
    F: Fn(usize, T) -> bool,
>(
    vec: &[T],
    tie_break: &[N],
    filter: F,
) -> Option<usize> {
    let mut min = T::MAX;
    let mut min_tie_break = N::MAX;
    let mut argmin = None;

    for (i, (&elem, &tie)) in vec.iter().zip(tie_break.iter()).enumerate() {
        if filter(i, elem) && (elem < min || (elem == min && tie < min_tie_break)) {
            argmin = Some(i);
            min = elem;
            min_tie_break = tie;
        }
    }

    argmin
}
