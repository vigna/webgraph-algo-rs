/// Returns the index of the maximum value in the slice `vec` if found, [`None`] otherwise.
///
/// # Arguments
/// - `vec`: the slice of elements.
///
/// # Examples
/// ```
/// use webgraph_algo::utils::math::argmax;
///
/// let v = vec![1, 2, 5, 2, 1];
/// let index = argmax(&v);
/// assert_eq!(index, Some(2));
/// ```
pub fn argmax<T: common_traits::FiniteRangeNumber>(vec: &[T]) -> Option<usize> {
    let mut max = T::MIN;
    let mut argmax = None;
    for (i, &elem) in vec.iter().enumerate() {
        if elem > max {
            argmax = Some(i);
            max = elem;
        }
    }
    argmax
}

/// Returns the index of the maximum value approved by `filter` in the slice `vec` if found, [`None`] otherwise.
///
/// In case of ties, the index for which `tie_break` is maximized is returned.
///
/// # Arguments
/// - `vec`: the slice of elements.
/// - `tie_break`: in case two elements of `vec` are the same, the index that maximises this slice is used.
/// - `filter`: a closure that takes as arguments the index of the element and the element itself and returns
/// `true` if the element may be selected.
///
/// # Examples
/// ```
/// use webgraph_algo::utils::math::filtered_argmax;
///
/// let v = vec![1, 2, 5, 2, 1];
/// let tie = vec![1, 2, 3, 4, 5];
/// let index = filtered_argmax(&v, &tie, |_, element| element < 4);
/// assert_eq!(index, Some(3));
/// ```
pub fn filtered_argmax<
    T: common_traits::FiniteRangeNumber,
    N: common_traits::FiniteRangeNumber,
    F: Fn(usize, T) -> bool,
>(
    vec: &[T],
    tie_break: &[N],
    filter: F,
) -> Option<usize> {
    let mut max = T::MIN;
    let mut max_tie_break = N::MIN;
    let mut argmax = None;

    for (i, (&elem, &tie)) in vec.iter().zip(tie_break.iter()).enumerate() {
        if filter(i, elem) && (elem > max || (elem == max && tie > max_tie_break)) {
            argmax = Some(i);
            max = elem;
            max_tie_break = tie;
        }
    }

    argmax
}
