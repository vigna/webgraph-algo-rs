/// Returns the index of the maximum value in the slice `vec` if found, [`None`] otherwise.
///
/// # Arguments
/// - `vec`: the slice of elements.
///
/// # Examples
/// ```
/// # use webgraph_algo::utils::math::argmax;
/// let v = vec![1, 2, 5, 2, 1];
/// let index = argmax(&v);
/// assert_eq!(index, Some(2));
/// ```
pub fn argmax<T: std::cmp::PartialOrd + Copy>(vec: &[T]) -> Option<usize> {
    if vec.is_empty() {
        return None;
    }
    let mut max = vec[0];
    let mut argmax = Some(0);
    for (i, &elem) in vec.iter().enumerate().skip(1) {
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
    let mut iter = vec.iter().zip(tie_break.iter()).enumerate();
    let mut argmax = None;

    while let Some((i, (&elem, &tie))) = iter.next() {
        if filter(i, elem) {
            argmax = Some(i);
            let mut max = elem;
            let mut max_tie_break = tie;

            for (i, (&elem, &tie)) in iter.by_ref() {
                if filter(i, elem) && (elem > max || (elem == max && tie > max_tie_break)) {
                    argmax = Some(i);
                    max = elem;
                    max_tie_break = tie;
                }
            }
        }
    }

    argmax
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_empty() {
        let v: Vec<usize> = Vec::new();
        assert_eq!(argmax(&v), None);
    }

    #[test]
    fn test_single_element_min() {
        let v = vec![usize::MIN];
        assert_eq!(argmax(&v), Some(0));
    }

    #[test]
    fn test_normal() {
        let v = vec![2, 1, 5, 3];
        assert_eq!(argmax(&v), Some(2));
    }

    #[test]
    fn test_duplicates() {
        let v = vec![2, 5, 1, 3, 5];
        assert_eq!(argmax(&v), Some(1));
    }

    #[test]
    fn test_filtered_empty() {
        let v: Vec<usize> = Vec::new();
        let t: Vec<usize> = Vec::new();
        assert_eq!(filtered_argmax(&v, &t, |_, _| true), None);
    }

    #[test]
    fn test_all_filtered_away() {
        let v = vec![2, 1, 5, 3, 1];
        let t = vec![5, 4, 3, 2, 1];
        assert_eq!(filtered_argmax(&v, &t, |_, _| false), None);
    }

    #[test]
    fn test_filtered_single_element_min() {
        let v = vec![usize::MIN];
        let t = vec![usize::MIN];
        assert_eq!(filtered_argmax(&v, &t, |_, _| true), Some(0));
    }

    #[test]
    fn test_filtered_normal() {
        let v = vec![1, 2, 3, 4, 5, 4, 3, 2, 1];
        let t = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
        assert_eq!(filtered_argmax(&v, &t, |_, e| e < 4), Some(6));
    }

    #[test]
    fn test_filtered_duplicates() {
        let v = vec![1, 2, 3, 2, 1];
        let t = vec![1, 2, 3, 2, 1];
        assert_eq!(filtered_argmax(&v, &t, |_, e| e < 3), Some(1));
    }
}
