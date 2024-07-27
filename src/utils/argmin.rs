/// Returns the index of the minimum value in the slice `vec` if found, [`None`] otherwise.
///
/// # Arguments
/// - `vec`: the slice of elements.
///
/// # Examples
/// ```
/// # use webgraph_algo::utils::math::argmin;
/// let v = vec![4, 3, 1, 0, 5];
/// let index = argmin(&v);
/// assert_eq!(index, Some(3));
/// ```
pub fn argmin<T: std::cmp::PartialOrd + Copy>(vec: &[T]) -> Option<usize> {
    if vec.is_empty() {
        return None;
    }
    let mut min = vec[0];
    let mut argmin = Some(0);
    for (i, &elem) in vec.iter().enumerate().skip(1) {
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
    let mut iter = vec.iter().zip(tie_break.iter()).enumerate();
    let mut argmin = None;

    while let Some((i, (&elem, &tie))) = iter.next() {
        if filter(i, elem) {
            argmin = Some(i);
            let mut min = elem;
            let mut min_tie_break = tie;

            for (i, (&elem, &tie)) in iter.by_ref() {
                if filter(i, elem) && (elem < min || (elem == min && tie < min_tie_break)) {
                    argmin = Some(i);
                    min = elem;
                    min_tie_break = tie;
                }
            }
        }
    }

    argmin
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_empty() {
        let v: Vec<usize> = Vec::new();
        assert_eq!(argmin(&v), None);
    }

    #[test]
    fn test_single_element_max() {
        let v = vec![usize::MAX];
        assert_eq!(argmin(&v), Some(0));
    }

    #[test]
    fn test_normal() {
        let v = vec![2, 1, 5, 3];
        assert_eq!(argmin(&v), Some(1));
    }

    #[test]
    fn test_duplicates() {
        let v = vec![2, 1, 5, 3, 1];
        assert_eq!(argmin(&v), Some(1));
    }

    #[test]
    fn test_filtered_empty() {
        let v: Vec<usize> = Vec::new();
        let t: Vec<usize> = Vec::new();
        assert_eq!(filtered_argmin(&v, &t, |_, _| true), None);
    }

    #[test]
    fn test_all_filtered_away() {
        let v = vec![2, 1, 5, 3, 1];
        let t = vec![5, 4, 3, 2, 1];
        assert_eq!(filtered_argmin(&v, &t, |_, _| false), None);
    }

    #[test]
    fn test_filtered_single_element_max() {
        let v = vec![usize::MAX];
        let t = vec![usize::MAX];
        assert_eq!(filtered_argmin(&v, &t, |_, _| true), Some(0));
    }

    #[test]
    fn test_filtered_normal() {
        let v = vec![1, 2, 3, 4, 5, 4, 3, 2, 1];
        let t = vec![9, 8, 7, 6, 5, 4, 3, 2, 1];
        assert_eq!(filtered_argmin(&v, &t, |_, e| e > 2), Some(6));
    }

    #[test]
    fn test_filtered_duplicates() {
        let v = vec![1, 2, 3, 2, 1];
        let t = vec![1, 2, 3, 2, 1];
        assert_eq!(filtered_argmin(&v, &t, |_, e| e > 1), Some(1));
    }
}
