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
