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
