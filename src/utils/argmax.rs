pub fn argmax<T: common_traits::FiniteRangeNumber>(vec: &[T]) -> isize {
    let mut max = T::MIN;
    let mut argmax = -1;
    for i in 0..vec.len() {
        if vec[i] > max {
            argmax = i.try_into().unwrap();
            max = vec[i];
        }
    }
    argmax
}

pub fn filtered_argmax<T: common_traits::FiniteRangeNumber, N: common_traits::FiniteRangeNumber>(
    vec: &[T],
    tie_break: &[N],
    filter: &[bool],
) -> isize {
    assert_eq!(vec.len(), tie_break.len());
    assert_eq!(vec.len(), filter.len());

    let mut max = T::MIN;
    let mut max_tie_break = N::MIN;
    let mut argmax = -1;

    for i in 0..vec.len() {
        if filter[i] && (vec[i] > max || (vec[i] == max && tie_break[i] > max_tie_break)) {
            argmax = i.try_into().unwrap();
            max = vec[i];
            max_tie_break = tie_break[i];
        }
    }

    argmax
}
