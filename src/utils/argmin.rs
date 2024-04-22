pub fn argmin<T: common_traits::FiniteRangeNumber>(vec: &[T]) -> isize {
    let mut min = T::MAX;
    let mut argmin = -1;
    for i in 0..vec.len() {
        if vec[i] < min {
            argmin = i.try_into().unwrap();
            min = vec[i];
        }
    }
    argmin
}

pub fn filtered_argmin<T: common_traits::FiniteRangeNumber, N: common_traits::FiniteRangeNumber>(
    vec: &[T],
    tie_break: &[N],
    filter: &[bool],
) -> isize {
    assert_eq!(vec.len(), tie_break.len());
    assert_eq!(vec.len(), filter.len());

    let mut min = T::MAX;
    let mut min_tie_break = N::MAX;
    let mut argmin = -1;

    for i in 0..vec.len() {
        if filter[i] && (vec[i] < min || (vec[i] == min && tie_break[i] < min_tie_break)) {
            argmin = i.try_into().unwrap();
            min = vec[i];
            min_tie_break = tie_break[i];
        }
    }

    argmin
}
