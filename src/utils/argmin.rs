use std::ops::Index;

pub fn argmin<T: common_traits::FiniteRangeNumber, A: Index<usize, Output = T>>(
    vec: &A,
) -> Option<usize>
where
    for<'a> &'a A: IntoIterator,
{
    let mut min = T::MAX;
    let mut argmin = None;
    for (i, _) in vec.into_iter().enumerate() {
        if vec[i] < min {
            argmin = Some(i);
            min = vec[i];
        }
    }
    argmin
}

pub fn filtered_argmin<
    T: common_traits::FiniteRangeNumber,
    N: common_traits::FiniteRangeNumber,
    A: Index<usize, Output = T>,
    V: Index<usize, Output = N>,
    F: Fn(usize) -> bool,
>(
    vec: &A,
    tie_break: &V,
    filter: F,
) -> Option<usize>
where
    for<'a> &'a A: IntoIterator,
{
    let mut min = T::MAX;
    let mut min_tie_break = N::MAX;
    let mut argmin = None;

    for (i, _) in vec.into_iter().enumerate() {
        if filter(i) && (vec[i] < min || (vec[i] == min && tie_break[i] < min_tie_break)) {
            argmin = Some(i);
            min = vec[i];
            min_tie_break = tie_break[i];
        }
    }

    argmin
}
