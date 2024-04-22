use std::ops::Index;

pub fn argmin<T: common_traits::FiniteRangeNumber, A: Index<usize, Output = T>>(vec: &A) -> isize
where
    for<'a> &'a A: IntoIterator,
{
    let mut min = T::MAX;
    let mut argmin = -1;
    let mut i = 0;
    for _ in vec {
        if vec[i] < min {
            argmin = i.try_into().unwrap();
            min = vec[i];
        }
        i += 1;
    }
    argmin
}

pub fn filtered_argmin<
    T: common_traits::FiniteRangeNumber,
    N: common_traits::FiniteRangeNumber,
    A: Index<usize, Output = T>,
    V: Index<usize, Output = N>,
    F: Index<usize, Output = bool>,
>(
    vec: &A,
    tie_break: &V,
    filter: &F,
) -> isize
where
    for<'a> &'a A: IntoIterator,
{
    let mut min = T::MAX;
    let mut min_tie_break = N::MAX;
    let mut argmin = -1;
    let mut i = 0;

    for _ in vec {
        if filter[i] && (vec[i] < min || (vec[i] == min && tie_break[i] < min_tie_break)) {
            argmin = i.try_into().unwrap();
            min = vec[i];
            min_tie_break = tie_break[i];
        }
        i += 1;
    }

    argmin
}
