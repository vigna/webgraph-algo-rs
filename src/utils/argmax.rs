use std::ops::Index;

pub fn argmax<T: common_traits::FiniteRangeNumber, A: Index<usize, Output = T>>(
    vec: &A,
) -> Option<usize>
where
    for<'a> &'a A: IntoIterator,
{
    let mut max = T::MIN;
    let mut argmax = None;
    for (i, _) in vec.into_iter().enumerate() {
        if vec[i] > max {
            argmax = Some(i);
            max = vec[i];
        }
    }
    argmax
}

pub fn filtered_argmax<
    T: common_traits::FiniteRangeNumber,
    N: common_traits::FiniteRangeNumber,
    A: Index<usize, Output = T>,
    V: Index<usize, Output = N>,
    F: Index<usize, Output = bool>,
>(
    vec: &A,
    tie_break: &V,
    filter: &F,
) -> Option<usize>
where
    for<'a> &'a A: IntoIterator,
{
    let mut max = T::MIN;
    let mut max_tie_break = N::MIN;
    let mut argmax = None;

    for (i, _) in vec.into_iter().enumerate() {
        if filter[i] && (vec[i] > max || (vec[i] == max && tie_break[i] > max_tie_break)) {
            argmax = Some(i);
            max = vec[i];
            max_tie_break = tie_break[i];
        }
    }

    argmax
}
