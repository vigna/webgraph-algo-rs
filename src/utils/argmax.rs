use std::ops::Index;

pub fn argmax<T: common_traits::FiniteRangeNumber, A: Index<usize, Output = T>>(vec: &A) -> isize
where
    for<'a> &'a A: IntoIterator,
{
    let mut max = T::MIN;
    let mut argmax = -1;
    let mut i = 0;
    for _ in vec {
        if vec[i] > max {
            argmax = i.try_into().unwrap();
            max = vec[i];
        }
        i += 1;
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
) -> isize
where
    for<'a> &'a A: IntoIterator,
{
    let mut max = T::MIN;
    let mut max_tie_break = N::MIN;
    let mut argmax = -1;
    let mut i = 0;

    for _ in vec {
        if filter[i] && (vec[i] > max || (vec[i] == max && tie_break[i] > max_tie_break)) {
            argmax = i.try_into().unwrap();
            max = vec[i];
            max_tie_break = tie_break[i];
        }
        i += 1;
    }

    argmax
}
