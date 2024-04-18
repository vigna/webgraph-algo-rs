pub fn argmax<T: common_traits::FiniteRangeNumber>(vec: &[T]) -> isize {
    let mut max = T::MAX;
    let mut arg_max = -1;
    for i in 0..vec.len() {
        if vec[i] > max {
            arg_max = i.try_into().unwrap();
            max = vec[i];
        }
    }
    arg_max
}
