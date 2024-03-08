pub fn dummy() {
    println!("Dummy!")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        dummy();
    }
}
