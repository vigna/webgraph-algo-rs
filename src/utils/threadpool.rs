#[derive(Debug, Clone, Copy)]
pub enum Threads {
    Default,
    NumThreads(usize),
}

impl Threads {
    pub fn build(self) -> rayon::ThreadPool {
        match self {
            Self::Default => rayon::ThreadPoolBuilder::new()
                .build()
                .expect("Should be able to build default threadpool"),
            Self::NumThreads(num_threads) => rayon::ThreadPoolBuilder::new()
                .num_threads(num_threads)
                .build()
                .unwrap_or_else(|_| {
                    panic!(
                        "Should be able to build custom threadpool with {} threads",
                        num_threads
                    )
                }),
        }
    }
}
