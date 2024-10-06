pub struct KahanSummation {
    /// The current value of the sum
    value: f64,
    /// The current correction
    c: f64,
}

impl KahanSummation {
    /// Creates a new Kahan summation instance
    pub fn new() -> Self {
        Self { value: 0.0, c: 0.0 }
    }

    /// Adds a value.
    ///
    /// # Arguments
    /// - `v`: the value to add to the sum.
    pub fn add(&mut self, v: f64) {
        let y = v - self.c;
        let t = self.value + y;
        self.c = (t - self.value) - y;
        self.value = t;
    }

    /// Returns the sum computed so far.
    pub fn value(&self) -> f64 {
        self.value
    }
}
