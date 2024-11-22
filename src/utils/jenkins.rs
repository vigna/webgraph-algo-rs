use common_traits::AsBytes;
use std::hash::*;

/// Jenkins Hasher as implemented in the
/// [Java version](https://github.com/vigna/dsiutils/blob/master/src/it/unimi/dsi/util/HyperLogLogCounterArray.java#L263).
#[derive(Debug, Clone)]
pub struct JenkinsHasher {
    a: u64,
    b: u64,
    c: u64,
    buffer: Vec<u8>,
}

impl JenkinsHasher {
    fn new(seed: u64) -> Self {
        Self {
            a: seed,
            b: seed,
            c: 0x9e3779b97f4a7c13,
            buffer: Vec::with_capacity(u64::BYTES),
        }
    }

    fn digest(&mut self) {
        while self.buffer.len() >= u64::BYTES {
            let bytes = &self.buffer[0..u64::BYTES];
            let word = u64::from_ne_bytes(bytes.try_into().unwrap());
            self.digest_word(word);
            self.buffer.drain(0..u64::BYTES);
        }
    }

    fn digest_word(&mut self, x: u64) {
        // Allow wrapping arithmetics
        let mut a = std::num::Wrapping(self.a);
        let mut b = std::num::Wrapping(self.b);
        let mut c = std::num::Wrapping(self.c);

        // Init state

        a += x;

        // a -= b; a -= c; a ^= (c >>> 43);

        a -= b;
        a -= c;
        a ^= c >> 43;

        // b -= c; b -= a; b ^= (a << 9);

        b -= c;
        b -= a;
        b ^= a << 9;

        // c -= a; c -= b; c ^= (b >>> 8);

        c -= a;
        c -= b;
        c ^= b >> 8;

        // a -= b; a -= c; a ^= (c >>> 38);

        a -= b;
        a -= c;
        a ^= c >> 38;

        // b -= c; b -= a; b ^= (a << 23);

        b -= c;
        b -= a;
        b ^= a << 23;

        // c -= a; c -= b; c ^= (b >>> 5);

        c -= a;
        c -= b;
        c ^= b >> 5;

        // a -= b; a -= c; a ^= (c >>> 35);

        a -= b;
        a -= c;
        a ^= c >> 35;

        // b -= c; b -= a; b ^= (a << 49);

        b -= c;
        b -= a;
        b ^= a << 49;

        // c -= a; c -= b; c ^= (b >>> 11);

        c -= a;
        c -= b;
        c ^= b >> 11;

        // a -= b; a -= c; a ^= (c >>> 12);

        a -= b;
        a -= c;
        a ^= c >> 12;

        // b -= c; b -= a; b ^= (a << 18);

        b -= c;
        b -= a;
        b ^= a << 18;

        // c -= a; c -= b; c ^= (b >>> 22);

        c -= a;
        c -= b;
        c ^= b >> 22;

        // Save modified state

        self.a = a.0;
        self.b = b.0;
        self.c = c.0;
    }
}

impl Hasher for JenkinsHasher {
    fn finish(&self) -> u64 {
        self.c
    }

    fn write(&mut self, bytes: &[u8]) {
        self.buffer.extend_from_slice(bytes);
        if self.buffer.len() >= u64::BYTES {
            self.digest();
        }
    }
}

#[derive(Clone, Debug)]
pub struct JenkinsHasherBuilder {
    seed: u64,
}

impl JenkinsHasherBuilder {
    pub fn new(seed: u64) -> Self {
        Self { seed }
    }
}

impl BuildHasher for JenkinsHasherBuilder {
    type Hasher = JenkinsHasher;

    fn build_hasher(&self) -> Self::Hasher {
        JenkinsHasher::new(self.seed)
    }
}
