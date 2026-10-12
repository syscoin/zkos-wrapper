use bellman::{
    rand::{CryptoRng, RngCore, rngs::OsRng},
    rand_crate::Error,
};

const OS_ENTROPY_BUFFER_BYTES: usize = 64 * 1024;

/// Amortizes operating-system entropy calls while preserving the underlying byte
/// sequence and distribution.
///
/// A refill is published only after `try_fill_bytes` succeeds. On failure `position`
/// remains exhausted, so no partially overwritten or stale refill can be consumed and
/// the next request retries a complete fresh refill.
///
/// This private RNG is constructed for one synchronous padding finalization and must
/// not be retained or reused across a process fork.
pub(crate) struct BufferedOsRng<R = OsRng> {
    inner: R,
    bytes: Box<[u8]>,
    position: usize,
}

impl BufferedOsRng<OsRng> {
    pub(crate) fn new() -> Self {
        Self::from_rng(OsRng)
    }
}

impl<R: RngCore> BufferedOsRng<R> {
    fn from_rng(inner: R) -> Self {
        Self {
            inner,
            bytes: vec![0; OS_ENTROPY_BUFFER_BYTES].into_boxed_slice(),
            position: OS_ENTROPY_BUFFER_BYTES,
        }
    }

    fn refill(&mut self) -> Result<(), Error> {
        debug_assert_eq!(self.bytes.len(), OS_ENTROPY_BUFFER_BYTES);
        debug_assert_eq!(self.position, OS_ENTROPY_BUFFER_BYTES);
        self.inner.try_fill_bytes(&mut self.bytes)?;
        self.position = 0;
        Ok(())
    }
}

impl<R: RngCore> RngCore for BufferedOsRng<R> {
    fn next_u32(&mut self) -> u32 {
        let mut bytes = [0; 4];
        self.fill_bytes(&mut bytes);
        u32::from_le_bytes(bytes)
    }

    fn next_u64(&mut self) -> u64 {
        let mut bytes = [0; 8];
        self.fill_bytes(&mut bytes);
        u64::from_le_bytes(bytes)
    }

    fn fill_bytes(&mut self, destination: &mut [u8]) {
        self.try_fill_bytes(destination)
            .expect("operating-system entropy unavailable for zero-knowledge padding");
    }

    fn try_fill_bytes(&mut self, mut destination: &mut [u8]) -> Result<(), Error> {
        while !destination.is_empty() {
            if self.position == OS_ENTROPY_BUFFER_BYTES {
                self.refill()?;
            }
            let count = destination
                .len()
                .min(OS_ENTROPY_BUFFER_BYTES - self.position);
            destination[..count].copy_from_slice(&self.bytes[self.position..self.position + count]);
            self.position += count;
            destination = &mut destination[count..];
        }
        Ok(())
    }
}

impl<R: RngCore + CryptoRng> CryptoRng for BufferedOsRng<R> {}

#[cfg(test)]
mod tests {
    use super::*;
    use bellman::{pairing::bn256::Fr, rand::Rand};
    use std::num::NonZeroU32;

    #[derive(Default)]
    struct StreamRng {
        position: usize,
        calls: usize,
        fail_next: bool,
    }

    impl RngCore for StreamRng {
        fn next_u32(&mut self) -> u32 {
            let mut bytes = [0; 4];
            self.fill_bytes(&mut bytes);
            u32::from_le_bytes(bytes)
        }

        fn next_u64(&mut self) -> u64 {
            let mut bytes = [0; 8];
            self.fill_bytes(&mut bytes);
            u64::from_le_bytes(bytes)
        }

        fn fill_bytes(&mut self, destination: &mut [u8]) {
            self.try_fill_bytes(destination).unwrap();
        }

        fn try_fill_bytes(&mut self, destination: &mut [u8]) -> Result<(), Error> {
            self.calls += 1;
            if self.fail_next {
                self.fail_next = false;
                destination.fill(0xff);
                return Err(Error::from(NonZeroU32::new(Error::CUSTOM_START).unwrap()));
            }
            for byte in destination {
                *byte = (self.position % 251) as u8;
                self.position += 1;
            }
            Ok(())
        }
    }

    impl CryptoRng for StreamRng {}

    #[test]
    fn mixed_stream_matches_across_refill_boundaries() {
        let mut direct = StreamRng::default();
        let mut buffered = BufferedOsRng::from_rng(StreamRng::default());
        for count in [0, 1, OS_ENTROPY_BUFFER_BYTES - 20, 7, 19, 8, 3] {
            assert_eq!(direct.next_u32(), buffered.next_u32());
            assert_eq!(direct.next_u64(), buffered.next_u64());
            let mut expected = vec![0; count];
            let mut actual = vec![0; count];
            direct.fill_bytes(&mut expected);
            buffered.fill_bytes(&mut actual);
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn field_element_stream_matches_across_many_refills() {
        let mut direct = StreamRng::default();
        let mut buffered = BufferedOsRng::from_rng(StreamRng::default());
        for _ in 0..10_000 {
            assert_eq!(Fr::rand(&mut direct), Fr::rand(&mut buffered));
        }
    }

    #[test]
    fn refills_are_full_sized_and_fresh() {
        let mut buffered = BufferedOsRng::from_rng(StreamRng::default());
        let mut first = vec![0; OS_ENTROPY_BUFFER_BYTES];
        buffered.fill_bytes(&mut first);
        assert_eq!(buffered.inner.calls, 1);
        assert_eq!(buffered.inner.position, OS_ENTROPY_BUFFER_BYTES);
        let mut next = [0; 1];
        buffered.fill_bytes(&mut next);
        assert_eq!(buffered.inner.calls, 2);
        assert_eq!(buffered.inner.position, 2 * OS_ENTROPY_BUFFER_BYTES);
        assert_eq!(next[0], (OS_ENTROPY_BUFFER_BYTES % 251) as u8);
    }

    #[test]
    fn failed_refill_is_not_consumed_and_is_retried() {
        let mut buffered = BufferedOsRng::from_rng(StreamRng {
            fail_next: true,
            ..StreamRng::default()
        });
        let mut output = [0x11; 8];
        assert!(buffered.try_fill_bytes(&mut output).is_err());
        assert_eq!(output, [0x11; 8]);
        assert_eq!(buffered.position, OS_ENTROPY_BUFFER_BYTES);
        assert_eq!(buffered.inner.calls, 1);

        buffered.try_fill_bytes(&mut output).unwrap();
        assert_eq!(output, [0, 1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(buffered.inner.calls, 2);
    }

    #[test]
    fn crypto_rng_marker_is_preserved_conditionally() {
        fn require_crypto_rng<T: CryptoRng>() {}
        require_crypto_rng::<BufferedOsRng<StreamRng>>();
        require_crypto_rng::<BufferedOsRng<OsRng>>();
    }
}
