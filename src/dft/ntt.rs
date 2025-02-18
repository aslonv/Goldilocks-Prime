use crate::dft::DFT;

fn pow_mod(a: u64, exp: u64, modulus: u64) -> u64 {
    let mut result = 1u128;
    let mut a = a as u128 % modulus as u128;
    let mut exp = exp;
    let modulus = modulus as u128;
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * a) % modulus;
        }
        a = (a * a) % modulus;
        exp >>= 1;
    }
    result as u64
}

#[inline(always)]
fn add_mod<const LAZY: bool>(a: u64, b: u64, modulus: u64) -> u64 {
    if LAZY {
        a + b
    } else {
        ((a as u128 + b as u128) % modulus as u128) as u64
    }
}

#[inline(always)]
fn sub_mod<const LAZY: bool>(a: u64, b: u64, modulus: u64) -> u64 {
    if LAZY {
        a.wrapping_sub(b)
    } else {
        let a = a as u128;
        let b = b as u128;
        let modulus = modulus as u128;
        ((a + modulus - b) % modulus) as u64
    }
}

#[inline(always)]
fn mul_mod(a: u64, b: u64, modulus: u64) -> u64 {
    ((a as u128 * b as u128) % modulus as u128) as u64
}

pub struct Table<O> {
    q: O,
    forward_twiddles: Vec<Vec<O>>,
    inverse_twiddles: Vec<Vec<O>>,
    inv_n_table: Vec<O>,
}

impl Table<u64> {
    pub fn new() -> Self {
        const Q: u64 = 0x1fffffffffe00001;
        const PSI: u64 = 0x15eb043c7aa2b01f;  // 2^17-th root of unity
        
        let max_log_n = 17;
        let mut forward_twiddles = Vec::with_capacity(max_log_n);
        let mut inverse_twiddles = Vec::with_capacity(max_log_n);

        for s in 1..=max_log_n {
            let m = 1 << s;
            let m_half = m >> 1;
            let exponent = (1 << (max_log_n - s)) as u64;
            
            let w_m = pow_mod(PSI, exponent, Q);
            let inv_w_m = pow_mod(w_m, Q - 2, Q);

            let mut fw_twiddles = Vec::with_capacity(m_half);
            let mut inv_twiddles = Vec::with_capacity(m_half);
            
            let mut current_fw = 1u64;
            let mut current_inv = 1u64;
            
            fw_twiddles.push(current_fw);
            inv_twiddles.push(current_inv);
            
            for _ in 1..m_half {
                current_fw = mul_mod(current_fw, w_m, Q);
                current_inv = mul_mod(current_inv, inv_w_m, Q);
                fw_twiddles.push(current_fw);
                inv_twiddles.push(current_inv);
            }
            
            forward_twiddles.push(fw_twiddles);
            inverse_twiddles.push(inv_twiddles);
        }

        let mut inv_n_table = Vec::with_capacity(max_log_n + 1);
        for k in 0..=max_log_n {
            let n = (1u64 << k) as u64;
            inv_n_table.push(pow_mod(n, Q - 2, Q));
        }

        Self {
            q: Q,
            forward_twiddles,
            inverse_twiddles,
            inv_n_table,
        }
    }

    pub fn get_q(&self) -> u64 {
        self.q
    }

    fn bit_reverse(a: &mut [u64]) {
        let n = a.len();
        let mut j = 0;
        for i in 1..n {
            let mut bit = n >> 1;
            while j >= bit {
                j -= bit;
                bit >>= 1;
            }
            j += bit;
            if i < j {
                a.swap(i, j);
            }
        }
    }

    pub fn forward_inplace_core<const LAZY: bool>(&self, a: &mut [u64]) {
        let q = self.q;
        let n = a.len();
        let log_n = n.trailing_zeros() as usize;

        Self::bit_reverse(a);

        for s in 1..=log_n {
            let m = 1 << s;
            let m_half = m >> 1;
            let twiddles = &self.forward_twiddles[s - 1];

            for k in (0..n).step_by(m) {
                for j in 0..m_half {
                    let idx1 = k + j;
                    let idx2 = k + j + m_half;
                    let t = mul_mod(twiddles[j], a[idx2], q);
                    let a1 = a[idx1];
                    a[idx2] = sub_mod::<LAZY>(a1, t, q);
                    a[idx1] = add_mod::<LAZY>(a1, t, q);
                }
            }
        }
    }

    pub fn backward_inplace_core<const LAZY: bool>(&self, a: &mut [u64]) {
        let q = self.q;
        let n = a.len();
        let log_n = n.trailing_zeros() as usize;

        Self::bit_reverse(a);

        for s in 1..=log_n {
            let m = 1 << s;
            let m_half = m >> 1;
            let twiddles = &self.inverse_twiddles[s - 1];

            for k in (0..n).step_by(m) {
                for j in 0..m_half {
                    let idx1 = k + j;
                    let idx2 = k + j + m_half;
                    let t = mul_mod(twiddles[j], a[idx2], q);
                    let a1 = a[idx1];
                    a[idx2] = sub_mod::<LAZY>(a1, t, q);
                    a[idx1] = add_mod::<LAZY>(a1, t, q);
                }
            }
        }

        let inv_n = self.inv_n_table[log_n];
        for elem in a.iter_mut() {
            *elem = mul_mod(*elem, inv_n, q);
        }
    }
}

impl DFT<u64> for Table<u64> {
    fn forward_inplace(&self, a: &mut [u64]) {
        self.forward_inplace_core::<false>(a)
    }

    fn forward_inplace_lazy(&self, a: &mut [u64]) {
        self.forward_inplace_core::<true>(a)
    }

    fn backward_inplace(&self, a: &mut [u64]) {
        self.backward_inplace_core::<false>(a)
    }

    fn backward_inplace_lazy(&self, a: &mut [u64]) {
        self.backward_inplace_core::<true>(a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ntt_roundtrip() {
        let ntt_table = Table::<u64>::new();
        let q = ntt_table.q;

        let mut a = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let original = a.clone();

        ntt_table.forward_inplace(&mut a);
        ntt_table.backward_inplace(&mut a);

        for (i, &val) in a.iter().enumerate() {
            assert_eq!(val, original[i] % q);
        }
    }

    #[test]
    fn test_ntt_correctness() {
        let ntt_table = Table::<u64>::new();
        let q = ntt_table.q;

        // Test 2-point NTT
        let mut a = vec![1, 0];
        ntt_table.forward_inplace(&mut a);
        assert_eq!(a[0], 1);
        assert_eq!(a[1], 1);

        ntt_table.backward_inplace(&mut a);
        assert_eq!(a[0], 1);
        assert_eq!(a[1], 0);

        // Test 2-point NTT with non-zero inputs
        let mut a = vec![1, 1];
        ntt_table.forward_inplace(&mut a);
        assert_eq!(a[0], add_mod::<false>(1, 1, q));
        assert_eq!(a[1], sub_mod::<false>(1, 1, q));
    }

    #[test]
    fn test_large_ntt() {
        let ntt_table = Table::<u64>::new();
        let q = ntt_table.q;
        let n = 1 << 16;
        
        let mut a: Vec<u64> = (0..n).map(|x| x % q).collect();
        let original = a.clone();
        
        ntt_table.forward_inplace(&mut a);
        ntt_table.backward_inplace(&mut a);
        
        for (i, &val) in a.iter().enumerate() {
            assert_eq!(val, original[i], "Mismatch at index {}", i);
        }
    }
}