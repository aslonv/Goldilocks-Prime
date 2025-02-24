// Without testing for smaller numbers
// use crate::dft::DFT;
// use std::vec::Vec;

// /// Goldilocks prime: 2^64 - 2^32 + 1
// const P: u64 = 0xffffffff00000001;

// const PSI: u64 = 0xabd0a6e8aa3d8a0e;

// /// Reduces a 128-bit number modulo the Goldilocks prime
// fn reduce(x: u128) -> u64 {
//     let x_lo = x as u64;
//     let x_hi = (x >> 64) as u64;
//     let t = x_lo as u128 + ((x_hi as u128) * (0xffffffffu64 as u128));
//     let t_lo = t as u64;
//     let t_hi = (t >> 64) as u64;
//     let mut result = t_lo.wrapping_add(t_hi.wrapping_mul(0xffffffff));
//     if result >= P { result = result.wrapping_sub(P); }
//     if result >= P { result = result.wrapping_sub(P); }
//     result
// }

// fn mul_mod(a: u64, b: u64) -> u64 {
//     reduce((a as u128) * (b as u128))
// }   

// fn add_mod(a: u64, b: u64) -> u64 {
//     let sum = a.wrapping_add(b);
//     if sum >= P { sum.wrapping_sub(P) } else { sum }
// }

// fn sub_mod(a: u64, b: u64) -> u64 {
//     if a >= b { a.wrapping_sub(b) } else { a.wrapping_add(P).wrapping_sub(b) }
// }

// /// Computes a^b mod P using square-and-multiply
// fn pow_mod(a: u64, b: u64) -> u64 {
//     let mut result = 1;
//     let mut base = a;
//     let mut exp = b;
//     while exp > 0 {
//         if exp & 1 == 1 {
//             result = mul_mod(result, base);
//         }
//         base = mul_mod(base, base);
//         exp >>= 1;
//     }
//     result
// }

// pub struct GoldilocksTable {
//     twiddle_factors: Vec<Vec<u64>>,     
//     inv_twiddle_factors: Vec<Vec<u64>>, 
//     inv_n: Vec<u64>,                    
// }

// impl GoldilocksTable {
//     /// table for n = 2^11 to 2^16
//     pub fn new() -> Self {
//         let mut twiddle_factors = Vec::new();
//         let mut inv_twiddle_factors = Vec::new();
//         let mut inv_n = Vec::new();
//         for log_n in 11..=16 {
//             let n = 1 << log_n;
//             let k = 17 - (log_n + 1);
//             // ψ_n = ψ^(2^(17 - (log_n + 1))) for 2n-th root
//             let psi_n = pow_mod(PSI, 1 << k);
//             let psi_inv = pow_mod(psi_n, P - 2); // Inverse of ψ_n
//             let n_inv = pow_mod(n as u64, P - 2); // n^-1 mod P

//             // Precomputes
//             let mut twiddles = Vec::with_capacity(n);
//             let mut current = 1;
//             for i in 0..n {
//                 twiddles.push(current);
//                 current = mul_mod(current, psi_n);
//             }
//             
//             let mut twiddles_br = vec![0; n];
//             for i in 0..n {
//                 twiddles_br[Self::bit_reverse(i as u32, log_n as u32) as usize] = twiddles[i];
//             }

//             // Precomputes
//             let mut inv_twiddles = Vec::with_capacity(n);
//             current = 1;
//             for i in 0..n {
//                 inv_twiddles.push(current);
//                 current = mul_mod(current, psi_inv);
//             }
//             let mut inv_twiddles_br = vec![0; n];
//             for i in 0..n {
//                 inv_twiddles_br[Self::bit_reverse(i as u32, log_n as u32) as usize] = inv_twiddles[i];
//             }

//             twiddle_factors.push(twiddles_br);
//             inv_twiddle_factors.push(inv_twiddles_br);
//             inv_n.push(n_inv);
//         }
//         GoldilocksTable {
//             twiddle_factors,
//             inv_twiddle_factors,
//             inv_n,
//         }
//     }
//     fn bit_reverse(mut num: u32, bits: u32) -> u32 {
//         num = (num >> 1) & 0x55555555 | (num & 0x55555555) << 1;
//         num = (num >> 2) & 0x33333333 | (num & 0x33333333) << 2;
//         num = (num >> 4) & 0x0f0f0f0f | (num & 0x0f0f0f0f) << 4;
//         num = (num >> 8) & 0x00ff00ff | (num & 0x00ff00ff) << 8;
//         num = (num >> 16) | (num << 16);
//         num >> (32 - bits)
//     }
// }

// impl DFT<u64> for GoldilocksTable {
//     fn forward_inplace(&self, x: &mut [u64]) {
//         let n = x.len();
//         let log_n = n.trailing_zeros() as usize;
//         assert!(log_n >= 11 && log_n <= 16, "n must be between 2^11 and 2^16");
//         let idx = log_n - 11;
//         let twiddles = &self.twiddle_factors[idx];

//         let mut t = n;
//         let mut m = 1;
//         while m < n {
//             t >>= 1;
//             for i in 0..m {
//                 let j1 = 2 * i * t;
//                 let s = twiddles[m + i];
//                 for j in j1..(j1 + t) {
//                     let u = x[j];
//                     let v = mul_mod(x[j + t], s);
//                     x[j] = add_mod(u, v);
//                     x[j + t] = sub_mod(u, v);
//                 }
//             }
//             m <<= 1;
//         }
//     }
//     fn backward_inplace(&self, x: &mut [u64]) {
//         let n = x.len();
//         let log_n = n.trailing_zeros() as usize;
//         assert!(log_n >= 11 && log_n <= 16, "n must be between 2^11 and 2^16");
//         let idx = log_n - 11;
//         let twiddles = &self.inv_twiddle_factors[idx];
//         let n_inv = self.inv_n[idx];

//         let mut t = 1;
//         let mut m = n;
//         while m > 1 {
//             let h = m >> 1;
//             let mut j1 = 0;
//             for i in 0..h {
//                 let j2 = j1 + t - 1;
//                 let s = twiddles[h + i];
//                 for j in j1..=j2 {
//                     let u = x[j];
//                     let v = x[j + t];
//                     x[j] = add_mod(u, v);
//                     x[j + t] = mul_mod(sub_mod(u, v), s);
//                 }
//                 j1 += 2 * t;
//             }
//             t <<= 1;
//             m >>= 1;
//         }
//         for i in 0..n {
//             x[i] = mul_mod(x[i], n_inv);
//         }
//     }

//     fn forward_inplace_lazy(&self, _x: &mut [u64]) {
//         unimplemented!("Lazy forward NTT not implemented");
//     }

//     fn backward_inplace_lazy(&self, _x: &mut [u64]) {
//         unimplemented!("Lazy backward NTT not implemented");
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use rand::Rng;

//     #[test]
//     fn test_modular_arithmetic() {
//         let p = 0xffffffff00000001;
//         assert_eq!(mul_mod(p - 1, 2), p - 2);
//         assert_eq!(add_mod(p - 1, 1), 0);
//         assert_eq!(sub_mod(0, 1), p - 1);
//     }

//     #[test]
//     fn test_ntt_correctness() {
//         let table = GoldilocksTable::new();
//         let n: usize = 1 << 11;
//         let mut a: Vec<u64> = (0..n).map(|i| (i as u64) % P).collect();
//         let b = a.clone();
//         table.forward_inplace(&mut a);
//         table.backward_inplace(&mut a);
//         for i in 0..n {
//             assert_eq!(a[i], b[i], "NTT round-trip failed at index {}", i);
//         }
//     }
// }


// For testing

use crate::dft::DFT;
use std::vec::Vec;

const P: u64 = 0xffffffff00000001;
const PSI: u64 = 0xabd0a6e8aa3d8a0e;

fn reduce(x: u128) -> u64 {
    let x_lo = x as u64;
    let x_hi = (x >> 64) as u64;
    let t = x_lo as u128 + ((x_hi as u128) * (0xffffffffu64 as u128));
    let t_lo = t as u64;
    let t_hi = (t >> 64) as u64;
    let mut result = t_lo.wrapping_add(t_hi.wrapping_mul(0xffffffff));
    if result >= P { result = result.wrapping_sub(P); }
    if result >= P { result = result.wrapping_sub(P); }
    result
}

fn mul_mod(a: u64, b: u64) -> u64 { reduce((a as u128) * (b as u128)) }
fn add_mod(a: u64, b: u64) -> u64 { if a >= P - b { a.wrapping_sub(P - b) } else { a + b } }
fn sub_mod(a: u64, b: u64) -> u64 { if a >= b { a - b } else { a.wrapping_add(P - b) } }
fn pow_mod(a: u64, b: u64) -> u64 {
    let mut result = 1;
    let mut base = a;
    let mut exp = b;
    while exp > 0 {
        if exp & 1 == 1 { result = mul_mod(result, base); }
        base = mul_mod(base, base);
        exp >>= 1;
    }
    result
}

pub struct GoldilocksTable {
    twiddle_factors: Vec<Vec<u64>>,
    inv_twiddle_factors: Vec<Vec<u64>>,
    inv_n: Vec<u64>,
    psi_powers: Vec<Vec<u64>>,
    inv_psi_powers: Vec<Vec<u64>>,
}

impl GoldilocksTable {
    pub fn new() -> Self {
        let mut twiddle_factors = Vec::new();
        let mut inv_twiddle_factors = Vec::new();
        let mut inv_n = Vec::new();
        let mut psi_powers = Vec::new();
        let mut inv_psi_powers = Vec::new();
        for log_n in 2..=16 {
            let n = 1 << log_n;
            let k = 17 - (log_n + 1);
            let psi_n = pow_mod(PSI, 1 << k);
            let psi_inv = pow_mod(psi_n, P - 2);
            let n_inv = pow_mod(n as u64, P - 2);

            let omega_n = mul_mod(psi_n, psi_n);
            let omega_inv = pow_mod(omega_n, P - 2);

            let mut twiddles = Vec::with_capacity(n);
            let mut current = 1;
            for _ in 0..n {
                twiddles.push(current);
                current = mul_mod(current, omega_n);
            }
            let mut twiddles_br = vec![0; n];
            for i in 0..n {
                twiddles_br[Self::bit_reverse(i as u32, log_n as u32) as usize] = twiddles[i];
            }

            let mut inv_twiddles = Vec::with_capacity(n);
            current = 1;
            for _ in 0..n {
                inv_twiddles.push(current);
                current = mul_mod(current, omega_inv);
            }
            let mut inv_twiddles_br = vec![0; n];
            for i in 0..n {
                inv_twiddles_br[Self::bit_reverse(i as u32, log_n as u32) as usize] = inv_twiddles[i];
            }

            let mut psi_pow = Vec::with_capacity(n);
            let mut inv_psi_pow = Vec::with_capacity(n);
            current = 1;
            let mut current_inv = 1;
            for _ in 0..n {
                psi_pow.push(current);
                inv_psi_pow.push(current_inv);
                current = mul_mod(current, psi_n);
                current_inv = mul_mod(current_inv, psi_inv);
            }

            twiddle_factors.push(twiddles_br);
            inv_twiddle_factors.push(inv_twiddles_br);
            inv_n.push(n_inv);
            psi_powers.push(psi_pow);
            inv_psi_powers.push(inv_psi_pow);
        }
        GoldilocksTable {
            twiddle_factors,
            inv_twiddle_factors,
            inv_n,
            psi_powers,
            inv_psi_powers,
        }
    }

    fn bit_reverse(mut num: u32, bits: u32) -> u32 {
        num = (num >> 1) & 0x55555555 | (num & 0x55555555) << 1;
        num = (num >> 2) & 0x33333333 | (num & 0x33333333) << 2;
        num = (num >> 4) & 0x0f0f0f0f | (num & 0x0f0f0f0f) << 4;
        num = (num >> 8) & 0x00ff00ff | (num & 0x00ff00ff) << 8;
        num = (num >> 16) | (num << 16);
        num >> (32 - bits)
    }
}

impl DFT<u64> for GoldilocksTable {
    fn forward_inplace(&self, x: &mut [u64]) {
        let n = x.len();
        let log_n = n.trailing_zeros() as usize;
        assert!(log_n >= 2 && log_n <= 16, "n must be between 2^2 and 2^16 for testing");
        let idx = log_n - 2;
        let twiddles = &self.twiddle_factors[idx];
        let psi_pow = &self.psi_powers[idx];

        for j in 0..n {
            x[j] = mul_mod(x[j], psi_pow[j]);
        }

        let mut t = n;
        let mut m = 1;
        while m < n {
            t >>= 1;
            for i in 0..m {
                let j1 = 2 * i * t;
                let s = twiddles[m + i];
                for j in j1..(j1 + t) {
                    let u = x[j];
                    let v = mul_mod(x[j + t], s);
                    x[j] = add_mod(u, v);
                    x[j + t] = sub_mod(u, v);
                }
            }
            m <<= 1;
        }
    }

    fn backward_inplace(&self, x: &mut [u64]) {
        let n = x.len();
        let log_n = n.trailing_zeros() as usize;
        assert!(log_n >= 2 && log_n <= 16, "n must be between 2^2 and 2^16 for testing");
        let idx = log_n - 2;
        let twiddles = &self.inv_twiddle_factors[idx]; // Fixed: Use inverse twiddles
        let n_inv = self.inv_n[idx];
        let inv_psi_pow = &self.inv_psi_powers[idx];

        let mut t = 1;
        let mut m = n;
        while m > 1 {
            let h = m >> 1;
            let mut j1 = 0;
            for i in 0..h {
                let j2 = j1 + t - 1;
                let s = twiddles[h + i];
                for j in j1..=j2 {
                    let u = x[j];
                    let v = x[j + t];
                    x[j] = add_mod(u, v);
                    x[j + t] = mul_mod(sub_mod(u, v), s);
                }
                j1 += 2 * t;
            }
            t <<= 1;
            m >>= 1;
        }

        for i in 0..n {
            x[i] = mul_mod(x[i], mul_mod(n_inv, inv_psi_pow[i]));
        }
    }

    fn forward_inplace_lazy(&self, _x: &mut [u64]) { unimplemented!("Lazy forward NTT not implemented"); }
    fn backward_inplace_lazy(&self, _x: &mut [u64]) { unimplemented!("Lazy backward NTT not implemented"); }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn test_modular_arithmetic() {
        let p = 0xffffffff00000001;
        assert_eq!(mul_mod(p - 1, 2), p - 2);
        assert_eq!(add_mod(p - 1, 1), 0);
        assert_eq!(sub_mod(0, 1), p - 1);
    }

    #[test]
    fn test_small_ntt() {
        let table = GoldilocksTable::new();
        let n: usize = 4;
        let mut a: Vec<u64> = (0..n).map(|i| i as u64).collect();
        let b = a.clone();
        println!("Input: {:?}", a);
        table.forward_inplace(&mut a);
        println!("After forward: {:?}", a);
        table.backward_inplace(&mut a);
        println!("After backward: {:?}", a);
        assert_eq!(a, b);
    }

    #[test]
    fn test_ntt_correctness() {
        let table = GoldilocksTable::new();
        let n: usize = 1 << 11;
        let mut a: Vec<u64> = (0..n).map(|i| (i as u64) % P).collect();
        let b = a.clone();
        table.forward_inplace(&mut a);
        table.backward_inplace(&mut a);
        for i in 0..n {
            assert_eq!(a[i], b[i], "NTT round-trip failed at index {}", i);
        }
    }
}