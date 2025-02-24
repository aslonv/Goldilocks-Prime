## NTT Algorithms

- Forward NTT: Uses a Cooley-Tukey butterfly taking input in natural order and outputting in bit-reversed order

- Backward NTT: Uses a Gentleman-Sande butterfly taking input in bit-reversed order and outputting in natural order, with scaling by n^-1 mod p

- Negacyclic Convolution: Incorporates twiddle factors (ψ^i) for X^n + 1 merged into the butterfly operations to avoid extra multiplications

- Precomputation: Twiddle factors and their inverses are precomputed for n from 2^11 to 2^16 using the provided 2^17-th root of unity 0xabd0a6e8aa3d8a0e


## Optimization

- Efficient Reduction: Reduces 128-bit products modulo p in a single pass

- In-Place Operations: Both forward and backward NTTs modify the input array directly

- No Bit-Reversal Step: The forward-backward pair avoids explicit bit-reversal
