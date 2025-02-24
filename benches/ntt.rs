use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use app::dft::ntt::GoldilocksTable;
use app::dft::DFT;

fn ntt_bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("NTT");

    // Goldilocks implementation
    let goldilocks_table = GoldilocksTable::new();
    for log_n in [11, 12, 13, 14, 15, 16] {
        let n = 1 << log_n;
        let mut a = vec![0u64; n];
        for i in 0..n {
            a[i] = i as u64 % 0xffffffff00000001;
        }
        group.bench_with_input(BenchmarkId::new("Goldilocks", n), &n, |b, _| {
            let mut a_copy = a.clone();
            b.iter(|| {
                goldilocks_table.forward_inplace(&mut a_copy);
                goldilocks_table.backward_inplace(&mut a_copy);
            })
        });
    }

    group.finish();
}

criterion_group!(benches, ntt_bench);
criterion_main!(benches);