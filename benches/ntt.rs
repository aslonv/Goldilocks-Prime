use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use app::dft::ntt::Table;
use app::dft::DFT;

fn ntt_bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("NTT");

    // Base 61-bit implementation
    let ntt_table = Table::new();
    for log_n in [11, 12, 13, 14, 15, 16] {
        let n = 1 << log_n;
        let mut a = vec![0u64; n];
        for i in 0..n {
            a[i] = i as u64 % ntt_table.get_q();
        }

        group.bench_with_input(BenchmarkId::new("Base", n), &n, |b, _| {
            b.iter(|| {
                ntt_table.forward_inplace(&mut a);
                ntt_table.backward_inplace(&mut a);
            })
        });
    }

    group.finish();
}

criterion_group!(benches, ntt_bench);
criterion_main!(benches);
