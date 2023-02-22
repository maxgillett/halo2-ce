use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use curves::bn256::Fr;
use ff::Field;
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

fn mul_bn256_fr(c: &mut Criterion) {
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);
    c.bench_function("mul_bn256_fr", |bench| {
        bench.iter_batched(
            || {
                let a = Fr::random(&mut rng);
                let b = Fr::random(&mut rng);
                (a, b)
            },
            |(a, b)| a * b,
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, mul_bn256_fr);
criterion_main!(benches);
