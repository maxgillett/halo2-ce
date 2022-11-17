use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use ff::Field;
use goldilocks::fp::Goldilocks;
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

use winter_math::fields::f64::BaseElement;
use winter_rand_utils::rand_value;

fn mul_winter(c: &mut Criterion) {
    c.bench_function("mul_winter", |bench| {
        bench.iter_batched(
            || {
                let a: BaseElement = rand_value();
                let b: BaseElement = rand_value();
                (a, b)
            },
            |(a, b)| a * b,
            BatchSize::SmallInput,
        )
    });
}

fn mul_arithmetic(c: &mut Criterion) {
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);
    c.bench_function("mul_arithmetic", |bench| {
        bench.iter_batched(
            || {
                let a = Goldilocks::random(&mut rng);
                let b = Goldilocks::random(&mut rng);
                (a, b)
            },
            |(a, b)| a * b,
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, mul_winter, mul_arithmetic);
criterion_main!(benches);
