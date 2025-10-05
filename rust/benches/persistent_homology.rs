use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use tcdb_core::{Simplex, SimplicialComplex};

fn bench_simplex_creation(c: &mut Criterion) {
    c.bench_function("simplex_creation", |b| {
        b.iter(|| {
            Simplex::new(black_box(vec![0, 1, 2, 3, 4]))
        });
    });
}

fn bench_simplex_faces(c: &mut Criterion) {
    let simplex = Simplex::new(vec![0, 1, 2, 3, 4]);
    
    c.bench_function("simplex_faces", |b| {
        b.iter(|| {
            black_box(&simplex).faces()
        });
    });
}

fn bench_complex_add_simplex(c: &mut Criterion) {
    c.bench_function("complex_add_simplex", |b| {
        b.iter(|| {
            let mut complex = SimplicialComplex::new();
            complex.add_simplex(Simplex::new(black_box(vec![0, 1, 2]))).unwrap();
        });
    });
}

fn bench_complex_euler_characteristic(c: &mut Criterion) {
    let mut group = c.benchmark_group("euler_characteristic");
    
    for size in [10, 50, 100, 200].iter() {
        let mut complex = SimplicialComplex::new();
        
        // Build a complex with many simplices
        for i in 0..*size {
            for j in (i+1)..*size {
                complex.add_simplex(Simplex::new(vec![i, j])).unwrap();
            }
        }
        
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                black_box(&complex).euler_characteristic()
            });
        });
    }
    
    group.finish();
}

fn bench_complex_verify_closure(c: &mut Criterion) {
    let mut complex = SimplicialComplex::new();
    
    // Build a tetrahedron
    complex.add_simplex(Simplex::new(vec![0, 1, 2])).unwrap();
    complex.add_simplex(Simplex::new(vec![0, 1, 3])).unwrap();
    complex.add_simplex(Simplex::new(vec![0, 2, 3])).unwrap();
    complex.add_simplex(Simplex::new(vec![1, 2, 3])).unwrap();
    
    c.bench_function("complex_verify_closure", |b| {
        b.iter(|| {
            black_box(&complex).verify_closure()
        });
    });
}

fn bench_rips_complex_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("rips_construction");
    
    for num_points in [10, 20, 50].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(num_points),
            num_points,
            |b, &n| {
                b.iter(|| {
                    let mut complex = SimplicialComplex::new();
                    
                    // Add vertices
                    for i in 0..n {
                        complex.add_simplex(Simplex::new(vec![i])).unwrap();
                    }
                    
                    // Add edges (complete graph for benchmark)
                    for i in 0..n {
                        for j in (i+1)..n {
                            complex.add_simplex(Simplex::new(vec![i, j])).unwrap();
                        }
                    }
                    
                    black_box(complex)
                });
            },
        );
    }
    
    group.finish();
}

criterion_group!(
    benches,
    bench_simplex_creation,
    bench_simplex_faces,
    bench_complex_add_simplex,
    bench_complex_euler_characteristic,
    bench_complex_verify_closure,
    bench_rips_complex_construction
);

criterion_main!(benches);

