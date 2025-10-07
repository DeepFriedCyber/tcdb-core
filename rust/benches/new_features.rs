use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use tcdb_core::euler::FVector;
use tcdb_core::bayes::{Evidence, posterior, sequential_update};
use tcdb_core::streaming::Streamer;
use tcdb_core::embed::{landscape_features, landscape_features_auto};

/// Benchmark Euler characteristic computation
fn bench_euler_characteristic(c: &mut Criterion) {
    let mut group = c.benchmark_group("euler_characteristic");
    
    // Standard complexes
    group.bench_function("point", |b| {
        b.iter(|| {
            let fv = FVector::point();
            black_box(fv.euler_characteristic())
        })
    });
    
    group.bench_function("triangle", |b| {
        b.iter(|| {
            let fv = FVector::triangle();
            black_box(fv.euler_characteristic())
        })
    });
    
    group.bench_function("tetrahedron", |b| {
        b.iter(|| {
            let fv = FVector::tetrahedron();
            black_box(fv.euler_characteristic())
        })
    });
    
    // Large complexes
    for size in [10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("large_complex", size), size, |b, &size| {
            let faces: Vec<usize> = (0..size).map(|i| i * 2).collect();
            b.iter(|| {
                let fv = FVector::new(faces.clone());
                black_box(fv.euler_characteristic())
            })
        });
    }
    
    // Disjoint union
    group.bench_function("disjoint_union", |b| {
        let t1 = FVector::triangle();
        let t2 = FVector::triangle();
        b.iter(|| {
            black_box(t1.disjoint_union(&t2))
        })
    });
    
    group.finish();
}

/// Benchmark Bayesian inference
fn bench_bayesian_inference(c: &mut Criterion) {
    let mut group = c.benchmark_group("bayesian_inference");
    
    // Single posterior update
    group.bench_function("posterior_single", |b| {
        let prior = 0.5;
        let ev = Evidence::new(0.9, 0.1);
        b.iter(|| {
            black_box(posterior(prior, ev.clone()))
        })
    });
    
    // Sequential updates
    for n in [2, 5, 10, 20].iter() {
        group.bench_with_input(BenchmarkId::new("sequential", n), n, |b, &n| {
            let prior = 0.5;
            let evidence: Vec<Evidence> = (0..n)
                .map(|i| Evidence::new(0.8 + (i as f64) * 0.01, 0.2))
                .collect();
            b.iter(|| {
                black_box(sequential_update(prior, &evidence))
            })
        });
    }
    
    group.finish();
}

/// Benchmark streaming filtrations
fn bench_streaming(c: &mut Criterion) {
    let mut group = c.benchmark_group("streaming");
    
    // Push operations
    for window_size in [10, 50, 100, 500].iter() {
        group.bench_with_input(BenchmarkId::new("push", window_size), window_size, |b, &size| {
            b.iter_batched(
                || Streamer::new(size),
                |mut streamer| {
                    for i in 0..100 {
                        streamer.push((i as f64, (i as f64).sin()));
                    }
                    black_box(streamer)
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }
    
    // PD computation
    for window_size in [10, 50, 100].iter() {
        group.bench_with_input(BenchmarkId::new("pd", window_size), window_size, |b, &size| {
            let mut streamer = Streamer::new(size);
            for i in 0..size {
                streamer.push((i as f64, (i as f64).sin()));
            }
            b.iter(|| {
                black_box(streamer.pd())
            })
        });
    }
    
    // Statistics computation
    group.bench_function("statistics", |b| {
        let mut streamer = Streamer::new(100);
        for i in 0..100 {
            streamer.push((i as f64, (i as f64).sin()));
        }
        b.iter(|| {
            black_box(streamer.statistics())
        })
    });
    
    group.finish();
}

/// Benchmark landscape embeddings
fn bench_landscape_embeddings(c: &mut Criterion) {
    let mut group = c.benchmark_group("landscape_embeddings");
    
    // Generate test persistence diagrams of varying sizes
    fn generate_pd(n: usize) -> Vec<(f64, f64)> {
        (0..n)
            .map(|i| {
                let birth = i as f64 * 0.1;
                let death = birth + 0.5 + (i as f64) * 0.05;
                (birth, death)
            })
            .collect()
    }
    
    // Landscape features with varying PD sizes
    for pd_size in [5, 10, 20, 50].iter() {
        group.bench_with_input(
            BenchmarkId::new("features_small", pd_size),
            pd_size,
            |b, &size| {
                let pd = generate_pd(size);
                b.iter(|| {
                    black_box(landscape_features(&pd, 2, 10, 0.0, 5.0))
                })
            },
        );
    }
    
    // Landscape features with varying levels
    for levels in [1, 2, 5, 10].iter() {
        group.bench_with_input(
            BenchmarkId::new("features_levels", levels),
            levels,
            |b, &levels| {
                let pd = generate_pd(20);
                b.iter(|| {
                    black_box(landscape_features(&pd, levels, 10, 0.0, 5.0))
                })
            },
        );
    }
    
    // Landscape features with varying samples
    for samples in [10, 50, 100, 200].iter() {
        group.bench_with_input(
            BenchmarkId::new("features_samples", samples),
            samples,
            |b, &samples| {
                let pd = generate_pd(20);
                b.iter(|| {
                    black_box(landscape_features(&pd, 2, samples, 0.0, 5.0))
                })
            },
        );
    }
    
    // Auto-range landscape features
    group.bench_function("features_auto", |b| {
        let pd = generate_pd(20);
        b.iter(|| {
            black_box(landscape_features_auto(&pd, 2, 10))
        })
    });
    
    group.finish();
}

/// Benchmark realistic workflows
fn bench_realistic_workflows(c: &mut Criterion) {
    let mut group = c.benchmark_group("realistic_workflows");
    
    // Workflow 1: Streaming + Landscape features
    group.bench_function("streaming_to_landscape", |b| {
        b.iter(|| {
            let mut streamer = Streamer::new(50);
            
            // Stream 100 samples
            for i in 0..100 {
                streamer.push((i as f64, (i as f64 * 0.1).sin()));
            }
            
            // Get PD
            let pd = streamer.pd();
            
            // Compute landscape features
            let features = landscape_features_auto(&pd, 2, 10);
            
            black_box(features)
        })
    });
    
    // Workflow 2: Multiple PDs + Bayesian classification
    group.bench_function("classification_workflow", |b| {
        let pd1 = vec![(0.0, 1.0), (0.5, 1.5)];
        let pd2 = vec![(0.0, 1.1), (0.5, 1.6)];
        
        b.iter(|| {
            // Compute features
            let f1 = landscape_features_auto(&pd1, 2, 10);
            let f2 = landscape_features_auto(&pd2, 2, 10);
            
            // Compute distance
            let dist: f64 = f1.iter()
                .zip(f2.iter())
                .map(|(a, b)| (a - b).powi(2))
                .sum::<f64>()
                .sqrt();
            
            // Use distance as evidence
            let evidence = if dist < 0.5 {
                Evidence::new(0.9, 0.1)
            } else {
                Evidence::new(0.1, 0.9)
            };
            
            let post = posterior(0.5, evidence);
            
            black_box(post)
        })
    });
    
    // Workflow 3: Euler characteristic + topology classification
    group.bench_function("topology_classification", |b| {
        b.iter(|| {
            // Compute Euler characteristics
            let sphere = FVector::new(vec![6, 12, 8]);
            let torus = FVector::new(vec![9, 27, 18]);
            
            let chi_sphere = sphere.euler_characteristic();
            let chi_torus = torus.euler_characteristic();
            
            // Classify based on chi
            let evidence = if chi_sphere == 2 {
                Evidence::new(0.9, 0.1)
            } else {
                Evidence::new(0.1, 0.9)
            };
            
            let post = posterior(0.5, evidence);
            
            black_box((chi_sphere, chi_torus, post))
        })
    });
    
    group.finish();
}

criterion_group!(
    benches,
    bench_euler_characteristic,
    bench_bayesian_inference,
    bench_streaming,
    bench_landscape_embeddings,
    bench_realistic_workflows
);
criterion_main!(benches);

