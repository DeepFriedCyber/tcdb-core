"""Debug Demo 1 - Check TCDB scores"""
import numpy as np
import sys
sys.path.insert(0, 'python')

from scripts.use_case_demos import (
    generate_normal_embeddings,
    generate_hallucination_embeddings,
    TCDBClient
)

# Generate small test
baseline_emb = generate_normal_embeddings(n=100, dim=128, seed=42)
normal_test = generate_normal_embeddings(n=20, dim=128, seed=43)
halluc_test = generate_hallucination_embeddings(n=10, dim=128, mode="novel-cluster", seed=44)

test_emb = np.vstack([normal_test, halluc_test])
labels = np.array([0] * 20 + [1] * 10)

# Create client and baseline
client = TCDBClient()
baseline_id = f"debug-baseline-{np.random.randint(10000)}"
client.create_baseline(baseline_id, baseline_emb)

# Compute scores
results = client.compute_descriptors(test_emb, baseline_id)
scores = np.array([r.score for r in results])
z_scores = np.array([r.descriptor_scores.get('z_score', 0) for r in results])

print(f"Scores shape: {scores.shape}")
print(f"Scores min/max: {scores.min():.4f} / {scores.max():.4f}")
print(f"Scores mean/std: {scores.mean():.4f} / {scores.std():.4f}")
print(f"\nZ-scores min/max: {z_scores.min():.4f} / {z_scores.max():.4f}")
print(f"Z-scores mean/std: {z_scores.mean():.4f} / {z_scores.std():.4f}")
print(f"\nFirst 10 scores (normal): {scores[:10]}")
print(f"Last 10 scores (halluc): {scores[-10:]}")
print(f"\nFirst 10 z-scores (normal): {z_scores[:10]}")
print(f"Last 10 z-scores (halluc): {z_scores[-10:]}")
print(f"\nNormal mean: {scores[:20].mean():.4f}")
print(f"Halluc mean: {scores[20:].mean():.4f}")

