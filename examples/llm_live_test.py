"""
Live LLM Test - Connect a real transformer model to TCDB descriptors

This script demonstrates:
1. Loading a pre-trained transformer (BERT/GPT-2)
2. Extracting embeddings and attention weights
3. Using the LLM adapter to detect drift
4. Analyzing attention patterns with descriptors

Requirements:
    pip install transformers torch numpy scipy requests
"""

from __future__ import annotations

import sys
import os
import numpy as np
import requests

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'python'))

from tcdb_api.adapters import LLMAdapter, DescriptorClient


def check_api_health(base_url: str = "http://localhost:8000") -> bool:
    """Check if the API is running."""
    try:
        response = requests.get(f"{base_url}/descriptor/health", timeout=5)
        return response.status_code == 200
    except:
        return False


def load_model_and_tokenizer(model_name: str = "bert-base-uncased"):
    """Load a transformer model and tokenizer."""
    try:
        from transformers import AutoModel, AutoTokenizer
        import torch
    except ImportError:
        print("❌ Error: transformers and torch not installed")
        print("Install with: pip install transformers torch")
        sys.exit(1)
    
    print(f"\n📦 Loading model: {model_name}")
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    model = AutoModel.from_pretrained(model_name, output_attentions=True)
    model.eval()
    
    print(f"✅ Model loaded successfully")
    print(f"   Hidden size: {model.config.hidden_size}")
    print(f"   Num layers: {model.config.num_hidden_layers}")
    print(f"   Num heads: {model.config.num_attention_heads}")
    
    return model, tokenizer


def extract_embeddings_and_attention(model, tokenizer, text: str):
    """Extract embeddings and attention from a text."""
    import torch
    
    # Tokenize
    inputs = tokenizer(text, return_tensors="pt", padding=True, truncation=True, max_length=512)
    
    # Forward pass
    with torch.no_grad():
        outputs = model(**inputs)
    
    # Extract embeddings (last hidden state)
    embeddings = outputs.last_hidden_state[0].numpy()  # (seq_len, hidden_dim)
    
    # Extract attention (average over heads for simplicity)
    attention = outputs.attentions[-1][0].mean(dim=0).numpy()  # (seq_len, seq_len)
    
    return embeddings, attention, inputs['input_ids'][0].tolist()


def test_semantic_drift():
    """Test semantic drift detection between different text domains."""
    print("\n" + "="*70)
    print("TEST 1: Semantic Drift Detection")
    print("="*70)
    
    # Load model
    model, tokenizer = load_model_and_tokenizer("bert-base-uncased")
    
    # Baseline: Technical text
    baseline_text = """
    The algorithm computes the topological features of high-dimensional data
    using persistent homology and Betti numbers. The computational complexity
    is polynomial in the number of data points.
    """
    
    # Current: Medical text (different domain)
    current_text = """
    The patient presented with acute symptoms including fever and fatigue.
    Laboratory tests revealed elevated white blood cell counts. Treatment
    with antibiotics was initiated immediately.
    """
    
    print("\n📝 Baseline text (Technical):")
    print(f"   {baseline_text.strip()[:80]}...")
    
    print("\n📝 Current text (Medical):")
    print(f"   {current_text.strip()[:80]}...")
    
    # Extract embeddings
    print("\n🔬 Extracting embeddings...")
    baseline_emb, _, _ = extract_embeddings_and_attention(model, tokenizer, baseline_text)
    current_emb, _, _ = extract_embeddings_and_attention(model, tokenizer, current_text)
    
    print(f"   Baseline shape: {baseline_emb.shape}")
    print(f"   Current shape: {current_emb.shape}")
    
    # Use adapter to detect drift
    print("\n🚀 Computing descriptors...")
    client = DescriptorClient("http://localhost:8000")
    adapter = LLMAdapter(client)
    
    drift_result = adapter.detect_drift(
        current_embeddings=current_emb,
        baseline_embeddings=baseline_emb,
        threshold=0.3
    )
    
    # Display results
    print("\n" + "="*70)
    print("RESULTS:")
    print("="*70)
    print(f"Drift detected: {drift_result['drift_detected']}")
    print(f"Drift score: {drift_result['drift_score']:.4f}")
    print(f"Threshold: {drift_result['threshold']}")
    
    print("\nFull descriptor results:")
    for desc_name, desc_results in drift_result['full_results'].items():
        print(f"\n{desc_name.upper()}:")
        for key, value in desc_results.items():
            print(f"  {key}: {value:.4f}")
    
    return drift_result


def test_attention_analysis():
    """Test attention pattern analysis."""
    print("\n" + "="*70)
    print("TEST 2: Attention Pattern Analysis")
    print("="*70)
    
    # Load model
    model, tokenizer = load_model_and_tokenizer("bert-base-uncased")
    
    # Test text with clear structure
    text = """
    The quick brown fox jumps over the lazy dog.
    This sentence contains every letter of the alphabet.
    """
    
    print("\n📝 Input text:")
    print(f"   {text.strip()}")
    
    # Extract embeddings and attention
    print("\n🔬 Extracting embeddings and attention...")
    embeddings, attention, token_ids = extract_embeddings_and_attention(model, tokenizer, text)
    
    print(f"   Embeddings shape: {embeddings.shape}")
    print(f"   Attention shape: {attention.shape}")
    print(f"   Num tokens: {len(token_ids)}")
    
    # Decode tokens
    tokens = tokenizer.convert_ids_to_tokens(token_ids)
    print(f"\n   Tokens: {' '.join(tokens[:10])}...")
    
    # Analyze attention structure
    print("\n🚀 Analyzing attention structure...")
    client = DescriptorClient("http://localhost:8000")
    adapter = LLMAdapter(client)
    
    attention_result = adapter.analyze_attention_structure(
        attention=attention,
        tau=0.1  # Threshold for attention graph
    )
    
    # Display results
    print("\n" + "="*70)
    print("RESULTS:")
    print("="*70)
    
    for desc_name, desc_results in attention_result.items():
        print(f"\n{desc_name.upper()}:")
        for key, value in desc_results.items():
            print(f"  {key}: {value:.4f}")
    
    # Visualize attention statistics
    print("\n📊 Attention Statistics:")
    print(f"   Mean attention: {attention.mean():.4f}")
    print(f"   Max attention: {attention.max():.4f}")
    print(f"   Sparsity (< 0.1): {(attention < 0.1).sum() / attention.size * 100:.1f}%")
    
    return attention_result


def test_fine_tuning_drift():
    """Simulate fine-tuning drift by comparing different model sizes."""
    print("\n" + "="*70)
    print("TEST 3: Fine-Tuning Drift (Model Size Comparison)")
    print("="*70)
    
    # Use same text for both models
    text = "The transformer architecture revolutionized natural language processing."
    
    print("\n📝 Test text:")
    print(f"   {text}")
    
    # Load base model
    print("\n📦 Loading base model (bert-base-uncased)...")
    model_base, tokenizer_base = load_model_and_tokenizer("bert-base-uncased")
    
    # Extract from base
    print("🔬 Extracting from base model...")
    emb_base, _, _ = extract_embeddings_and_attention(model_base, tokenizer_base, text)
    
    print(f"   Base embeddings shape: {emb_base.shape}")
    
    # For comparison, we'll use the same model but with different random seed
    # (simulating a fine-tuned version)
    print("\n🔬 Simulating fine-tuned model (adding noise)...")
    
    # Add controlled noise to simulate fine-tuning changes
    np.random.seed(42)
    noise_level = 0.1
    emb_finetuned = emb_base + np.random.randn(*emb_base.shape) * noise_level * emb_base.std()
    
    print(f"   Fine-tuned embeddings shape: {emb_finetuned.shape}")
    print(f"   Noise level: {noise_level}")
    
    # Detect drift
    print("\n🚀 Computing drift...")
    client = DescriptorClient("http://localhost:8000")
    adapter = LLMAdapter(client)
    
    drift_result = adapter.detect_drift(
        current_embeddings=emb_finetuned,
        baseline_embeddings=emb_base,
        threshold=0.2
    )
    
    # Display results
    print("\n" + "="*70)
    print("RESULTS:")
    print("="*70)
    print(f"Drift detected: {drift_result['drift_detected']}")
    print(f"Drift score: {drift_result['drift_score']:.4f}")
    print(f"Threshold: {drift_result['threshold']}")
    
    # Compute actual embedding distance for comparison
    emb_dist = np.linalg.norm(emb_base - emb_finetuned) / np.linalg.norm(emb_base)
    print(f"\nRelative L2 distance: {emb_dist:.4f}")
    
    return drift_result


def main():
    """Run all tests."""
    print("="*70)
    print("🧠 TCDB LLM Live Test")
    print("="*70)
    print("\nThis script tests the TCDB descriptor system with real LLMs")
    
    # Check API
    print("\n🔍 Checking API status...")
    if not check_api_health():
        print("❌ Error: API is not running")
        print("\nPlease start the API first:")
        print("  cd python")
        print("  python -m uvicorn tcdb_api.app:app --reload")
        sys.exit(1)
    
    print("✅ API is healthy")
    
    # Run tests
    try:
        # Test 1: Semantic drift
        test_semantic_drift()
        
        # Test 2: Attention analysis
        test_attention_analysis()
        
        # Test 3: Fine-tuning drift
        test_fine_tuning_drift()
        
        print("\n" + "="*70)
        print("✅ ALL TESTS COMPLETED SUCCESSFULLY!")
        print("="*70)
        
    except Exception as e:
        print(f"\n❌ Error during testing: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()

