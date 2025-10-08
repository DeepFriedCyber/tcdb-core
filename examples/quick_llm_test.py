"""
Quick LLM Test - Minimal example with BERT

This is a simplified version that:
1. Loads a small BERT model
2. Extracts embeddings from two sentences
3. Tests drift detection

Requirements:
    pip install transformers torch
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'python'))

from tcdb_api.adapters import LLMAdapter, DescriptorClient
import numpy as np


def main():
    print("="*60)
    print("🧠 Quick LLM Test with BERT")
    print("="*60)
    
    # Check dependencies
    try:
        from transformers import AutoModel, AutoTokenizer
        import torch
    except ImportError:
        print("\n❌ Missing dependencies!")
        print("Install with: pip install transformers torch")
        return
    
    # Check API
    print("\n1️⃣ Checking API...")
    client = DescriptorClient("http://localhost:8000")
    if not client.health_check():
        print("❌ API not running. Start with:")
        print("   cd python && python -m uvicorn tcdb_api.app:app --reload")
        return
    print("✅ API is healthy")
    
    # Load model
    print("\n2️⃣ Loading BERT model...")
    model_name = "bert-base-uncased"
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    model = AutoModel.from_pretrained(model_name)
    model.eval()
    print(f"✅ Loaded {model_name}")
    
    # Test sentences
    baseline_text = "The cat sat on the mat."
    current_text = "The dog ran in the park."
    
    print(f"\n3️⃣ Processing sentences...")
    print(f"   Baseline: '{baseline_text}'")
    print(f"   Current:  '{current_text}'")
    
    # Extract embeddings
    def get_embeddings(text):
        inputs = tokenizer(text, return_tensors="pt")
        with torch.no_grad():
            outputs = model(**inputs)
        return outputs.last_hidden_state[0].numpy()
    
    baseline_emb = get_embeddings(baseline_text)
    current_emb = get_embeddings(current_text)
    
    print(f"   Baseline shape: {baseline_emb.shape}")
    print(f"   Current shape:  {current_emb.shape}")
    
    # Detect drift
    print("\n4️⃣ Computing descriptors...")
    adapter = LLMAdapter(client)
    
    result = adapter.detect_drift(
        current_embeddings=current_emb,
        baseline_embeddings=baseline_emb,
        threshold=0.5
    )
    
    # Results
    print("\n" + "="*60)
    print("📊 RESULTS")
    print("="*60)
    print(f"Drift detected: {result['drift_detected']}")
    print(f"Drift score:    {result['drift_score']:.4f}")
    print(f"Threshold:      {result['threshold']}")
    
    print("\nDescriptor details:")
    for desc_name, values in result['full_results'].items():
        print(f"\n{desc_name.upper()}:")
        for key, val in values.items():
            print(f"  {key}: {val:.4f}")
    
    print("\n✅ Test complete!")


if __name__ == "__main__":
    main()

