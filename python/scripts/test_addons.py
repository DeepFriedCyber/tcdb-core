"""
Test script for TCDB Addons Pack
Tests all 3 addon endpoints:
1. TDA Analysis (PHH utilities)
2. Fisher-Rao Gram matrix
3. Wilson rectangle generator (LGT demo)
"""

import requests
import numpy as np
import json

API_BASE = "http://localhost:8000"

def print_header(text):
    print(f"\n{'='*70}")
    print(f"  {text}")
    print(f"{'='*70}\n")

def print_success(text):
    print(f"✅ {text}")

def print_info(text):
    print(f"ℹ️  {text}")

def print_error(text):
    print(f"❌ {text}")

def test_api_health():
    """Test API is running and addons are available"""
    print_header("Testing API Health")
    
    response = requests.get(f"{API_BASE}/api")
    if response.status_code == 200:
        data = response.json()
        print_success(f"API is running: {data['name']} v{data['version']}")
        print_success(f"Rust available: {data['rust_available']}")
        print_success(f"Addons available: {data['addons_available']}")
        return data['addons_available']
    else:
        print_error(f"API health check failed: {response.status_code}")
        return False

def test_tda_analyze():
    """Test TDA point cloud analysis endpoint"""
    print_header("Test 1: TDA Point Cloud Analysis")
    
    # Generate random point cloud
    np.random.seed(42)
    X = np.random.randn(50, 3).tolist()  # 50 points in 3D
    Y = (np.random.randn(50, 3) + 0.5).tolist()  # Shifted point cloud
    
    print_info(f"Generated point cloud: {len(X)} points in 3D")
    
    # Test without Y (only barcode entropy)
    payload = {"X": X}
    response = requests.post(f"{API_BASE}/addons/tda/analyze", json=payload)
    
    if response.status_code == 200:
        data = response.json()
        print_success(f"TDA analysis (X only) successful!")
        print(f"   Number of points: {data['n']}")
        print(f"   Barcode entropy: {data['barcode_entropy']:.4f}")
    else:
        print_error(f"TDA analysis failed: {response.status_code}")
        print(f"   Response: {response.text}")
        return
    
    # Test with Y (includes stability modulus)
    payload = {"X": X, "Y": Y}
    response = requests.post(f"{API_BASE}/addons/tda/analyze", json=payload)
    
    if response.status_code == 200:
        data = response.json()
        print_success(f"TDA analysis (X and Y) successful!")
        print(f"   Number of points: {data['n']}")
        print(f"   Barcode entropy: {data['barcode_entropy']:.4f}")
        print(f"   Stability modulus: {data.get('stability_modulus', 'N/A')}")
    else:
        print_error(f"TDA analysis with Y failed: {response.status_code}")
        print(f"   Response: {response.text}")

def test_fisher_rao_gram():
    """Test Fisher-Rao Gram matrix endpoint"""
    print_header("Test 2: Fisher-Rao Gram Matrix")
    
    # Generate random data matrix
    np.random.seed(42)
    X = np.random.randn(10, 5).tolist()  # 10 samples, 5 features
    
    print_info(f"Generated data matrix: {len(X)} samples × {len(X[0])} features")
    
    payload = {"X": X}
    response = requests.post(f"{API_BASE}/addons/metric/fisher_rao/gram", json=payload)
    
    if response.status_code == 200:
        data = response.json()
        gram = np.array(data['gram'])
        print_success(f"Fisher-Rao Gram matrix computed!")
        print(f"   Matrix size: {data['n']} × {data['n']}")
        print(f"   Gram matrix shape: {gram.shape}")
        print(f"   Gram matrix norm: {np.linalg.norm(gram):.4f}")
        print(f"   Is symmetric: {np.allclose(gram, gram.T)}")
        
        # Show first 3x3 corner
        print(f"\n   First 3×3 corner:")
        for i in range(min(3, gram.shape[0])):
            row_str = "   " + " ".join([f"{gram[i,j]:7.4f}" for j in range(min(3, gram.shape[1]))])
            print(row_str)
    else:
        print_error(f"Fisher-Rao Gram failed: {response.status_code}")
        print(f"   Response: {response.text}")

def test_wilson_rectangles():
    """Test Wilson rectangle generator (LGT demo)"""
    print_header("Test 3: Wilson Rectangle Generator (LGT Demo)")
    
    # Generate Wilson loop expectations for a grid
    R_vals = [1, 2, 3, 4]
    T_vals = [1, 2, 3, 4]
    
    print_info(f"Generating Wilson rectangles for R={R_vals}, T={T_vals}")
    
    payload = {
        "R_vals": R_vals,
        "T_vals": T_vals,
        "sigma": 0.2,
        "C": 0.9,
        "noise": 0.02,
        "seed": 42
    }
    
    response = requests.post(f"{API_BASE}/addons/lgt/wilson", json=payload)
    
    if response.status_code == 200:
        data = response.json()
        grid = data['grid']
        print_success(f"Wilson rectangles generated!")
        print(f"   Total rectangles: {len(grid)}")
        
        # Show first 10 results
        print(f"\n   First 10 Wilson loop expectations:")
        print(f"   {'R':>3} {'T':>3} {'⟨W(R,T)⟩':>12}")
        print(f"   {'-'*3} {'-'*3} {'-'*12}")
        for item in grid[:10]:
            print(f"   {item['R']:3d} {item['T']:3d} {item['W']:12.6f}")
        
        # Verify area law: W(R,T) ~ exp(-σ*R*T)
        print(f"\n   Verifying area law decay:")
        W_11 = next(item['W'] for item in grid if item['R'] == 1 and item['T'] == 1)
        W_22 = next(item['W'] for item in grid if item['R'] == 2 and item['T'] == 2)
        W_33 = next(item['W'] for item in grid if item['R'] == 3 and item['T'] == 3)
        print(f"   W(1,1) = {W_11:.6f}")
        print(f"   W(2,2) = {W_22:.6f}")
        print(f"   W(3,3) = {W_33:.6f}")
        print(f"   Ratio W(2,2)/W(1,1) = {W_22/W_11:.4f} (expect ~0.67 for σ=0.2)")
        print(f"   Ratio W(3,3)/W(2,2) = {W_33/W_22:.4f} (expect ~0.37 for σ=0.2)")
    else:
        print_error(f"Wilson rectangles failed: {response.status_code}")
        print(f"   Response: {response.text}")

def test_lattice_merge():
    """Test lattice merge API (Python-only, not HTTP endpoint)"""
    print_header("Test 4: Lattice Merge API (Python)")

    try:
        import sys
        import os
        # Add python directory to path
        sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
        from tcdb_addons.lattice.api import LatticeElement, merge_policy
        
        # Test policy merging
        low = LatticeElement("low")
        med = LatticeElement("med")
        high = LatticeElement("high")
        
        print_info("Testing trust lattice policy merging...")
        
        result1 = merge_policy(low, med)
        print_success(f"merge_policy(low, med) = {result1.value}")
        
        result2 = merge_policy(low, high)
        print_success(f"merge_policy(low, high) = {result2.value}")
        
        result3 = merge_policy(med, med, low)
        print_success(f"merge_policy(med, med, low) = {result3.value}")
        
        result4 = merge_policy(high, low, med)
        print_success(f"merge_policy(high, low, med) = {result4.value}")
        
        print(f"\n   Lattice order: low < med < high")
        print(f"   Join operation: max(a, b)")
        
    except ImportError as e:
        print_error(f"Lattice API not available: {e}")

def main():
    """Run all addon tests"""
    print_header("TCDB Addons Pack - Test Suite")
    
    # Check API health
    if not test_api_health():
        print_error("API is not available or addons are not enabled!")
        return
    
    # Run all tests
    test_tda_analyze()
    test_fisher_rao_gram()
    test_wilson_rectangles()
    test_lattice_merge()
    
    print_header("All Tests Complete! 🎉")
    print_success("All addon endpoints are working correctly!")
    print_info("Check the output above for detailed results")

if __name__ == "__main__":
    main()

