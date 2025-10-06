#!/usr/bin/env python3
"""
TCDB API Test Script
Test all API endpoints with your API key
"""

import requests
import json

# Get your API key from the dashboard at https://tcdb.uk/dashboard
API_KEY = input("Enter your API key from https://tcdb.uk/dashboard: ").strip()

BASE_URL = "https://tcdb.uk/api/v1"

headers = {
    "Authorization": f"Bearer {API_KEY}",
    "Content-Type": "application/json"
}

def test_health():
    """Test health check endpoint"""
    print("\n" + "="*60)
    print("Testing Health Check")
    print("="*60)
    
    response = requests.get(f"{BASE_URL}/health", headers=headers)
    print(f"Status: {response.status_code}")
    print(f"Response: {json.dumps(response.json(), indent=2)}")
    return response.status_code == 200

def test_topology_signature():
    """Test topological signature generation"""
    print("\n" + "="*60)
    print("Testing Topological Signature")
    print("="*60)
    
    data = {
        "data": [1.0, 2.5, 3.2, 4.1, 5.0, 6.3, 7.1, 8.5],
        "method": "vietoris_rips",
        "max_dimension": 2
    }
    
    response = requests.post(
        f"{BASE_URL}/topology/signature",
        headers=headers,
        json=data
    )
    
    print(f"Status: {response.status_code}")
    print(f"Response: {json.dumps(response.json(), indent=2)}")
    return response.status_code == 200

def test_provenance_track():
    """Test provenance tracking"""
    print("\n" + "="*60)
    print("Testing Provenance Tracking")
    print("="*60)
    
    data = {
        "operation": "model_inference",
        "inputs": ["embedding_data", "model_weights"],
        "outputs": ["prediction", "confidence_score"],
        "metadata": {
            "model": "gpt-4",
            "version": "1.0",
            "user": "test_user"
        }
    }
    
    response = requests.post(
        f"{BASE_URL}/provenance/track",
        headers=headers,
        json=data
    )
    
    print(f"Status: {response.status_code}")
    print(f"Response: {json.dumps(response.json(), indent=2)}")
    return response.status_code == 200

def test_data_proof():
    """Test data proof generation"""
    print("\n" + "="*60)
    print("Testing Data Proof")
    print("="*60)
    
    data = {
        "data": ["item1", "item2", "item3", "item4", "item5"],
        "proof_type": "membership"
    }
    
    response = requests.post(
        f"{BASE_URL}/data/proof",
        headers=headers,
        json=data
    )
    
    print(f"Status: {response.status_code}")
    print(f"Response: {json.dumps(response.json(), indent=2)}")
    return response.status_code == 200

def test_cross_domain_reason():
    """Test cross-domain reasoning"""
    print("\n" + "="*60)
    print("Testing Cross-Domain Reasoning")
    print("="*60)
    
    data = {
        "domain_a": "neural_networks",
        "domain_b": "power_grids",
        "data_a": [0.5, 0.8, 0.3, 0.9, 0.7],
        "data_b": [0.6, 0.7, 0.4, 0.8, 0.75]
    }
    
    response = requests.post(
        f"{BASE_URL}/cross-domain/reason",
        headers=headers,
        json=data
    )
    
    print(f"Status: {response.status_code}")
    print(f"Response: {json.dumps(response.json(), indent=2)}")
    return response.status_code == 200

def main():
    """Run all tests"""
    print("\n" + "="*60)
    print("TCDB API Test Suite")
    print("="*60)
    print(f"Base URL: {BASE_URL}")
    print(f"API Key: {API_KEY[:15]}...")
    
    results = {
        "Health Check": test_health(),
        "Topological Signature": test_topology_signature(),
        "Provenance Tracking": test_provenance_track(),
        "Data Proof": test_data_proof(),
        "Cross-Domain Reasoning": test_cross_domain_reason()
    }
    
    print("\n" + "="*60)
    print("Test Results Summary")
    print("="*60)
    
    for test_name, passed in results.items():
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"{test_name}: {status}")
    
    total = len(results)
    passed = sum(results.values())
    print(f"\nTotal: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n🎉 All tests passed! Your API is working perfectly!")
    else:
        print("\n⚠️  Some tests failed. Check the output above for details.")

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\nTest interrupted by user.")
    except Exception as e:
        print(f"\n❌ Error: {e}")

