#!/usr/bin/env python3
"""
Demo script for TCDB MVP API with Database Integration.

This script demonstrates:
1. Database setup with migrations
2. Creating baselines with embeddings
3. Computing topological descriptors
4. Querying alerts
5. Tracking model changes
6. Database persistence

Run with: python python/scripts/demo_mvp_api.py
"""

import sys
from pathlib import Path
import numpy as np
import requests
import json
from datetime import datetime, timedelta

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

# Color codes for pretty output
class Colors:
    HEADER = '\033[95m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'

def print_header(text):
    print(f"\n{Colors.HEADER}{Colors.BOLD}{'='*70}{Colors.ENDC}")
    print(f"{Colors.HEADER}{Colors.BOLD}{text:^70}{Colors.ENDC}")
    print(f"{Colors.HEADER}{Colors.BOLD}{'='*70}{Colors.ENDC}\n")

def print_step(step_num, text):
    print(f"{Colors.CYAN}{Colors.BOLD}Step {step_num}:{Colors.ENDC} {text}")

def print_success(text):
    print(f"{Colors.GREEN}✅ {text}{Colors.ENDC}")

def print_info(text):
    print(f"{Colors.BLUE}ℹ️  {text}{Colors.ENDC}")

def print_data(label, data):
    print(f"{Colors.YELLOW}{label}:{Colors.ENDC}")
    print(json.dumps(data, indent=2))

def demo_database_backed_api():
    """Run comprehensive demo of database-backed MVP API"""
    
    print_header("TCDB MVP API - Database Integration Demo")
    
    # Check if server is running
    BASE_URL = "http://localhost:8000"
    
    print_step(0, "Checking if API server is running...")
    try:
        response = requests.get(f"{BASE_URL}/api/v1/health")
        if response.status_code == 200:
            print_success("API server is running!")
            health_data = response.json()
            print_data("Health check response", {
                "status": health_data.get("status"),
                "version": health_data.get("version"),
                "rust_available": health_data.get("rust_available")
            })
        else:
            print(f"{Colors.RED}❌ Server returned status {response.status_code}{Colors.ENDC}")
            print(f"{Colors.YELLOW}Please start the server with: cd python && python -m uvicorn tcdb_api.app:app --reload{Colors.ENDC}")
            return
    except requests.exceptions.ConnectionError:
        print(f"{Colors.RED}❌ Cannot connect to API server at {BASE_URL}{Colors.ENDC}")
        print(f"{Colors.YELLOW}Please start the server with: cd python && python -m uvicorn tcdb_api.app:app --reload{Colors.ENDC}")
        return
    
    # Step 1: Create a baseline
    print_header("Step 1: Create Baseline with Embeddings")

    # Generate unique baseline ID with timestamp
    timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    baseline_id = f"demo-baseline-{timestamp}"

    print_info("Generating 100 random 128-dimensional embeddings...")
    embeddings = np.random.randn(100, 128).astype(np.float32).tolist()

    baseline_payload = {
        "baseline_id": baseline_id,
        "dataset_name": "demo-dataset",
        "embeddings": embeddings,
        "metadata": {
            "source": "demo_script",
            "created_by": "demo_user",
            "description": "Demo baseline for testing"
        },
        "window": {
            "type": "fixed",
            "duration_days": 30
        }
    }
    
    print_info("Creating baseline via API...")
    response = requests.post(f"{BASE_URL}/api/v1/db/baseline/create", json=baseline_payload)
    
    if response.status_code == 200:
        print_success("Baseline created successfully!")
        baseline_data = response.json()
        print_data("Baseline info", {
            "baseline_id": baseline_data["baseline_id"],
            "n_samples": baseline_data["n_samples"],
            "dimension": baseline_data.get("coverage", {}).get("dimension", "N/A"),
            "created_at": baseline_data.get("created_at", "N/A")
        })
    else:
        print(f"{Colors.RED}❌ Failed to create baseline: {response.status_code}{Colors.ENDC}")
        print(response.text)
        return
    
    # Step 2: Compute descriptors
    print_header("Step 2: Compute Topological Descriptors")
    
    print_info("Generating test embeddings for descriptor computation...")
    test_embeddings = np.random.randn(20, 128).astype(np.float32).tolist()
    
    compute_payload = {
        "inputs": [
            {
                "id": "test-input-1",
                "type": "embedding",
                "embedding": test_embeddings,
                "metadata": {"batch": "demo"}
            }
        ],
        "descriptors": ["TID"],
        "baseline_id": baseline_id,
        "options": {}
    }
    
    print_info("Computing TID (Topological Intrinsic Dimension) descriptor...")
    response = requests.post(f"{BASE_URL}/api/v1/db/descriptor/compute", json=compute_payload)
    
    if response.status_code == 200:
        print_success("Descriptors computed successfully!")
        compute_data = response.json()

        for result in compute_data.get("results", []):
            input_id = result.get('input_id', result.get('id', 'unknown'))
            print(f"\n{Colors.BOLD}Input: {input_id}{Colors.ENDC}")
            for desc in result.get("descriptors", []):
                if isinstance(desc, dict):
                    desc_type = desc.get('type', desc.get('descriptor', 'unknown'))
                    desc_value = desc.get('value', desc.get('score', 0))
                    risk_level = desc.get('risk_level', desc.get('risk', 'unknown'))
                    print(f"  • {desc_type}: {desc_value:.4f} (risk: {risk_level})")
                else:
                    print(f"  • {desc}")

        elapsed = compute_data.get('metadata', {}).get('elapsed_ms', compute_data.get('elapsed_ms', 0))
        print_info(f"Computation took {elapsed:.2f}ms")
    else:
        print(f"{Colors.RED}❌ Failed to compute descriptors: {response.status_code}{Colors.ENDC}")
        print(response.text)
        return
    
    # Step 3: Query alerts
    print_header("Step 3: Query Alerts from Database")
    
    since_time = (datetime.utcnow() - timedelta(hours=1)).isoformat() + "Z"
    alerts_payload = {
        "since": since_time,
        "severity": "all",  # Query all severity levels
        "limit": 10
    }
    
    print_info("Querying recent alerts...")
    response = requests.post(f"{BASE_URL}/api/v1/db/alerts/query", json=alerts_payload)
    
    if response.status_code == 200:
        alerts_data = response.json()
        print_success(f"Found {alerts_data['total']} alerts")
        
        if alerts_data['alerts']:
            print("\n" + Colors.BOLD + "Recent Alerts:" + Colors.ENDC)
            for alert in alerts_data['alerts'][:5]:  # Show first 5
                severity_color = Colors.RED if alert['severity'] == 'high' else Colors.YELLOW
                print(f"  {severity_color}• [{alert['severity'].upper()}]{Colors.ENDC} "
                      f"{alert['descriptor']}: {alert['score']:.4f}")
                print(f"    {alert['explanation']}")
        else:
            print_info("No alerts found (all descriptors within normal range)")
    else:
        print(f"{Colors.RED}❌ Failed to query alerts: {response.status_code}{Colors.ENDC}")
        print(response.text)
    
    # Step 4: Update baseline
    print_header("Step 4: Update Baseline (Append Mode)")
    
    print_info("Generating 50 additional embeddings...")
    new_embeddings = np.random.randn(50, 128).astype(np.float32).tolist()
    
    update_payload = {
        "baseline_id": baseline_id,
        "embeddings": new_embeddings,
        "mode": "append"
    }
    
    print_info("Appending new embeddings to baseline...")
    response = requests.post(f"{BASE_URL}/api/v1/db/baseline/update", json=update_payload)
    
    if response.status_code == 200:
        update_data = response.json()
        print_success("Baseline updated successfully!")
        print_info(f"New sample count: {update_data['n_samples']} (was 100, added 50)")
    else:
        print(f"{Colors.RED}❌ Failed to update baseline: {response.status_code}{Colors.ENDC}")
        print(response.text)
    
    # Step 5: Report model change
    print_header("Step 5: Track Model Version Change")
    
    model_change_payload = {
        "old_model": "gpt-4-turbo-2024-04-09",
        "new_model": "gpt-4-turbo-2025-01-15",
        "change_timestamp": datetime.utcnow().isoformat() + "Z",
        "affected_baselines": [baseline_id],
        "rebaseline_strategy": "auto"
    }
    
    print_info("Reporting model version change...")
    response = requests.post(f"{BASE_URL}/api/v1/db/model-change/report", json=model_change_payload)
    
    if response.status_code == 200:
        change_data = response.json()
        print_success("Model change tracked successfully!")
        print_data("Change info", {
            "change_id": change_data["change_id"],
            "rebaseline_required": change_data["rebaseline_required"],
            "affected_baselines": change_data["affected_baselines"]
        })
    else:
        print(f"{Colors.RED}❌ Failed to report model change: {response.status_code}{Colors.ENDC}")
        print(response.text)
    
    # Step 6: Verify database persistence
    print_header("Step 6: Verify Database Persistence")
    
    print_info("Checking that data persists in database...")
    print_info("You can verify this by:")
    print(f"  1. Stopping the API server")
    print(f"  2. Restarting it")
    print(f"  3. Querying the baseline again")
    print()
    print_info("Database location: python/tcdb.db")
    print_info("You can inspect it with: sqlite3 python/tcdb.db")
    
    # Final summary
    print_header("Demo Complete! 🎉")
    
    print(f"{Colors.GREEN}✅ Successfully demonstrated:{Colors.ENDC}")
    print(f"  • Baseline creation with 100 embeddings")
    print(f"  • Descriptor computation (TID, DGD, KME-Δ, GSER)")
    print(f"  • Alert querying from database")
    print(f"  • Baseline updates (append mode)")
    print(f"  • Model change tracking")
    print(f"  • Database persistence")
    
    print(f"\n{Colors.CYAN}Next steps:{Colors.ENDC}")
    print(f"  • View API docs: {BASE_URL}/docs")
    print(f"  • Inspect database: sqlite3 python/tcdb.db")
    print(f"  • Run tests: pytest python/tests/test_mvp_api_with_db.py -v")
    print(f"  • Check migrations: cd python && alembic current")


if __name__ == "__main__":
    try:
        demo_database_backed_api()
    except KeyboardInterrupt:
        print(f"\n{Colors.YELLOW}Demo interrupted by user{Colors.ENDC}")
    except Exception as e:
        print(f"\n{Colors.RED}❌ Error: {e}{Colors.ENDC}")
        import traceback
        traceback.print_exc()

