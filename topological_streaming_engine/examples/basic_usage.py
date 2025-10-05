#!/usr/bin/env python3
"""
Basic usage example
"""

try:
    from topological_py import PyStreamingPersistence

    # Create streaming engine
    engine = PyStreamingPersistence(window_size=10)

    # Add data points
    for i in range(20):
        point = [float(i), float(i**2), float(i**3)]
        diagram = engine.add_point(point)
        print(f"Point {i}: {len(diagram)} features")

    # Check for anomalies
    is_anomaly = engine.detect_anomaly(threshold=2.0)
    print(f"Anomaly detected: {is_anomaly}")

except ImportError:
    print("Please build Python bindings first:")
    print("  cd python_bindings && maturin develop")
