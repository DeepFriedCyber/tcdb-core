"""
Streaming Filtrations Example

Demonstrates real-time topological analysis with sliding windows.
"""

import tcdb_core
import math


def main():
    print("=" * 60)
    print("Streaming Filtrations Examples")
    print("=" * 60)
    
    # Basic streaming
    print("\n1. Basic Streaming:")
    print("-" * 40)
    
    streamer = tcdb_core.Streamer(10)
    
    print(f"Initial state: len={streamer.len()}, empty={streamer.is_empty()}")
    
    # Add samples
    for i in range(5):
        streamer.push((float(i), float(i)))
    
    print(f"After 5 samples: len={streamer.len()}, empty={streamer.is_empty()}")
    
    # Get persistence diagram
    pd = streamer.pd()
    print(f"Persistence diagram: {len(pd)} features")
    
    # Window statistics
    print("\n2. Window Statistics:")
    print("-" * 40)
    
    streamer = tcdb_core.Streamer(20)
    
    for i in range(10):
        streamer.push((float(i), float(i) ** 2))
    
    stats = streamer.statistics()
    if stats:
        min_val, max_val, mean, std_dev = stats
        print(f"Min: {min_val:.2f}")
        print(f"Max: {max_val:.2f}")
        print(f"Mean: {mean:.2f}")
        print(f"Std Dev: {std_dev:.2f}")
    
    # Sliding window
    print("\n3. Sliding Window Behavior:")
    print("-" * 40)
    
    streamer = tcdb_core.Streamer(5)
    
    print("Adding samples to window of size 5:")
    for i in range(8):
        streamer.push((float(i), float(i)))
        print(f"  Sample {i}: window size = {streamer.len()}")
    
    # Streaming sine wave
    print("\n4. Streaming Sine Wave:")
    print("-" * 40)
    
    streamer = tcdb_core.Streamer(50)
    
    print("Streaming 100 samples of sine wave...")
    for i in range(100):
        t = i * 0.1
        value = math.sin(t)
        streamer.push((t, value))
        
        if i % 20 == 0:
            pd = streamer.pd()
            stats = streamer.statistics()
            if stats:
                _, _, mean, _ = stats
                print(f"  t={t:.1f}: window={streamer.len()}, features={len(pd)}, mean={mean:.2f}")
    
    # Real-time anomaly detection
    print("\n5. Real-Time Anomaly Detection:")
    print("-" * 40)
    
    streamer = tcdb_core.Streamer(30)
    
    print("Monitoring data stream for anomalies...")
    
    # Normal data
    for i in range(20):
        value = math.sin(i * 0.2) + 0.1 * (i % 3)
        streamer.push((float(i), value))
    
    # Baseline persistence
    pd_normal = streamer.pd()
    baseline_features = len(pd_normal)
    print(f"Baseline: {baseline_features} topological features")
    
    # Inject anomaly
    streamer.push((20.0, 10.0))  # Spike!
    
    pd_anomaly = streamer.pd()
    anomaly_features = len(pd_anomaly)
    
    if anomaly_features != baseline_features:
        print(f"⚠️  ANOMALY DETECTED at t=20!")
        print(f"   Features changed: {baseline_features} → {anomaly_features}")
    
    # Continue normal data
    for i in range(21, 30):
        value = math.sin(i * 0.2) + 0.1 * (i % 3)
        streamer.push((float(i), value))
    
    pd_recovered = streamer.pd()
    print(f"After recovery: {len(pd_recovered)} features")
    
    # Clear and restart
    print("\n6. Clear and Restart:")
    print("-" * 40)
    
    streamer = tcdb_core.Streamer(10)
    
    for i in range(5):
        streamer.push((float(i), float(i)))
    
    print(f"Before clear: len={streamer.len()}")
    
    streamer.clear()
    
    print(f"After clear: len={streamer.len()}, empty={streamer.is_empty()}")
    
    # Time series monitoring
    print("\n7. Time Series Monitoring:")
    print("-" * 40)
    
    streamer = tcdb_core.Streamer(100)
    
    print("Monitoring time series with trend...")
    
    # Linear trend + noise
    for i in range(150):
        trend = 0.1 * i
        noise = 0.5 * math.sin(i * 0.5)
        value = trend + noise
        streamer.push((float(i), value))
        
        if i % 30 == 0 and i > 0:
            stats = streamer.statistics()
            if stats:
                min_val, max_val, mean, _ = stats
                print(f"  t={i}: range=[{min_val:.1f}, {max_val:.1f}], mean={mean:.1f}")
    
    print("\n" + "=" * 60)


if __name__ == "__main__":
    main()

