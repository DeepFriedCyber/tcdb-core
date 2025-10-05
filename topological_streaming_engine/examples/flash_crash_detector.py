#!/usr/bin/env python3
"""
Flash Crash Detector using Streaming Persistent Homology
"""

import numpy as np
import time
from typing import List, Tuple
try:
    from topological_py import PyStreamingPersistence
except ImportError:
    print("Warning: Rust bindings not available, using Python fallback")
    PyStreamingPersistence = None

class FlashCrashDetector:
    def __init__(self, window_size: int = 100, threshold: float = 2.0):
        self.window_size = window_size
        self.threshold = threshold
        if PyStreamingPersistence:
            self.engine = PyStreamingPersistence(window_size)
        else:
            self.engine = None
        self.alerts = []

    def process_price(self, price: float, volume: float, timestamp: float) -> bool:
        """Process new market data point"""
        point = [price, volume, timestamp]

        if self.engine:
            is_anomaly = self.engine.detect_anomaly(self.threshold)
        else:
            # Fallback: simple volatility check
            is_anomaly = abs(price) > self.threshold

        if is_anomaly:
            alert = {
                'timestamp': timestamp,
                'price': price,
                'volume': volume,
                'type': 'FLASH_CRASH_WARNING'
            }
            self.alerts.append(alert)
            print(f"⚠️  ALERT: {alert}")

        return is_anomaly

    def simulate_market_data(self, n_points: int = 1000):
        """Simulate market data with occasional crashes"""
        print(f"Simulating {n_points} market data points...")

        for i in range(n_points):
            # Normal market behavior
            price = 100 + np.random.randn() * 0.5
            volume = 1000 + np.random.randn() * 100

            # Inject flash crash at 30%, 60%
            if i == int(n_points * 0.3) or i == int(n_points * 0.6):
                price -= 10  # Sudden drop
                volume *= 5  # Volume spike

            timestamp = time.time() + i
            self.process_price(price, volume, timestamp)

            if i % 100 == 0:
                print(f"Processed {i}/{n_points} points, {len(self.alerts)} alerts")

        print(f"\n✅ Simulation complete: {len(self.alerts)} anomalies detected")
        return self.alerts

if __name__ == "__main__":
    detector = FlashCrashDetector(window_size=50, threshold=1.5)
    alerts = detector.simulate_market_data(1000)

    print("\n" + "="*50)
    print(f"Total alerts: {len(alerts)}")
    for alert in alerts:
        print(f"  - {alert['type']} at t={alert['timestamp']:.2f}")
