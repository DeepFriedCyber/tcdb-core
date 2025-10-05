import React, { useState, useEffect } from 'react';
import { LineChart, Line, XAxis, YAxis, CartesianGrid, Tooltip, Legend } from 'recharts';

function App() {
  const [alerts, setAlerts] = useState([]);
  const [priceData, setPriceData] = useState([]);

  useEffect(() => {
    // Simulate real-time data
    const interval = setInterval(() => {
      const newPrice = {
        time: new Date().toLocaleTimeString(),
        price: 100 + Math.random() * 10,
        volume: 1000 + Math.random() * 500
      };

      setPriceData(prev => [...prev.slice(-50), newPrice]);

      // Random alert
      if (Math.random() > 0.95) {
        setAlerts(prev => [...prev, {
          time: newPrice.time,
          message: 'Anomaly detected!'
        }]);
      }
    }, 1000);

    return () => clearInterval(interval);
  }, []);

  return (
    <div style={{ padding: '20px', fontFamily: 'Arial' }}>
      <h1>🔍 Topological Streaming Engine</h1>
      <h2>Flash Crash Monitor</h2>

      <div style={{ marginBottom: '20px' }}>
        <h3>Price Chart</h3>
        <LineChart width={800} height={300} data={priceData}>
          <CartesianGrid strokeDasharray="3 3" />
          <XAxis dataKey="time" />
          <YAxis />
          <Tooltip />
          <Legend />
          <Line type="monotone" dataKey="price" stroke="#8884d8" />
        </LineChart>
      </div>

      <div>
        <h3>Recent Alerts ({alerts.length})</h3>
        <div style={{ maxHeight: '200px', overflow: 'auto', border: '1px solid #ccc', padding: '10px' }}>
          {alerts.slice(-10).reverse().map((alert, i) => (
            <div key={i} style={{ padding: '5px', borderBottom: '1px solid #eee' }}>
              ⚠️ {alert.time}: {alert.message}
            </div>
          ))}
        </div>
      </div>
    </div>
  );
}

export default App;
