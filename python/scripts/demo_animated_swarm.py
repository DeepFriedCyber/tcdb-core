#!/usr/bin/env python3
"""
Animated Swarm Detection Demo

Shows real-time visualization of:
1. Agent embeddings evolving over time
2. Entropy dropping as coordination increases
3. Top-k mass rising as agents align
4. Detection threshold being crossed

Usage:
    python demo_animated_swarm.py --scenario Swarm --animate
    python demo_animated_swarm.py --scenario Swarm --save-gif
"""
import argparse
import json
import sys
import time
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.animation as animation
from pathlib import Path
from matplotlib.patches import Rectangle

# Add scripts directory to path
sys.path.insert(0, str(Path(__file__).parent))


class AnimatedSwarmDemo:
    """Animated visualization of swarm detection."""
    
    def __init__(self, scenario='Swarm', n_agents=64, n_steps=30):
        self.scenario = scenario
        self.n_agents = n_agents
        self.n_steps = n_steps
        
        # Generate data
        self.events = self.generate_data()
        
        # Analysis results
        self.baseline_results = []
        self.tcdb_results = []
        
        # Setup figure
        self.setup_figure()
        
    def generate_data(self):
        """Generate synthetic swarm data."""
        events = []
        
        # Set sync strength based on scenario
        if self.scenario == "Swarm":
            base_sync = 0.1
            final_sync = 0.95
        else:
            base_sync = 0.1
            final_sync = 0.15
        
        for t in range(self.n_steps):
            # Ramp sync strength
            alpha = t / max(1, self.n_steps - 1)
            sync = base_sync + alpha * (final_sync - base_sync)
            
            # Generate embeddings
            dim = 32
            embeddings = []
            
            # Create a common direction for coordination
            common_dir = np.random.randn(dim)
            common_dir /= np.linalg.norm(common_dir)
            
            for i in range(self.n_agents):
                # Mix common direction with random noise
                noise = np.random.randn(dim)
                noise /= np.linalg.norm(noise)
                
                emb = sync * common_dir + (1 - sync) * noise
                emb /= np.linalg.norm(emb)
                embeddings.append(emb)
            
            events.append({
                't': t,
                'sync': sync,
                'embeddings': embeddings,
                'edges': []
            })
        
        return events
    
    def setup_figure(self):
        """Setup matplotlib figure with 4 subplots."""
        self.fig = plt.figure(figsize=(16, 10))
        self.fig.suptitle(f'Animated Swarm Detection Demo - {self.scenario} Scenario', 
                         fontsize=16, fontweight='bold')
        
        # Create grid
        gs = self.fig.add_gridspec(3, 2, hspace=0.3, wspace=0.3)
        
        # Subplot 1: Agent embeddings (2D projection)
        self.ax1 = self.fig.add_subplot(gs[0, 0])
        self.ax1.set_title('Agent Embeddings (PCA 2D)', fontweight='bold')
        self.ax1.set_xlabel('PC1')
        self.ax1.set_ylabel('PC2')
        self.ax1.grid(True, alpha=0.3)
        
        # Subplot 2: Sync strength over time
        self.ax2 = self.fig.add_subplot(gs[0, 1])
        self.ax2.set_title('Synchronization Strength', fontweight='bold')
        self.ax2.set_xlabel('Time Step')
        self.ax2.set_ylabel('Sync Strength')
        self.ax2.set_ylim(0, 1)
        self.ax2.grid(True, alpha=0.3)
        
        # Subplot 3: Entropy over time
        self.ax3 = self.fig.add_subplot(gs[1, 0])
        self.ax3.set_title('TCDB: Entropy (Distance Distribution)', fontweight='bold')
        self.ax3.set_xlabel('Time Step')
        self.ax3.set_ylabel('Entropy')
        self.ax3.grid(True, alpha=0.3)
        
        # Subplot 4: Top-k mass over time
        self.ax4 = self.fig.add_subplot(gs[1, 1])
        self.ax4.set_title('TCDB: Top-k Gram Mass', fontweight='bold')
        self.ax4.set_xlabel('Time Step')
        self.ax4.set_ylabel('Top-k Mass')
        self.ax4.set_ylim(0, 1)
        self.ax4.grid(True, alpha=0.3)
        
        # Subplot 5: Baseline magnetization
        self.ax5 = self.fig.add_subplot(gs[2, 0])
        self.ax5.set_title('Baseline: Magnetization (Kaggle)', fontweight='bold')
        self.ax5.set_xlabel('Time Step')
        self.ax5.set_ylabel('Magnetization')
        self.ax5.grid(True, alpha=0.3)
        
        # Subplot 6: Detection status
        self.ax6 = self.fig.add_subplot(gs[2, 1])
        self.ax6.set_title('Detection Status', fontweight='bold')
        self.ax6.set_xlim(0, 1)
        self.ax6.set_ylim(0, 1)
        self.ax6.axis('off')
        
    def analyze_event(self, event):
        """Analyze a single event with both methods."""
        embeddings = np.array(event['embeddings'])
        
        # Baseline: Magnetization
        from scipy.spatial.distance import pdist
        distances = pdist(embeddings, metric='euclidean')
        dist_var = np.var(distances)
        magnetization = 1.0 / (1.0 + dist_var)
        
        # TCDB: Entropy and Gram mass
        from demo_driver import SwarmDriver
        driver = SwarmDriver(use_local=True)
        result = driver.process(event)
        
        return {
            'magnetization': magnetization,
            'entropy': result['entropy'],
            'topk_mass': result['topk_mass'],
            'flag': result['flag']
        }
    
    def init_animation(self):
        """Initialize animation."""
        return []
    
    def update_frame(self, frame):
        """Update animation frame."""
        if frame >= len(self.events):
            return []
        
        event = self.events[frame]
        
        # Analyze event
        analysis = self.analyze_event(event)
        self.baseline_results.append(analysis['magnetization'])
        self.tcdb_results.append({
            'entropy': analysis['entropy'],
            'topk_mass': analysis['topk_mass'],
            'flag': analysis['flag']
        })
        
        # Update subplot 1: Agent embeddings (PCA 2D)
        self.ax1.clear()
        self.ax1.set_title(f'Agent Embeddings (PCA 2D) - Step {frame}', fontweight='bold')
        self.ax1.set_xlabel('PC1')
        self.ax1.set_ylabel('PC2')
        self.ax1.grid(True, alpha=0.3)
        
        embeddings = np.array(event['embeddings'])
        from sklearn.decomposition import PCA
        pca = PCA(n_components=2)
        coords_2d = pca.fit_transform(embeddings)
        
        self.ax1.scatter(coords_2d[:, 0], coords_2d[:, 1], 
                        c=range(self.n_agents), cmap='viridis', 
                        s=50, alpha=0.6, edgecolors='black', linewidth=0.5)
        
        # Update subplot 2: Sync strength
        self.ax2.clear()
        self.ax2.set_title('Synchronization Strength', fontweight='bold')
        self.ax2.set_xlabel('Time Step')
        self.ax2.set_ylabel('Sync Strength')
        self.ax2.set_ylim(0, 1)
        self.ax2.grid(True, alpha=0.3)
        
        sync_values = [e['sync'] for e in self.events[:frame+1]]
        self.ax2.plot(range(len(sync_values)), sync_values, 'b-', linewidth=2)
        self.ax2.scatter(frame, event['sync'], c='red', s=100, zorder=5)
        
        # Update subplot 3: Entropy
        self.ax3.clear()
        self.ax3.set_title('TCDB: Entropy (Distance Distribution)', fontweight='bold')
        self.ax3.set_xlabel('Time Step')
        self.ax3.set_ylabel('Entropy')
        self.ax3.grid(True, alpha=0.3)
        
        entropy_values = [r['entropy'] for r in self.tcdb_results]
        self.ax3.plot(range(len(entropy_values)), entropy_values, 'g-', linewidth=2)
        self.ax3.scatter(frame, analysis['entropy'], c='red', s=100, zorder=5)
        
        # Add baseline threshold
        if len(entropy_values) >= 5:
            baseline = np.mean(entropy_values[:5])
            threshold = baseline * 0.7
            self.ax3.axhline(y=threshold, color='r', linestyle='--', 
                           label=f'Threshold (70% of baseline)', alpha=0.7)
            self.ax3.legend()
        
        # Update subplot 4: Top-k mass
        self.ax4.clear()
        self.ax4.set_title('TCDB: Top-k Gram Mass', fontweight='bold')
        self.ax4.set_xlabel('Time Step')
        self.ax4.set_ylabel('Top-k Mass')
        self.ax4.set_ylim(0, 1)
        self.ax4.grid(True, alpha=0.3)
        
        mass_values = [r['topk_mass'] for r in self.tcdb_results]
        self.ax4.plot(range(len(mass_values)), mass_values, 'm-', linewidth=2)
        self.ax4.scatter(frame, analysis['topk_mass'], c='red', s=100, zorder=5)
        
        # Add baseline threshold
        if len(mass_values) >= 5:
            baseline = np.mean(mass_values[:5])
            threshold = baseline + 0.15
            self.ax4.axhline(y=threshold, color='r', linestyle='--', 
                           label=f'Threshold (baseline + 0.15)', alpha=0.7)
            self.ax4.legend()
        
        # Update subplot 5: Baseline magnetization
        self.ax5.clear()
        self.ax5.set_title('Baseline: Magnetization (Kaggle)', fontweight='bold')
        self.ax5.set_xlabel('Time Step')
        self.ax5.set_ylabel('Magnetization')
        self.ax5.grid(True, alpha=0.3)
        
        self.ax5.plot(range(len(self.baseline_results)), self.baseline_results, 
                     'c-', linewidth=2)
        self.ax5.scatter(frame, analysis['magnetization'], c='red', s=100, zorder=5)
        
        # Update subplot 6: Detection status
        self.ax6.clear()
        self.ax6.set_title('Detection Status', fontweight='bold')
        self.ax6.set_xlim(0, 1)
        self.ax6.set_ylim(0, 1)
        self.ax6.axis('off')
        
        # Show detection status
        status_text = f"Time Step: {frame}/{self.n_steps-1}\n\n"
        status_text += f"Sync: {event['sync']:.3f}\n\n"
        status_text += f"TCDB Detection: {'🚨 SWARM!' if analysis['flag'] else '✅ Normal'}\n"
        status_text += f"  Entropy: {analysis['entropy']:.3f}\n"
        status_text += f"  Mass: {analysis['topk_mass']:.3f}\n\n"
        status_text += f"Baseline: {analysis['magnetization']:.4f}"
        
        self.ax6.text(0.5, 0.5, status_text, 
                     ha='center', va='center', fontsize=12,
                     bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
        
        return []
    
    def animate(self, save_gif=False):
        """Run animation."""
        anim = animation.FuncAnimation(
            self.fig, 
            self.update_frame,
            init_func=self.init_animation,
            frames=self.n_steps,
            interval=500,  # 500ms between frames
            blit=False,
            repeat=True
        )
        
        if save_gif:
            output_dir = Path("demo_results")
            output_dir.mkdir(exist_ok=True)
            output_file = output_dir / f"animated_swarm_{self.scenario.lower()}.gif"
            
            print(f"💾 Saving animation to {output_file}...")
            print("   This may take a minute...")
            
            anim.save(str(output_file), writer='pillow', fps=2)
            print(f"✅ Animation saved!")
        else:
            plt.show()


def main():
    parser = argparse.ArgumentParser(description="Animated Swarm Detection Demo")
    parser.add_argument('--scenario', choices=['Legitimate', 'Swarm', 'Mixed'], 
                        default='Swarm', help='Scenario to simulate')
    parser.add_argument('--agents', type=int, default=64, help='Number of agents')
    parser.add_argument('--steps', type=int, default=30, help='Number of time steps')
    parser.add_argument('--animate', action='store_true', 
                        help='Show live animation')
    parser.add_argument('--save-gif', action='store_true', 
                        help='Save animation as GIF')
    
    args = parser.parse_args()
    
    print("=" * 80)
    print("  Animated Swarm Detection Demo")
    print("=" * 80)
    print(f"\nScenario: {args.scenario}")
    print(f"Agents: {args.agents}")
    print(f"Steps: {args.steps}")
    
    if args.save_gif:
        print("\n⚠️  Saving as GIF - this will take 1-2 minutes...")
    else:
        print("\n▶️  Starting live animation...")
    
    demo = AnimatedSwarmDemo(
        scenario=args.scenario,
        n_agents=args.agents,
        n_steps=args.steps
    )
    
    demo.animate(save_gif=args.save_gif)
    
    print("\n✅ Demo complete!")


if __name__ == "__main__":
    main()

