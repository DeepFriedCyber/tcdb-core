"""
Configuration management for descriptors
"""

import yaml
from pathlib import Path
from typing import Dict, Any, Optional


class DescriptorConfig:
    """
    Configuration manager for descriptor modules.
    """
    
    def __init__(self, config_path: Optional[str] = None):
        """
        Initialize configuration.
        
        Args:
            config_path: Path to YAML config file (uses default if None)
        """
        if config_path is None:
            # Use default config
            config_path = Path(__file__).parent / 'descriptor_defaults.yaml'
        
        self.config_path = Path(config_path)
        self.config = self._load_config()
    
    def _load_config(self) -> Dict[str, Any]:
        """Load configuration from YAML file."""
        if not self.config_path.exists():
            raise FileNotFoundError(f"Config file not found: {self.config_path}")
        
        with open(self.config_path, 'r') as f:
            return yaml.safe_load(f)
    
    def get(self, descriptor_name: str) -> Dict[str, Any]:
        """
        Get configuration for a specific descriptor.
        
        Args:
            descriptor_name: Name of descriptor ('tid', 'dgd', 'kme_delta', 'gser')
            
        Returns:
            Configuration dictionary
        """
        if descriptor_name not in self.config:
            raise KeyError(f"No configuration for descriptor: {descriptor_name}")
        
        return self.config[descriptor_name].copy()
    
    def get_common(self) -> Dict[str, Any]:
        """Get common configuration settings."""
        return self.config.get('common', {}).copy()
    
    def get_api(self) -> Dict[str, Any]:
        """Get API configuration settings."""
        return self.config.get('api', {}).copy()
    
    def update(self, descriptor_name: str, updates: Dict[str, Any]) -> None:
        """
        Update configuration for a descriptor.
        
        Args:
            descriptor_name: Name of descriptor
            updates: Dictionary of updates
        """
        if descriptor_name not in self.config:
            self.config[descriptor_name] = {}
        
        self.config[descriptor_name].update(updates)
    
    def save(self, output_path: Optional[str] = None) -> None:
        """
        Save configuration to YAML file.
        
        Args:
            output_path: Output path (overwrites current if None)
        """
        if output_path is None:
            output_path = self.config_path
        
        with open(output_path, 'w') as f:
            yaml.dump(self.config, f, default_flow_style=False)


# Global config instance
_default_config = None


def get_default_config() -> DescriptorConfig:
    """Get the default configuration instance."""
    global _default_config
    if _default_config is None:
        _default_config = DescriptorConfig()
    return _default_config


def load_config(config_path: str) -> DescriptorConfig:
    """
    Load configuration from file.
    
    Args:
        config_path: Path to YAML config file
        
    Returns:
        DescriptorConfig instance
    """
    return DescriptorConfig(config_path)

