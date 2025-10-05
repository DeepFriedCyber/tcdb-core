from setuptools import setup, find_packages

setup(
    name="tcdb-core",
    version="1.0.0",
    author="DeepFriedCyber",
    description="Topological Data Analysis Core System",
    url="https://github.com/DeepFriedCyber/tcdb-core",
    packages=find_packages(),
    python_requires=">=3.8",
    install_requires=[
        "flask>=2.0.0",
        "gudhi>=3.5.0",
        "numpy>=1.21.0",
        "scikit-learn>=1.0.0",
        "scipy>=1.7.0",
        "requests>=2.26.0",
    ],
    extras_require={
        "dev": [
            "pytest>=7.0.0",
            "pytest-cov>=3.0.0",
        ],
    },
)
