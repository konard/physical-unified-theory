# General Relativity: Formalization Guide

This document provides background on Einstein's general relativity for contributors working on the formalization.

## Overview

General relativity (GR) is Einstein's theory of gravitation. Its core insight:

> **Gravity is not a force, but the curvature of spacetime caused by mass and energy.**

Objects in free fall follow geodesics (straightest possible paths) through curved spacetime.

## Key Principles

### 1. Equivalence Principle

Locally, gravitational and inertial effects are indistinguishable:
- A freely falling observer feels no gravity
- An accelerating observer feels an apparent gravitational field

This connects GR to special relativity in local frames.

### 2. General Covariance

The laws of physics are the same in all coordinate systems:
- No preferred reference frame
- Equations must be tensor equations

### 3. Spacetime as a Manifold

Spacetime is a 4-dimensional pseudo-Riemannian manifold:
- Locally looks like Minkowski space
- Globally can have complex topology and curvature

## Mathematical Framework

### Spacetime Manifold

A 4-dimensional smooth manifold M with:
- Lorentzian metric gμν with signature (-,+,+,+)
- Levi-Civita connection (torsion-free, metric-compatible)

Coordinates: xμ = (t, x, y, z) or (x⁰, x¹, x², x³)

### Metric Tensor

The metric gμν defines:
- Distances: ds² = gμν dxμ dxν
- Angles and causality
- Raising/lowering indices: v^μ = g^μν v_ν

Minkowski metric (flat spacetime):
```
η = diag(-1, 1, 1, 1)
ds² = -dt² + dx² + dy² + dz²
```

### Christoffel Symbols

Connection coefficients derived from the metric:
```
Γ^ρ_μν = (1/2) g^ρσ (∂_μ g_νσ + ∂_ν g_μσ - ∂_σ g_μν)
```

Used for covariant derivatives and geodesics.

### Curvature Tensors

**Riemann tensor** measures curvature:
```
R^ρ_σμν = ∂_μ Γ^ρ_νσ - ∂_ν Γ^ρ_μσ + Γ^ρ_μλ Γ^λ_νσ - Γ^ρ_νλ Γ^λ_μσ
```

**Ricci tensor** (contraction):
```
R_μν = R^ρ_μρν
```

**Scalar curvature** (trace):
```
R = g^μν R_μν
```

**Einstein tensor**:
```
G_μν = R_μν - (1/2) R g_μν
```

### Einstein Field Equations

The core equations of GR:
```
G_μν + Λg_μν = (8πG/c⁴) T_μν
```

Or equivalently:
```
R_μν - (1/2) R g_μν + Λg_μν = (8πG/c⁴) T_μν
```

Where:
- G_μν: Einstein tensor (geometry)
- Λ: Cosmological constant
- T_μν: Energy-momentum tensor (matter)

This is a system of 10 coupled, nonlinear PDEs.

### Geodesics

Paths of freely falling particles:
```
d²x^μ/dτ² + Γ^μ_ρσ (dx^ρ/dτ)(dx^σ/dτ) = 0
```

Where τ is proper time.

## Key Solutions

### Minkowski Spacetime
Flat spacetime of special relativity. No gravity.
```
ds² = -dt² + dx² + dy² + dz²
```

### Schwarzschild Solution
Spherically symmetric vacuum solution (non-rotating black hole):
```
ds² = -(1 - 2GM/r)dt² + (1 - 2GM/r)⁻¹dr² + r²dΩ²
```

Features:
- Event horizon at r = 2GM
- Singularity at r = 0

### Kerr Solution
Rotating black hole. More complex metric involving angular momentum.

### FLRW Metric
Cosmological solution for homogeneous, isotropic universe:
```
ds² = -dt² + a(t)²[dr²/(1-kr²) + r²dΩ²]
```

Where a(t) is the scale factor, k is spatial curvature.

## Formalization Strategy

### 1. Special Relativity First

Start with flat spacetime:
- Minkowski metric
- Lorentz transformations
- Four-vectors
- Relativistic mechanics

### 2. Differential Geometry

Use Mathlib's manifold infrastructure:
- `Mathlib.Geometry.Manifold.SmoothManifoldWithCorners`
- `Mathlib.Geometry.Manifold.MFDeriv`

Extend with:
- Pseudo-Riemannian metrics
- Connections and curvature

### 3. Einstein Equations

Build up to:
- Christoffel symbols from metric
- Riemann tensor computation
- Ricci tensor and scalar
- Einstein tensor
- Matter coupling

### 4. Specific Solutions

Verify known solutions:
- Schwarzschild satisfies vacuum equations
- FLRW satisfies equations with perfect fluid

## Formalization Challenges

### 1. Coordinate Dependence

Physics is coordinate-free; calculations often use coordinates:
- Need both coordinate and abstract formulations
- See [Index Notation in Lean](https://arxiv.org/abs/2411.07667)

### 2. Tensor Calculus

Einstein summation convention is pervasive:
- Implicit sums over repeated indices
- Formalization needs explicit handling

### 3. Global Structure

Full GR requires global analysis:
- Causal structure
- Singularities and geodesic incompleteness
- Penrose diagrams

### 4. Initial Value Problem

ADM formalism for evolution:
- 3+1 decomposition of spacetime
- Constraint equations
- Evolution equations

## Resources

### Textbooks
- Wald, "General Relativity"
- Misner, Thorne, Wheeler, "Gravitation"
- Carroll, "Spacetime and Geometry"

### Mathlib Resources
- [Smooth Manifolds](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/SmoothManifoldWithCorners.html)
- [Elements of Differential Geometry in Lean](https://arxiv.org/abs/2108.00484)

### Related Work
- [PhysLean](https://physlean.com/) - Special relativity formalization
- [Formalization of index notation](https://arxiv.org/abs/2411.07667)

## Getting Started

1. Study Mathlib's manifold infrastructure
2. Understand how metrics are represented
3. Start with Minkowski spacetime (explicit coordinates)
4. Prove basic properties (interval invariance, Lorentz transformation)
5. Gradually build toward curved spacetime

See the `lean/PhysicalUnifiedTheory/GeneralRelativity/` directory for our implementations.
