module

/-
# Physical Unified Theory

A formalization of physics toward a unified theory of quantum mechanics and general relativity.

## Structure

- `Foundations`: Mathematical foundations (Track A)
  - `Basic`: Core definitions and physical constants
  - `LinearAlgebra`: Hilbert spaces, operators, spectral theory (A.1)
  - `HilbertSpaces`: Matrix operators, Pauli matrices, unitaries (A.1.2–A.1.3)
  - `Distributions`: Schwartz space, tempered distributions and a rigged Hilbert space (A.1.4–A.1.5)
  - `DifferentialGeometry`: Manifolds, tensors, curvature, causal structure (A.2)
  - `FiberBundles`: Principal bundles, gauge theories (A.2.5)
  - `Algebra`: Lie groups, representations, Clifford algebras (A.4)
  - `MeasureTheory`: Measure spaces, probability, density matrices (A.5)
  - `Topology`: Algebraic topology, topological invariants (A.3)
  - `PDEs`: Elliptic, parabolic, hyperbolic, and geometric PDEs (A.6)
- `QuantumMechanics`: Non-relativistic and relativistic quantum theory
- `GeneralRelativity`: Einstein's theory of gravitation
- `Unification`: Approaches to unifying quantum mechanics and general relativity

## References

- Mathlib: https://github.com/leanprover-community/mathlib4
- PhysLean: https://physlean.com/
-/

-- Track A: Mathematical Foundations
public import PhysicalUnifiedTheory.Foundations.Basic
public import PhysicalUnifiedTheory.Foundations.LinearAlgebra
public import PhysicalUnifiedTheory.Foundations.HilbertSpaces
public import PhysicalUnifiedTheory.Foundations.Distributions
public import PhysicalUnifiedTheory.Foundations.DifferentialGeometry
public import PhysicalUnifiedTheory.Foundations.FiberBundles
public import PhysicalUnifiedTheory.Foundations.Algebra
public import PhysicalUnifiedTheory.Foundations.MeasureTheory
public import PhysicalUnifiedTheory.Foundations.Topology
public import PhysicalUnifiedTheory.Foundations.PDEs

-- Higher tracks (depend on Track A)
public import PhysicalUnifiedTheory.QuantumMechanics.Basic
public import PhysicalUnifiedTheory.QuantumMechanics.Bell
public import PhysicalUnifiedTheory.GeneralRelativity.Basic
public import PhysicalUnifiedTheory.Unification.Basic

-- Track N: Experimental Connections and Predictions
public import PhysicalUnifiedTheory.Experimental.Units
public import PhysicalUnifiedTheory.Experimental.Constants
