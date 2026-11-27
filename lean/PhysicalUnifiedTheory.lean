/-
# Physical Unified Theory

A formalization of physics toward a unified theory of quantum mechanics and general relativity.

## Structure

- `Foundations`: Mathematical foundations (Track A)
  - `Basic`: Core definitions and physical constants
  - `LinearAlgebra`: Hilbert spaces, operators, spectral theory (A.1)
  - `HilbertSpaces`: Matrix operators, Pauli matrices, unitaries (A.1.2–A.1.3)
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
import PhysicalUnifiedTheory.Foundations.Basic
import PhysicalUnifiedTheory.Foundations.LinearAlgebra
import PhysicalUnifiedTheory.Foundations.HilbertSpaces
import PhysicalUnifiedTheory.Foundations.DifferentialGeometry
import PhysicalUnifiedTheory.Foundations.FiberBundles
import PhysicalUnifiedTheory.Foundations.Algebra
import PhysicalUnifiedTheory.Foundations.MeasureTheory
import PhysicalUnifiedTheory.Foundations.Topology
import PhysicalUnifiedTheory.Foundations.PDEs

-- Higher tracks (depend on Track A)
import PhysicalUnifiedTheory.QuantumMechanics.Basic
import PhysicalUnifiedTheory.GeneralRelativity.Basic
import PhysicalUnifiedTheory.Unification.Basic
