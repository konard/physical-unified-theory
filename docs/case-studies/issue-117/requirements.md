# Requirements and verification for issue 117

The [repository requirements register](../../REQUIREMENTS.md) tracks the
current delivery status of these original requirements.

[Issue 117](https://github.com/konard/physical-unified-theory/issues/117) requires
all 102 listed issues to be fully implemented in [PR 118](https://github.com/konard/physical-unified-theory/pull/118).
Its body and the recursive GitHub sub-issue tree reach the same 102 issues.
The tree has 20 direct children and 82 nested children. The issue bodies define
415 distinct task rows and 41 explicitly labeled hypotheses. The issue and its
children had no conversation comments during the initial audit. The pull
request had no conversation comments, inline review comments or reviews when
the audit began.

The parent asks for one pull request, one positive closing keyword per required
issue and a statement in the PR description for any already resolved or
unreproducible issue. The scope is open until its task rows have implementation
and verification evidence. The proposed checks below describe acceptance work.
Current implementation evidence and research limits are in the
[status and sources](status.md).

Issues with task tables retain the original task identifiers. The separate
[track plans](../../../plan/README.md) give the original execution order and
the [dependency graph](../../../plan/DEPENDENCIES.md) shows cross-track
prerequisites.

### A.1: Linear Algebra and Functional Analysis ([#28](https://github.com/konard/physical-unified-theory/issues/28))

Use Mathlib Hilbert spaces, bounded maps, spectra and Schwartz space. Add densely defined operators and explicit continuous dense embeddings for Gelfand triples.

**Verification.** Check self-adjoint real expectations and the spectral theorem in its stated scope, then instantiate a Schwartz–L²–tempered-distribution triple.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| A.1.1 | Hilbert space definitions and basic properties | **Critical** | — |
| A.1.2 | Bounded and unbounded operators | **Critical** | — |
| A.1.3 | Spectral theory (spectral theorem, functional calculus) | High | — |
| A.1.4 | Distribution theory (Schwartz space, tempered distributions) | Medium | — |
| A.1.5 | Rigged Hilbert spaces (Gelfand triples) | Medium | — |

**Lean Directory.** `Foundations/LinearAlgebra.lean`, `Foundations/HilbertSpaces.lean`, `Foundations/Distributions.lean`

**Mathlib Status.** Partial (InnerProductSpace available)

**Hypothesis.** Rigged Hilbert spaces resolve continuous spectrum issues in QM (see Track C).

- Track B, C, E, F, H, I, K, L, N all depend on A.1

### A.2: Differential Geometry ([#29](https://github.com/konard/physical-unified-theory/issues/29))

Reuse Mathlib manifolds and vector bundles, then define connections and Lorentzian fields with chart compatibility.

**Verification.** Verify tensor change-of-basis laws, curvature contractions, bundle actions and the Minkowski zero-curvature case.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| A.2.1 | Smooth manifolds and tangent bundles | **Critical** | — |
| A.2.2 | Tensor fields and tensor calculus | **Critical** | — |
| A.2.3 | Connections and covariant derivatives | High | — |
| A.2.4 | Curvature (Riemann, Ricci, scalar) | High | — |
| A.2.5 | Fiber bundles (principal, associated, vector) | High | — |
| A.2.6 | Lorentzian geometry and causal structure | High | — |

**Lean Directory.** `Foundations/DifferentialGeometry.lean`, `Foundations/FiberBundles.lean`

**Hypothesis.** Fiber bundle theory provides a unified framework for gauge theories and GR.

- Track B, D, E, K, L depend on A.2

### A.3: Topology ([#30](https://github.com/konard/physical-unified-theory/issues/30))

Use Mathlib fundamental groups and singular homology where available and construct the characteristic classes from bundle cohomology or Chern–Weil representatives.

**Verification.** Compute circle and sphere examples, prove homotopy invariance in the chosen model and verify a nontrivial Chern or Pontryagin pairing.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| A.3.1 | Topological spaces and continuity (Mathlib available) | Medium | — |
| A.3.2 | Algebraic topology (fundamental group, homology) | Medium | — |
| A.3.3 | Topological invariants relevant to physics (Chern, Pontryagin) | Medium | — |

### A.4: Algebra ([#31](https://github.com/konard/physical-unified-theory/issues/31))

Use Mathlib Lie, Clifford and category APIs. Add group representations with explicit group actions and bridge them to Lie-algebra representations.

**Verification.** Verify spin representations, Clifford relations and universal properties, and check shared category interfaces used by L.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| A.4.1 | Lie groups and Lie algebras | **Critical** | — |
| A.4.2 | Representation theory | High | — |
| A.4.3 | Clifford algebras and spinors | High | — |
| A.4.4 | Category theory foundations | Medium | — |

**Hypothesis.** C*-algebras provide the correct mathematical framework for QM (see Track L).

- Track E, I, K, L depend on A.4

### A.5: Measure Theory and Probability ([#32](https://github.com/konard/physical-unified-theory/issues/32))

Use measure and probability spaces, filtration and process infrastructure. For path integration, prove a Gaussian or Euclidean construction under explicit hypotheses and state the 4D interacting claim precisely.

**Verification.** Check normalization, finite-dimensional marginals and stochastic examples. Record the regularization, convergence mode and validity limits of path measures.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| A.5.1 | Measure spaces and integration (Mathlib available) | **Critical** | — |
| A.5.2 | Probability theory foundations | High | — |
| A.5.3 | Functional integration (path integrals) | High | — |
| A.5.4 | Stochastic processes | Medium | — |

**Hypothesis.** Rigorous path integrals can be constructed in 4D via constructive QFT methods (see Track E).

- Track C, E, F depend on A.5

### A.6: Partial Differential Equations ([#33](https://github.com/konard/physical-unified-theory/issues/33))

Formalize principal symbols and weak or classical solutions in named function spaces. Reuse Mathlib differential and integral primitives for nonlinear and geometric flows.

**Verification.** Verify Poisson, heat and wave examples, then compute Ricci and Yang–Mills flow on controlled ansätze and state existence conditions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| A.6.1 | Linear PDEs (elliptic, parabolic, hyperbolic) | High | — |
| A.6.2 | Nonlinear PDEs | Medium | — |
| A.6.3 | Geometric PDEs (Ricci flow, Yang-Mills flow) | Medium | — |

- Track D depends on A.6

### Track B: Classical Physics ([#14](https://github.com/konard/physical-unified-theory/issues/14))

Use one smooth configuration and phase-space model across Newtonian, variational and symplectic mechanics, with field theory sharing the variational primitives.

**Verification.** Derive the same harmonic oscillator flow in B.1–B.4, match gauge invariance across B.5–B.6, and use consistent thermodynamic variables in B.7–B.8.

The associated requirement sets are [#34](https://github.com/konard/physical-unified-theory/issues/34), [#35](https://github.com/konard/physical-unified-theory/issues/35), [#36](https://github.com/konard/physical-unified-theory/issues/36), [#37](https://github.com/konard/physical-unified-theory/issues/37), [#38](https://github.com/konard/physical-unified-theory/issues/38), [#39](https://github.com/konard/physical-unified-theory/issues/39), [#40](https://github.com/konard/physical-unified-theory/issues/40), [#41](https://github.com/konard/physical-unified-theory/issues/41).

**Dependencies.** Track A (A.1, A.2).

### Track C: Quantum Mechanics ([#15](https://github.com/konard/physical-unified-theory/issues/15))

Use Mathlib Hilbert spaces and a shared domain-aware operator API. Where exact solutions need unbounded operators, start from explicit dense cores and prove the required closures.

**Verification.** Check consistency across the five postulates, spectral examples, tensor products, channels and Fock spaces. Require convergence hypotheses at scattering and path-integral boundaries.

The associated requirement sets are [#42](https://github.com/konard/physical-unified-theory/issues/42), [#43](https://github.com/konard/physical-unified-theory/issues/43), [#44](https://github.com/konard/physical-unified-theory/issues/44), [#45](https://github.com/konard/physical-unified-theory/issues/45), [#46](https://github.com/konard/physical-unified-theory/issues/46), [#47](https://github.com/konard/physical-unified-theory/issues/47), [#48](https://github.com/konard/physical-unified-theory/issues/48), [#49](https://github.com/konard/physical-unified-theory/issues/49), [#50](https://github.com/konard/physical-unified-theory/issues/50), [#51](https://github.com/konard/physical-unified-theory/issues/51).

**Dependencies.** Track A (A.1, A.5).

### Track D: General Relativity ([#16](https://github.com/konard/physical-unified-theory/issues/16))

Build Lorentzian metrics and connections once and derive Einstein and ADM equations in compatible conventions.

**Verification.** Check covariance, curvature symmetries, field-equation residuals for exact solutions and a flat limit for waves.

The associated requirement sets are [#52](https://github.com/konard/physical-unified-theory/issues/52), [#53](https://github.com/konard/physical-unified-theory/issues/53), [#54](https://github.com/konard/physical-unified-theory/issues/54), [#55](https://github.com/konard/physical-unified-theory/issues/55), [#56](https://github.com/konard/physical-unified-theory/issues/56), [#57](https://github.com/konard/physical-unified-theory/issues/57), [#58](https://github.com/konard/physical-unified-theory/issues/58), [#59](https://github.com/konard/physical-unified-theory/issues/59), [#60](https://github.com/konard/physical-unified-theory/issues/60).

**Dependencies.** Track A (A.2, A.6), Track B (B.2, B.3).

### Track E: Quantum Field Theory ([#17](https://github.com/konard/physical-unified-theory/issues/17))

Use shared free-field and Fock interfaces, then express each regulated interacting model and its parameter limits.

**Verification.** Check locality or gauge invariance where applicable, power counting, anomaly cancellation and the actual scope of each regulator result.

The associated requirement sets are [#61](https://github.com/konard/physical-unified-theory/issues/61), [#62](https://github.com/konard/physical-unified-theory/issues/62), [#63](https://github.com/konard/physical-unified-theory/issues/63), [#64](https://github.com/konard/physical-unified-theory/issues/64), [#65](https://github.com/konard/physical-unified-theory/issues/65).

**Dependencies.** Track A (A.1–A.5), Track C (C.1, C.9), Track D (D.1).

### Track F: Statistical Mechanics and Thermodynamics ([#18](https://github.com/konard/physical-unified-theory/issues/18))

Use probability spaces and positive trace-one states from A and C. Keep finite statistical models and thermodynamic-limit results connected by explicit limit statements.

**Verification.** Check partition functions in solvable examples, entropy or response identities on their stated domains and the black-hole specialization with Track D.

The associated requirement sets are [#66](https://github.com/konard/physical-unified-theory/issues/66), [#67](https://github.com/konard/physical-unified-theory/issues/67), [#68](https://github.com/konard/physical-unified-theory/issues/68), [#69](https://github.com/konard/physical-unified-theory/issues/69), [#70](https://github.com/konard/physical-unified-theory/issues/70), [#71](https://github.com/konard/physical-unified-theory/issues/71), [#72](https://github.com/konard/physical-unified-theory/issues/72).

**Dependencies.** Track A (A.1, A.5), Track B (B.7), Track C (C.1).

### Track G: Cosmology and Astrophysics ([#19](https://github.com/konard/physical-unified-theory/issues/19))

Derive FLRW dynamics from Track D with a closed matter model, then layer on perturbations and observed-data likelihoods.

**Verification.** Reproduce exact Friedmann solutions, verify scale-factor and sign conventions and trace every reported observational bound to its likelihood and release.

The associated requirement sets are [#73](https://github.com/konard/physical-unified-theory/issues/73), [#74](https://github.com/konard/physical-unified-theory/issues/74), [#75](https://github.com/konard/physical-unified-theory/issues/75), [#76](https://github.com/konard/physical-unified-theory/issues/76), [#77](https://github.com/konard/physical-unified-theory/issues/77).

**Dependencies.** Track D (D.3, D.4), Track E (E.4), Track F (F.1).

### Track H: Quantum Information and Computation ([#20](https://github.com/konard/physical-unified-theory/issues/20))

Share the circuit model across algorithms, error correction and protocols. Evaluate CoqQ and SQIR for reusable small circuits and source-level proofs.

**Verification.** Check gate and register semantics, algorithm success bounds, channel laws and security assumptions, including the adversary model.

The associated requirement sets are [#78](https://github.com/konard/physical-unified-theory/issues/78), [#79](https://github.com/konard/physical-unified-theory/issues/79), [#80](https://github.com/konard/physical-unified-theory/issues/80), [#81](https://github.com/konard/physical-unified-theory/issues/81), [#82](https://github.com/konard/physical-unified-theory/issues/82), [#83](https://github.com/konard/physical-unified-theory/issues/83).

**Dependencies.** Track A (A.1), Track C (C.1, C.6, C.7).

### Track I: Condensed Matter and Many-Body Physics ([#21](https://github.com/konard/physical-unified-theory/issues/21))

Reuse the statistics and Fock APIs for paired particles, lattice Hamiltonians and tensor networks.

**Verification.** Use exactly diagonalizable lattices, bond-dimension-one states and limiting cases of the effective models as checks.

The associated requirement sets are [#84](https://github.com/konard/physical-unified-theory/issues/84), [#85](https://github.com/konard/physical-unified-theory/issues/85), [#86](https://github.com/konard/physical-unified-theory/issues/86), [#87](https://github.com/konard/physical-unified-theory/issues/87), [#88](https://github.com/konard/physical-unified-theory/issues/88), [#89](https://github.com/konard/physical-unified-theory/issues/89).

**Dependencies.** Track A (A.1, A.4), Track C (C.9), Track F (F.2, F.3).

### Track J: Particle Physics Phenomenology ([#22](https://github.com/konard/physical-unified-theory/issues/22))

Build particle models on a single Standard Model schema with CKM and PMNS conventions. Use explicit matching scales and reference data for phenomenology.

**Verification.** Check decoupling limits, mixing identities and experimental comparisons with stated uncertainties and assumptions.

The associated requirement sets are [#90](https://github.com/konard/physical-unified-theory/issues/90), [#91](https://github.com/konard/physical-unified-theory/issues/91), [#92](https://github.com/konard/physical-unified-theory/issues/92), [#93](https://github.com/konard/physical-unified-theory/issues/93), [#94](https://github.com/konard/physical-unified-theory/issues/94).

**Dependencies.** Track E (E.3, E.4).

### Track K: Approaches to Quantum Gravity ([#23](https://github.com/konard/physical-unified-theory/issues/23))

Express incompatibilities under explicit assumptions. Encode quantum-gravity candidates on common observables and formalize open predictions as proposition-valued statements.

**Verification.** Prove known consequences from candidate assumptions, check recovery of classical or semiclassical limits where established and identify the scope of unresolved claims.

The associated requirement sets are [#95](https://github.com/konard/physical-unified-theory/issues/95), [#96](https://github.com/konard/physical-unified-theory/issues/96), [#97](https://github.com/konard/physical-unified-theory/issues/97), [#98](https://github.com/konard/physical-unified-theory/issues/98), [#99](https://github.com/konard/physical-unified-theory/issues/99).

**Dependencies.** Track A (all), Track C (C.1), Track D (D.3, D.5, D.6), Track E (E.1–E.3).

### Track L: Mathematical Physics and Structural Approaches ([#24](https://github.com/konard/physical-unified-theory/issues/24))

Reuse operator algebra, category theory and topology interfaces. Instantiate abstract quantum field and quantization axioms on verified examples.

**Verification.** Check morphism, locality and composition laws, then verify invariants in simple spaces and reconcile duplicated structures with other tracks.

The associated requirement sets are [#100](https://github.com/konard/physical-unified-theory/issues/100), [#101](https://github.com/konard/physical-unified-theory/issues/101), [#102](https://github.com/konard/physical-unified-theory/issues/102), [#103](https://github.com/konard/physical-unified-theory/issues/103).

**Dependencies.** Track A (all), Track C (C.1), Track D (D.3), Track E (E.1, E.3).

### Track M: Hypotheses and Speculative Directions ([#25](https://github.com/konard/physical-unified-theory/issues/25))

State separate precise conjectures for speculative proposals with cited assumptions and well-defined observables.

**Verification.** Check types and consistency of the formulations, prove conditional consequences and document the missing evidence for each empirical or mathematical claim.

The associated requirement sets are [#104](https://github.com/konard/physical-unified-theory/issues/104), [#105](https://github.com/konard/physical-unified-theory/issues/105), [#106](https://github.com/konard/physical-unified-theory/issues/106), [#107](https://github.com/konard/physical-unified-theory/issues/107).

**Dependencies.** All tracks inform M (cross-cutting).

The track asks for precise formal conjectures for its speculative directions.

### Track N: Experimental Connections and Predictions ([#26](https://github.com/konard/physical-unified-theory/issues/26))

Use dimension-indexed quantities and provenance-bearing observations, then restate published likelihoods and theory predictions in the same dimension system.

**Verification.** Check conversion laws and constants first, then reproduce representative published central values, bounds, error bars and domain assumptions.

The associated requirement sets are [#108](https://github.com/konard/physical-unified-theory/issues/108), [#109](https://github.com/konard/physical-unified-theory/issues/109), [#110](https://github.com/konard/physical-unified-theory/issues/110), [#111](https://github.com/konard/physical-unified-theory/issues/111).

**Dependencies.** Track A (A.1); various physics tracks for later items.

### Track O: Foundations and Philosophy of Physics ([#27](https://github.com/konard/physical-unified-theory/issues/27))

Define interpretations, operational theories and ontological models on shared QM and GR primitives. State distinct empirical and philosophical assumptions explicitly.

**Verification.** Prove finite reconstruction and impossibility results where applicable, then check each comparison against its assumptions and observations.

The associated requirement sets are [#112](https://github.com/konard/physical-unified-theory/issues/112), [#113](https://github.com/konard/physical-unified-theory/issues/113), [#114](https://github.com/konard/physical-unified-theory/issues/114), [#115](https://github.com/konard/physical-unified-theory/issues/115).

**Dependencies.** Track C (C.1, C.6), Track D (D.1, D.5).

### B.1: Newtonian Mechanics ([#34](https://github.com/konard/physical-unified-theory/issues/34))

Define Newtonian trajectories with position and velocity derivatives, additive interactions and central forces.

**Verification.** Derive conservation of energy and both momenta under their stated hypotheses and verify radial force in the two-body reduction.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| B.1.1 | Newton's laws as axioms | High | — |
| B.1.2 | Conservation laws (energy, momentum, angular momentum) | High | — |
| B.1.3 | Central force problems | Medium | — |

**Upstream.** Requires A.1 (linear algebra), A.2 (differential geometry)

### B.2: Lagrangian Mechanics ([#35](https://github.com/konard/physical-unified-theory/issues/35))

Define admissible fixed-endpoint variations. Use a first-variation result and integration by parts for Euler–Lagrange, then prove Noether under infinitesimal invariance. Model holonomic constraints by multipliers.

**Verification.** Check free-particle and oscillator actions and derive energy conservation from time translation.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| B.2.1 | Principle of least action | **Critical** | — |
| B.2.2 | Euler-Lagrange equations | **Critical** | — |
| B.2.3 | Noether's theorem | **Critical** | — |
| B.2.4 | Constrained systems | Medium | — |

**Key output.** B.2.1–B.2.3 are required by Track D (Einstein-Hilbert action).

### B.3: Hamiltonian Mechanics ([#36](https://github.com/konard/physical-unified-theory/issues/36))

Define the fibre derivative and require its local inverse for the Legendre transformation. Derive Hamilton equations, canonical maps and the Hamilton–Jacobi condition.

**Verification.** Verify the regular oscillator transform, its symplectic flow and an explicit complete integral.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| B.3.1 | Legendre transform and Hamilton's equations | **Critical** | — |
| B.3.2 | Canonical transformations | High | — |
| B.3.3 | Hamilton-Jacobi theory | Medium | — |

**Key output.** B.3.1 is required by Track D (ADM formalism).

### B.4: Symplectic Geometry ([#37](https://github.com/konard/physical-unified-theory/issues/37))

Define closed nondegenerate two-forms, their Poisson bracket and the symplectic volume form. Use pullbacks and Cartan's identity.

**Verification.** Check antisymmetry, Jacobi, Liouville preservation and the prequantization integrality prerequisite on a canonical cotangent example.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| B.4.1 | Symplectic manifolds and Poisson brackets | High | — |
| B.4.2 | Liouville's theorem | High | — |
| B.4.3 | Geometric quantization connection | Medium | — |

**Hypothesis.** Geometric quantization provides a rigorous path from classical to quantum (see Track L).

### B.5: Classical Electromagnetism ([#38](https://github.com/konard/physical-unified-theory/issues/38))

Use a 1-form potential and 2-form curvature, Hodge star and Maxwell equations on a Lorentzian manifold.

**Verification.** Prove gauge invariance using d² = 0 and derive on-shell stress-energy divergence with compatible source conventions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| B.5.1 | Maxwell's equations in differential form | High | — |
| B.5.2 | Gauge invariance (U(1)) | High | — |
| B.5.3 | Electromagnetic energy-momentum tensor | High | — |

### B.6: Classical Field Theory ([#39](https://github.com/konard/physical-unified-theory/issues/39))

Define local Lagrangian densities and variation with support conditions. Derive field equations and Noether currents on shared tensor infrastructure.

**Verification.** Recover the scalar wave equation and check the canonical stress-energy and current identities on solutions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| B.6.1 | Field Lagrangian and Euler-Lagrange for fields | High | — |
| B.6.2 | Noether's theorem for fields | High | — |
| B.6.3 | Energy-momentum tensor | High | — |

### B.7: Classical Thermodynamics ([#40](https://github.com/konard/physical-unified-theory/issues/40))

Model equilibrium state variables and paths, heat and work sign conventions and thermodynamic Legendre transforms.

**Verification.** Verify each law at its stated scope, identities for ideal-gas potentials and equality of chemical potentials at phase coexistence.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| B.7.1 | Laws of thermodynamics (0th through 3rd) | High | — |
| B.7.2 | Thermodynamic potentials | Medium | — |
| B.7.3 | Phase equilibria | Medium | — |

**Key output.** B.7.1 is required by Track F (Statistical Mechanics).

### B.8–B.9: Fluid Mechanics and Nonlinear Dynamics ([#41](https://github.com/konard/physical-unified-theory/issues/41))

Define stress and transport fields on fluid state spaces, including relativistic conservation. Formalize a canonical Hamiltonian flow and KAM hypotheses through the required dynamical-systems infrastructure.

**Verification.** Check the incompressible linear limit, a relativistic perfect-fluid reduction and an integrable invariant torus.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| B.8.1 | Navier-Stokes equations | Medium | — |
| B.8.2 | Relativistic fluid dynamics | Medium | — |
| B.9.1 | Hamiltonian chaos and KAM theory | Low | — |

### C.1: Fundamental Postulates of Quantum Mechanics ([#42](https://github.com/konard/physical-unified-theory/issues/42))

Use normalized vectors and positive trace-one density operators, self-adjoint observables, projection-valued measures, unitary evolution and tensor products.

**Verification.** Verify Born normalization, Lüders projection for positive-probability outcomes, Schrödinger evolution under stated generator assumptions and a two-system product state.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| C.1.1 | State space axiom (Hilbert space, density operators) | **Critical** | — |
| C.1.2 | Observable axiom (self-adjoint operators) | **Critical** | — |
| C.1.3 | Measurement axiom (Born rule, projection postulate) | **Critical** | — |
| C.1.4 | Time evolution (Schrödinger equation, unitary evolution) | **Critical** | — |
| C.1.5 | Composite systems (tensor products) | **Critical** | — |

**Key output.** C.1 is the most widely depended-upon deliverable in the entire project.

### C.2: Exactly Solvable Quantum Systems ([#43](https://github.com/konard/physical-unified-theory/issues/43))

Model qubits and spin with finite matrices. Use dense operator cores and the appropriate boundary conditions for oscillator, hydrogen and well eigenproblems.

**Verification.** Check spectrum and eigenfunction normalization, ladder actions, commutators and degeneracies.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| C.2.1 | Finite-dimensional systems (spin-1/2, qubits) | **Critical** | — |
| C.2.2 | Quantum harmonic oscillator (creation/annihilation operators) | **Critical** | — |
| C.2.3 | Hydrogen atom (Coulomb problem) | High | — |
| C.2.4 | Particle in a box and other 1D problems | High | — |
| C.2.5 | Angular momentum and spin | High | — |

### C.3: Symmetries in Quantum Mechanics ([#44](https://github.com/konard/physical-unified-theory/issues/44))

Define symmetry on rays and transition probabilities. Connect rotation lifts and generators to unitary representations and time reversal to antiunitary maps.

**Verification.** Check the two branches of Wigner's theorem and verify rotations, translations and time reversal on concrete spin or wavefunction models.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| C.3.1 | Wigner's theorem (symmetries as unitary/antiunitary operators) | High | — |
| C.3.2 | Rotation group SO(3) and SU(2) representations | High | — |
| C.3.3 | Translation symmetry and momentum | High | — |
| C.3.4 | Time-reversal symmetry | Medium | — |

**Hypothesis.** Superselection structure is determined by symmetry groups.

### C.4: Approximation Methods ([#45](https://github.com/konard/physical-unified-theory/issues/45))

Build perturbation expansions with remainder bounds, a variational spectral bound, and semiclassical and adiabatic approximation theorems.

**Verification.** Check nondegenerate and degenerate examples, verify a golden-rule limit, and isolate WKB turning-point and adiabatic gap conditions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| C.4.1 | Time-independent perturbation theory | High | — |
| C.4.2 | Time-dependent perturbation theory (Fermi's golden rule) | High | — |
| C.4.3 | Variational method | Medium | — |
| C.4.4 | WKB approximation | Medium | — |
| C.4.5 | Adiabatic theorem and Berry phase | Medium | — |

### C.5: Scattering Theory ([#46](https://github.com/konard/physical-unified-theory/issues/46))

Define wave operators and the S and T operators under scattering hypotheses, then derive Born and partial-wave formulas.

**Verification.** Verify unitarity on complete scattering subspaces, the free limit and a central-potential expansion.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| C.5.1 | S-matrix and T-matrix | High | — |
| C.5.2 | Born approximation | Medium | — |
| C.5.3 | Partial wave analysis | Medium | — |

### C.6: Composite Systems and Entanglement ([#47](https://github.com/konard/physical-unified-theory/issues/47))

Reuse tensor-product and matrix operations for Schmidt decomposition, partial trace and Bell correlators.

**Verification.** Check a product state, Bell-state marginals, the local bound and a quantum violation and evaluate selected entanglement measures.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| C.6.1 | Tensor product spaces | **Critical** | — |
| C.6.2 | Entanglement (Bell states, Schmidt decomposition) | **Critical** | — |
| C.6.3 | Bell inequalities and non-locality | High | — |
| C.6.4 | Entanglement measures | Medium | — |

**Key output.** C.6 is required by Track H (Quantum Information) and Track O (Foundations).

**Hypothesis.** Entanglement is fundamental to spacetime emergence (see Track K, Track M).

### C.7: Open Quantum Systems ([#48](https://github.com/konard/physical-unified-theory/issues/48))

Use the shared density operator, complete positivity and Kraus maps. Derive a finite-dimensional Lindblad semigroup and explicit decoherence channels.

**Verification.** Prove trace preservation and complete positivity, and check dephasing and its composition law.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| C.7.1 | Density matrices and mixed states | High | — |
| C.7.2 | Quantum channels (CPTP maps) | High | — |
| C.7.3 | Lindblad master equation | High | — |
| C.7.4 | Decoherence | Medium | — |

### C.8: Path Integral Formulation ([#49](https://github.com/konard/physical-unified-theory/issues/49))

Formalize time slicing and a Trotter limit for admissible potentials. Use analytic continuation only under stated hypotheses.

**Verification.** Match the free propagator and at least one interacting operator evolution, with a precise interpretation of the integral and limit.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| C.8.1 | Feynman path integral (non-relativistic) | Medium | — |
| C.8.2 | Connection to operator formalism | Medium | — |

### C.9: Second Quantization ([#50](https://github.com/konard/physical-unified-theory/issues/50))

Construct graded Hilbert direct sums of symmetric or antisymmetric powers and define ladder operators on finite-particle domains.

**Verification.** Check vacuum, number operator, adjointness and both canonical commutation and anticommutation relations.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| C.9.1 | Fock space construction | **Critical** | — |
| C.9.2 | Creation and annihilation operators | **Critical** | — |
| C.9.3 | Bosonic and fermionic statistics | **Critical** | — |

**Key output.** C.9 is required by Track E (QFT) and Track I (Condensed Matter).

### C.10: Quantum Chaos ([#51](https://github.com/konard/physical-unified-theory/issues/51))

Define the relevant random-matrix ensembles and normalized level-spacing statistics, with deterministic reference computations.

**Verification.** Check Hermiticity, symmetry class, normalization and the scope of level statistics in a finite ensemble.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| C.10.1 | Random matrix theory | Low | — |
| C.10.2 | Level statistics | Low | — |

### D.1: Special Relativity ([#52](https://github.com/konard/physical-unified-theory/issues/52))

Use one signature and shared four-vector model. Represent Lorentz transformations as linear Minkowski isometries and connect boosts to energy–momentum.

**Verification.** Prove interval invariance and group laws, recover velocity addition and verify the rest and massless dispersion cases.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| D.1.1 | Minkowski spacetime and metric | **Critical** | — |
| D.1.2 | Lorentz transformations and Lorentz group | **Critical** | — |
| D.1.3 | Four-vectors and relativistic kinematics | **Critical** | — |
| D.1.4 | Relativistic energy-momentum | High | — |

**Key output.** D.1 is required by Track E (relativistic QFT).

### D.2: Differential Geometry for GR ([#53](https://github.com/konard/physical-unified-theory/issues/53))

Use smooth bilinear metric fields and derive Levi-Civita using metric compatibility and torsion freedom. Build curvature and its traces from that connection.

**Verification.** Verify connection uniqueness, geodesic covariance, Riemann symmetries and Ricci contractions in a flat chart and curved example.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| D.2.1 | Pseudo-Riemannian manifolds | **Critical** | — |
| D.2.2 | Levi-Civita connection | **Critical** | — |
| D.2.3 | Geodesic equation | **Critical** | — |
| D.2.4 | Riemann curvature tensor | **Critical** | — |
| D.2.5 | Ricci tensor and scalar curvature | **Critical** | — |

### D.3: Einstein's Field Equations ([#54](https://github.com/konard/physical-unified-theory/issues/54))

Define Einstein and stress-energy tensors on the shared metric and derive the equations through variation with boundary conditions. Specify linearization order.

**Verification.** Check the contracted Bianchi identity, cosmological term, conservation and linear harmonic-gauge reduction.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| D.3.1 | Einstein tensor | **Critical** | — |
| D.3.2 | Stress-energy tensor | **Critical** | — |
| D.3.3 | Einstein field equations (with cosmological constant) | **Critical** | — |
| D.3.4 | Einstein-Hilbert action and variational derivation | High | — |
| D.3.5 | Linearized gravity | High | — |

### D.4: Exact Solutions of Einstein Equations ([#55](https://github.com/konard/physical-unified-theory/issues/55))

Define exact metrics on coordinate regions and explicitly evaluate their Einstein or Einstein–Maxwell residuals.

**Verification.** Check Schwarzschild and Kerr limits, charge reduction, FLRW curvature cases and pp-wave field equations.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| D.4.1 | Schwarzschild solution (static spherically symmetric) | **Critical** | — |
| D.4.2 | Kerr solution (rotating black holes) | High | — |
| D.4.3 | FLRW metric (cosmological) | High | — |
| D.4.4 | Reissner-Nordström (charged black holes) | Medium | — |
| D.4.5 | Gravitational wave solutions (pp-waves) | Medium | — |

**Hypothesis.** Physically reasonable exact solutions follow a unified classification.

### D.5: Singularity Theorems and Causal Structure ([#56](https://github.com/konard/physical-unified-theory/issues/56))

Build causal and conformal structures. Import comparison and focusing results for singularity theorems and write separately scoped censorship conjectures.

**Verification.** Prove the required incompleteness under the appropriate Penrose and Hawking hypotheses and verify a reference conformal compactification.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| D.5.1 | Causal structure (timelike, spacelike, null) | High | — |
| D.5.2 | Penrose-Hawking singularity theorems | High | — |
| D.5.3 | Penrose diagrams (conformal compactification) | Medium | — |
| D.5.4 | Cosmic censorship conjecture | Medium | — |

**Hypothesis.** Cosmic censorship holds — naked singularities do not form from generic initial data.

### D.6: ADM Formalism and Initial Value Problem ([#57](https://github.com/konard/physical-unified-theory/issues/57))

Define lapse, shift, extrinsic curvature and ADM evolution. Connect the constraints to projections of Einstein's equations and harmonic-gauge analysis.

**Verification.** Check constraint propagation and the statement of well-posedness modulo diffeomorphism with its regularity and boundary conditions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| D.6.1 | 3+1 decomposition (lapse, shift, spatial metric) | High | — |
| D.6.2 | ADM Hamiltonian and momentum constraints | High | — |
| D.6.3 | Well-posedness of initial value problem | Medium | — |

**Key output.** D.6 is required by Track K (canonical quantum gravity).

### D.7: Gravitational Waves ([#58](https://github.com/konard/physical-unified-theory/issues/58))

Derive linearized vacuum waves and transverse-traceless polarization from Track D.3. Add a slow-motion source multipole expansion.

**Verification.** Verify the two polarization tensors, their plane-wave solutions and the quadrupole limit for a model binary.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| D.7.1 | Linearized theory and wave equation | High | — |
| D.7.2 | Polarizations (plus and cross) | Medium | — |
| D.7.3 | Energy radiated (quadrupole formula) | Medium | — |

### D.8: Black Hole Physics ([#59](https://github.com/konard/physical-unified-theory/issues/59))

Define global event horizons and local Killing horizons and state the stationary mechanics laws. Couple to a semiclassical radiation model.

**Verification.** Check Schwarzschild surface gravity, temperature and entropy, and first-law and limiting statements for appropriate stationary solutions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| D.8.1 | Event horizons and Killing horizons | High | — |
| D.8.2 | Black hole mechanics (four laws) | High | — |
| D.8.3 | Hawking radiation (semiclassical) | Medium | — |
| D.8.4 | Black hole entropy (Bekenstein-Hawking) | Medium | — |

**Hypothesis.** Black hole mechanics is identical to thermodynamics (see Track F).

### D.9–D.10: Alternative Theories and Numerical Methods ([#60](https://github.com/konard/physical-unified-theory/issues/60))

Define f(R) and Brans–Dicke actions with assumptions on fields. Specify a constrained numerical formulation and discrete convergence or stability criteria.

**Verification.** Recover Einstein gravity in the appropriate limit and verify a small numerical benchmark with an exact solution.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| D.9.1 | f(R) gravity | Low | — |
| D.9.2 | Scalar-tensor theories (Brans-Dicke) | Low | — |
| D.10.1 | Numerical GR foundations | Low | — |

### E.1: Free Field Theory ([#61](https://github.com/konard/physical-unified-theory/issues/61))

Reuse Lorentz representations and Fock space. Model free fields as operator-valued distributions and define Proca and Maxwell with their constraints.

**Verification.** Verify Klein–Gordon and Dirac dispersion, gauge redundancy or Proca transversality, and locality and vacuum two-point identities.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| E.1.1 | Free scalar field (Klein-Gordon equation) | **Critical** | — |
| E.1.2 | Free spinor field (Dirac equation) | **Critical** | — |
| E.1.3 | Free vector field (Proca and Maxwell) | High | — |
| E.1.4 | Canonical quantization of free fields | **Critical** | — |
| E.1.5 | Fock space and particle interpretation | **Critical** | — |

**Hypothesis.** Haag's theorem is resolvable through better understanding of the interaction picture.

### E.2: Interacting Field Theory ([#62](https://github.com/konard/physical-unified-theory/issues/62))

Build finite regulator and expansion interfaces for diagrams, counterterms, RG and lattice or instanton constructions.

**Verification.** Check an explicit loop calculation, beta function and finite lattice result. Record the assumptions required to remove regulators and the open continuum mass-gap claim.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| E.2.1 | Perturbation theory and Feynman diagrams | **Critical** | — |
| E.2.2 | Renormalization (UV divergences, regularization) | **Critical** | — |
| E.2.3 | Renormalization group | High | — |
| E.2.4 | Non-perturbative methods (instantons, lattice) | Medium | — |

**Hypothesis.** Yang-Mills mass gap is solvable via formalization (Millennium Prize).

### E.3: Gauge Theories ([#63](https://github.com/konard/physical-unified-theory/issues/63))

Share bundle connections between Abelian and non-Abelian theories. Formalize BRST, ghost grading and gauge fixing under proper domain assumptions.

**Verification.** Check transformation of curvature, BRST nilpotence and the Faddeev–Popov determinant in a controlled gauge.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| E.3.1 | Abelian gauge theory (QED) | **Critical** | — |
| E.3.2 | Non-Abelian gauge theory (Yang-Mills) | **Critical** | — |
| E.3.3 | BRST symmetry and ghost fields | High | — |
| E.3.4 | Gauge fixing and Faddeev-Popov procedure | High | — |

### E.4: The Standard Model ([#64](https://github.com/konard/physical-unified-theory/issues/64))

Use explicit representation and charge assignments for electroweak and color sectors and model symmetry breaking with a Higgs potential.

**Verification.** Compute the unbroken generator and tree-level masses and prove local anomaly coefficients cancel for a generation.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| E.4.1 | Electroweak theory (SU(2) × U(1)) | High | — |
| E.4.2 | Higgs mechanism and spontaneous symmetry breaking | High | — |
| E.4.3 | QCD (SU(3) color) | High | — |
| E.4.4 | Full Standard Model gauge group SU(3) × SU(2) × U(1) | High | — |
| E.4.5 | Anomaly cancellation | Medium | — |

**Hypothesis.** The Standard Model gauge group is nearly uniquely determined by anomaly cancellation.

### E.5–E.8: Advanced QFT Topics ([#65](https://github.com/konard/physical-unified-theory/issues/65))

Define regularized anomaly and topological charge computations, conformal correlation functions and a scale-indexed EFT expansion.

**Verification.** Check a chiral anomaly coefficient, charge of a topological sector, a Ward identity and cutoff or power-counting errors.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| E.5.1 | Chiral and gauge anomalies | Medium | — |
| E.6.1 | Topological aspects (instantons, monopoles, theta vacuum) | Medium | — |
| E.7.1 | Conformal field theory (2D and higher) | Medium | — |
| E.8.1 | Effective field theory framework | Medium | — |

**Hypothesis.** All QFTs are effective theories, each valid within an energy domain.

### F.1: Foundations of Statistical Mechanics ([#66](https://github.com/konard/physical-unified-theory/issues/66))

Use a common Hamiltonian and phase space to define each ensemble and free energy, then choose a thermodynamic limit with explicit conditions.

**Verification.** Check normalization, a solvable partition sum and equivalence for a well-defined short-range family.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| F.1.1 | Microcanonical, canonical, grand canonical ensembles | **Critical** | — |
| F.1.2 | Partition functions and free energies | **Critical** | — |
| F.1.3 | Equivalence of ensembles in thermodynamic limit | High | — |

### F.2: Quantum Statistical Mechanics ([#67](https://github.com/konard/physical-unified-theory/issues/67))

Use trace-one thermal states, Fock occupations, Bose condensation limits and operator-algebraic KMS dynamics.

**Verification.** Check two-level Gibbs states, Bose/Fermi statistics, a condensation criterion and finite-dimensional KMS equivalence.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| F.2.1 | Density matrix formulation | High | — |
| F.2.2 | Bose-Einstein and Fermi-Dirac statistics | **Critical** | — |
| F.2.3 | Bose-Einstein condensation | High | — |
| F.2.4 | KMS condition for thermal equilibrium | Medium | — |

**Hypothesis.** KMS condition characterizes thermal equilibrium in quantum field theory.

### F.3: Phase Transitions and Critical Phenomena ([#68](https://github.com/konard/physical-unified-theory/issues/68))

Use lattice spin configurations, Landau potentials and scaled couplings to connect microscopic and effective models.

**Verification.** Verify exact finite or transfer-matrix Ising results, critical behavior in a stated limit and stable directions at a fixed point.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| F.3.1 | Ising model and exact solutions | High | — |
| F.3.2 | Landau theory of phase transitions | High | — |
| F.3.3 | Renormalization group for critical phenomena | Medium | — |
| F.3.4 | Universality classes | Medium | — |

**Hypothesis.** Universality in critical phenomena arises from RG fixed points.

### F.4: Entropy and Information ([#69](https://github.com/konard/physical-unified-theory/issues/69))

Use finite probability distributions, density spectra and collision dynamics with explicit zero-probability conventions.

**Verification.** Check Shannon and von Neumann entropy agreement on diagonal states, H-theorem conditions and maximum entropy of a constrained ensemble.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| F.4.1 | Boltzmann entropy and H-theorem | High | — |
| F.4.2 | Von Neumann entropy | High | — |
| F.4.3 | Shannon entropy and connections to physics | Medium | — |
| F.4.4 | Maximum entropy principle | Medium | — |

### F.5: Non-Equilibrium Statistical Mechanics ([#70](https://github.com/konard/physical-unified-theory/issues/70))

Build collision dynamics, time-correlations and work distributions with explicit stochastic or Hamiltonian assumptions.

**Verification.** Check the collision invariants, Kubo and fluctuation-dissipation identities and Jarzynski or Crooks relations on solvable dynamics.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| F.5.1 | Boltzmann equation | Medium | — |
| F.5.2 | Linear response theory (Kubo formula) | Medium | — |
| F.5.3 | Fluctuation-dissipation theorem | Medium | — |
| F.5.4 | Jarzynski equality and Crooks theorem | Low | — |

### F.6: Black Hole Thermodynamics ([#71](https://github.com/konard/physical-unified-theory/issues/71))

Reuse black-hole surface gravity and area laws. Model radiation subsystem entropy and define the Page curve or generalized entropy under explicit assumptions.

**Verification.** Recover stationary Bekenstein–Hawking entropy and verify conditional Page-curve behavior in a specified evaporation model.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| F.6.1 | Four laws of black hole mechanics | High | — |
| F.6.2 | Bekenstein-Hawking entropy | High | — |
| F.6.3 | Information paradox | High | — |
| F.6.4 | Page curve and unitarity | Medium | — |

**Note.** Requires Track D D.8 (black hole physics) — Phase 5 task.

**Hypothesis.** Black hole evaporation is unitary; the Page curve is correct.

### F.7: Thermodynamics of Spacetime ([#72](https://github.com/konard/physical-unified-theory/issues/72))

Model accelerated detector response and local horizon entropy. Formalize the assumptions in Jacobson and Verlinde arguments separately.

**Verification.** Check Unruh temperature and the Einstein-equation derivation under specified local Clausius and horizon assumptions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| F.7.1 | Unruh effect | Medium | — |
| F.7.2 | Jacobson's derivation of Einstein equations from thermodynamics | Medium | — |
| F.7.3 | Verlinde's entropic gravity | Low | — |

**Note.** Requires Track D D.3 — Phase 5 task.

**Hypothesis.** Einstein equations can be derived from thermodynamic relations on local Rindler horizons.

### G.1: Big Bang Cosmology ([#73](https://github.com/konard/physical-unified-theory/issues/73))

Derive Friedmann dynamics and redshift. Use tabulated thermal degrees of freedom and a reaction-network treatment of primordial abundances.

**Verification.** Check matter and radiation limits, Hubble scaling in the low-redshift limit and reproduce abundances within documented inputs.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| G.1.1 | FLRW dynamics (Friedmann equations) | **Critical** | — |
| G.1.2 | Cosmological redshift and Hubble's law | **Critical** | — |
| G.1.3 | Thermal history of the universe | High | — |
| G.1.4 | Big Bang nucleosynthesis | Medium | — |

### G.2: Inflation ([#74](https://github.com/konard/physical-unified-theory/issues/74))

Model a scalar inflaton and gauge-invariant perturbations. Define slow-roll expansions and the stochastic condition for eternal inflation.

**Verification.** Check spectral tilt and tensor predictions on a reference potential and document scale, approximation and prior dependence.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| G.2.1 | Slow-roll inflation (single scalar field) | High | — |
| G.2.2 | Inflationary perturbation theory | High | — |
| G.2.3 | Observational predictions (spectral index, tensor-to-scalar ratio) | High | — |
| G.2.4 | Eternal inflation | Medium | — |

**Hypothesis.** Cosmic inflation occurred and generated primordial perturbations that seeded structure.

### G.3: Dark Matter ([#75](https://github.com/konard/physical-unified-theory/issues/75))

Combine rotation curves or lensing with a CDM perturbation model. Refer WIMP and axion assumptions to J.

**Verification.** Show gravitational evidence via a sourced likelihood or benchmark and keep particle identification parameterized.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| G.3.1 | Evidence and observational constraints | High | — |
| G.3.2 | CDM model and structure formation | High | — |
| G.3.3 | Particle dark matter candidates (links to Track J) | Medium | — |

### G.4: Dark Energy and Cosmological Constant ([#76](https://github.com/konard/physical-unified-theory/issues/76))

Separate vacuum contributions from observed expansion parameters. Define quintessence and general w(z) distances against released likelihoods.

**Verification.** Recover cosmological-constant distances in the w = −1 limit and reproduce a selected SNe, BAO or CMB constraint.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| G.4.1 | Cosmological constant problem | High | — |
| G.4.2 | Dark energy models (quintessence, w(z)) | Medium | — |
| G.4.3 | Observational constraints (SNe Ia, BAO, CMB) | Medium | — |

**Hypothesis.** The cosmological constant problem is the most important unsolved problem in physics.

### G.5–G.9: Advanced Cosmology ([#77](https://github.com/konard/physical-unified-theory/issues/77))

Build specialized perturbation, early-universe, black-hole and minisuperspace models over shared G.1 and K primitives.

**Verification.** Check primordial tensor transfer, baryon-production assumptions, structure growth, boundary proposals and explicit cyclic or bouncing solutions where established.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| G.5.1 | Primordial gravitational waves | Medium | — |
| G.5.2 | Baryogenesis | Medium | — |
| G.6.1 | Linear perturbation theory and structure formation | Medium | — |
| G.7.1 | Wheeler-DeWitt equation for cosmology | Medium | — |
| G.7.2 | Hartle-Hawking no-boundary proposal | Low | — |
| G.8.1 | Astrophysical black holes | Low | — |
| G.9.1 | Cyclic and bouncing cosmologies | Low | — |

### H.1: Quantum Circuits and Gates ([#78](https://github.com/konard/physical-unified-theory/issues/78))

Use indexed finite complex matrices and a typed circuit composition syntax. Reuse the existing Pauli and Hadamard definitions and compare Physlib and SQIR semantics.

**Verification.** Prove unitarity for each named gate, normalization of Bloch coordinates, and the relevant exact or approximate universality statements.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| H.1.1 | Qubit formalization (Bloch sphere representation) | **Critical** | — |
| H.1.2 | Single-qubit gates (Pauli, Hadamard, phase, T) | **Critical** | — |
| H.1.3 | Multi-qubit gates (CNOT, Toffoli, SWAP) | **Critical** | — |
| H.1.4 | Universal gate sets | High | — |
| H.1.5 | Circuit model of computation | High | — |

### H.2: Quantum Algorithms ([#79](https://github.com/konard/physical-unified-theory/issues/79))

Define oracle and resource models over H.1. Reuse verified library circuits where semantics match and derive reduction or approximation bounds.

**Verification.** Verify correctness and resource assumptions for each named algorithm and small simulation, VQE and QAOA instances.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| H.2.1 | Deutsch-Jozsa algorithm | High | — |
| H.2.2 | Grover's search algorithm | High | — |
| H.2.3 | Shor's factoring algorithm | High | — |
| H.2.4 | Quantum simulation algorithms | Medium | — |
| H.2.5 | Variational quantum algorithms (VQE, QAOA) | Medium | — |

### H.3: Quantum Error Correction ([#80](https://github.com/konard/physical-unified-theory/issues/80))

State Knill–Laflamme conditions with explicit noise channels, then define commuting Pauli stabilizers and cell-complex surface checks.

**Verification.** Verify correction for a small code and distance and commutation properties for a suitable surface-code family.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| H.3.1 | Quantum error correction basics (Knill-Laflamme conditions) | High | — |
| H.3.2 | Stabilizer formalism | High | — |
| H.3.3 | Surface codes | High | — |
| H.3.4 | Topological quantum error correction | Medium | — |

**Hypothesis.** Topological QEC connects to TQFT (Track L) and condensed matter (Track I).

### H.4: Quantum Cryptography ([#81](https://github.com/konard/physical-unified-theory/issues/81))

Represent BB84 as preparation, basis sifting, parameter estimation, reconciliation and amplification. Consider a composable security definition over quantum and classical side information.

**Verification.** Check noiseless key agreement, abort handling and a proved quantitative security bound for a named adversary model.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| H.4.1 | BB84 protocol | High | — |
| H.4.2 | Security proofs | Medium | — |
| H.4.3 | Quantum key distribution | Medium | — |

### H.5: Entanglement Theory ([#82](https://github.com/konard/physical-unified-theory/issues/82))

Define reduced-state, partial-transpose and multipartite invariants on the shared tensor model. Model area laws with explicit classes of Hamiltonians.

**Verification.** Check normalization on product and Bell states, a witness's soundness, multipartite inequivalence and a scoped area-law result.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| H.5.1 | Entanglement measures (concurrence, negativity, entropy) | High | — |
| H.5.2 | Entanglement witnesses | Medium | — |
| H.5.3 | Entanglement area laws | Medium | — |
| H.5.4 | Multipartite entanglement | Medium | — |

**Hypothesis.** Entanglement area laws are fundamental to the gravity-information connection (see Track K).

### H.6–H.8: Complexity, Channels, and Thermodynamics ([#83](https://github.com/konard/physical-unified-theory/issues/83))

Define uniform circuit families with acceptance promises. Build channel capacity and relative entropy APIs and state resource and holographic conjectures precisely.

**Verification.** Verify elementary complexity reductions, data processing, capacity for a simple channel and a resource monotone.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| H.6.1 | BQP and complexity classes | Medium | — |
| H.6.2 | Quantum computational supremacy | Medium | — |
| H.6.3 | Holographic complexity conjectures | Low | — |
| H.7.1 | Quantum channel capacity | Medium | — |
| H.7.2 | Quantum data processing inequality | Medium | — |
| H.8.1 | Quantum thermodynamic resource theory | Low | — |

**Hypothesis.** AdS/CFT is a quantum error-correcting code.

### I.1: Second Quantization and Many-Body Techniques ([#84](https://github.com/konard/physical-unified-theory/issues/84))

Reuse bosonic and fermionic Fock space. Model Hartree–Fock variation, correlator time ordering and perturbative diagrams.

**Verification.** Check occupation bounds, stationary Slater determinant conditions and free Green-function and diagram limits.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| I.1.1 | Many-body Fock space (bosonic and fermionic) | **Critical** | — |
| I.1.2 | Mean-field theory (Hartree-Fock) | High | — |
| I.1.3 | Green's functions (single-particle, many-body) | High | — |
| I.1.4 | Feynman diagrams for condensed matter | Medium | — |

### I.2: Superconductivity ([#85](https://github.com/konard/physical-unified-theory/issues/85))

Formalize gap self-consistency and the Ginzburg–Landau energy. Model flux confinement and Josephson dynamics.

**Verification.** Check a weak-coupling gap law, GL critical parameter and junction phase relations with approximation conditions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| I.2.1 | BCS theory (Cooper pairs, gap equation) | High | — |
| I.2.2 | Ginzburg-Landau theory | High | — |
| I.2.3 | Type-I and Type-II superconductors | Medium | — |
| I.2.4 | Josephson effect | Medium | — |

**Hypothesis.** High-Tc superconductivity is explained by a single theoretical framework.

### I.3: Topological Phases of Matter ([#86](https://github.com/konard/physical-unified-theory/issues/86))

Construct gapped lattice Hamiltonians, symmetry classes, Berry bundles and topological field models for fractional response.

**Verification.** Compute an integer invariant, verify stability under a gap-preserving deformation and check fractional and anyon examples.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| I.3.1 | Topological insulators (Z₂ classification) | High | — |
| I.3.2 | Integer quantum Hall effect (Chern number) | High | — |
| I.3.3 | Fractional quantum Hall effect | High | — |
| I.3.4 | Topological classification (ten-fold way) | Medium | — |
| I.3.5 | Anyons and topological order | Medium | — |

**Hypothesis.** Topological phase classification is governed by cobordism/K-theory.

### I.4–I.5: Quantum Magnetism and Strongly Correlated Systems ([#87](https://github.com/konard/physical-unified-theory/issues/87))

Construct Heisenberg and Hubbard lattice models with reference reductions for spin waves, Kondo and heavy-fermion behavior.

**Verification.** Verify small-lattice spectra and symmetry sectors, then specify the approximation and scale limits of the many-body results.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| I.4.1 | Heisenberg model | Medium | — |
| I.4.2 | Spin waves and magnons | Medium | — |
| I.4.3 | Frustrated magnets and spin liquids | Low | — |
| I.5.1 | Hubbard model | Medium | — |
| I.5.2 | Kondo effect | Low | — |
| I.5.3 | Heavy fermions | Low | — |

### I.6: Tensor Networks and Entanglement ([#88](https://github.com/konard/physical-unified-theory/issues/88))

Define MPS contraction and gauge equivalence, DMRG optimization and MERA isometries. State the holographic relation with explicit assumptions.

**Verification.** Check exact contraction and norm, variational energy improvement and the scales or geometries modeled by MERA.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| I.6.1 | Matrix product states (MPS) | High | — |
| I.6.2 | DMRG algorithm | Medium | — |
| I.6.3 | MERA (multiscale entanglement renormalization) | Medium | — |
| I.6.4 | Tensor network / holography connection | Medium | — |

**Hypothesis.** MERA encodes AdS geometry, realizing the holographic principle (see Track K).

### I.7: Emergent Phenomena ([#89](https://github.com/konard/physical-unified-theory/issues/89))

Derive coarse-grained and low-energy variables for explicit microscopic models. State emergent gravity comparisons using K and F.

**Verification.** Check a universality class or low-energy effective expansion and show the regime in which the emergent gauge quantities are valid.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| I.7.1 | Universality and effective theories | Medium | — |
| I.7.2 | Emergent gauge fields | Low | — |
| I.7.3 | Gravity as emergent phenomenon | Low | — |

**Hypothesis.** Gravity is emergent like elasticity — it arises from microscopic degrees of freedom.

### J.1: Neutrino Physics ([#90](https://github.com/konard/physical-unified-theory/issues/90))

Define Dirac and Majorana mass matrices, PMNS flavor transitions and block reduction for the seesaw scale.

**Verification.** Verify probability conservation, vacuum two-flavor limit and the block-diagonalization error estimate.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| J.1.1 | Neutrino mass terms (Dirac and Majorana) | High | — |
| J.1.2 | Neutrino oscillations (PMNS matrix) | High | — |
| J.1.3 | Seesaw mechanism | Medium | — |

**Hypothesis.** Neutrinos are Majorana fermions and the seesaw mechanism explains their small masses.

### J.2: CP Violation and Matter-Antimatter Asymmetry ([#91](https://github.com/konard/physical-unified-theory/issues/91))

Use flavor-basis invariants and CP transformations for CKM, the QCD theta term and axion relaxation. State Sakharov premises.

**Verification.** Check Jarlskog rephasing invariance, an explicit axion potential minimum and applicability of the baryogenesis criteria.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| J.2.1 | CKM matrix and CP violation in quarks | High | — |
| J.2.2 | Strong CP problem | High | — |
| J.2.3 | Axions as solution to strong CP | High | — |
| J.2.4 | Baryogenesis (Sakharov conditions) | Medium | — |

**Hypothesis.** Axions solve the strong CP problem and constitute dark matter.

### J.3: Grand Unified Theories ([#92](https://github.com/konard/physical-unified-theory/issues/92))

Define embeddings and representation branching for SU(5) and SO(10). Match running couplings and decay operators at reference scales.

**Verification.** Check group and charge assignments, model-dependent proton lifetimes and comparison to experiment with assumptions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| J.3.1 | SU(5) GUT (Georgi-Glashow) | High | — |
| J.3.2 | SO(10) GUT | High | — |
| J.3.3 | Proton decay predictions | Medium | — |
| J.3.4 | Gauge coupling unification | Medium | — |

**Hypothesis.** Gauge couplings unify at the GUT scale (~10¹⁶ GeV).

### J.4: Supersymmetry ([#93](https://github.com/konard/physical-unified-theory/issues/93))

Build graded algebra and representations, model MSSM field content, and use explicit spontaneous or soft breaking parameters.

**Verification.** Check superalgebra closure, symmetry and charge invariance of MSSM terms and stated naturalness measures.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| J.4.1 | SUSY algebra and superfields | High | — |
| J.4.2 | Minimal Supersymmetric Standard Model (MSSM) | High | — |
| J.4.3 | SUSY breaking mechanisms | Medium | — |
| J.4.4 | Naturalness and hierarchy problem | Medium | — |

### J.5–J.9: Extra Dimensions, Dark Matter, Flavor, Precision, Collider ([#94](https://github.com/konard/physical-unified-theory/issues/94))

Use model-specific Lagrangians and alternative event-level numerical calculators. Keep flavor, precision and collider quantities in the same schema.

**Verification.** Verify compactification spectra, relic or collider predictions and agreement with specified benchmark constraints under a documented model.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| J.5.1 | Kaluza-Klein theory | Medium | — |
| J.5.2 | Large extra dimensions (ADD) | Medium | — |
| J.5.3 | Warped extra dimensions (Randall-Sundrum) | Medium | — |
| J.6.1 | WIMP dark matter | Medium | — |
| J.6.2 | Axion dark matter | Medium | — |
| J.7.1 | Flavor symmetries | Low | — |
| J.8.1 | Precision electroweak tests | Low | — |
| J.9.1 | Collider phenomenology | Low | — |

### K.0: The Incompatibility Problem ([#95](https://github.com/konard/physical-unified-theory/issues/95))

State perturbative power counting, time evolution and background choices under precise hypotheses. Use the published two-loop counterterm as a reference.

**Verification.** Derive superficial divergence counting and distinguish the perturbative result from a general impossibility claim. Verify constraint-generated time in a specified model.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| K.0.1 | Formal statement of QM-GR incompatibility | **Critical** | — |
| K.0.2 | Non-renormalizability of perturbative quantum gravity | **Critical** | — |
| K.0.3 | Problem of time | High | — |
| K.0.4 | Background independence requirement | High | — |

### K.1: Canonical Quantum Gravity ([#96](https://github.com/konard/physical-unified-theory/issues/96))

Define canonical constraints and holonomies before loop kinematics. Use spin-labeled graphs and state precisely which spectra are kinematical.

**Verification.** Check a discrete area example and a homogeneous cosmology constraint, then spell out which physical-observable and dynamics results remain needed.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| K.1.1 | Wheeler-DeWitt equation | High | — |
| K.1.2 | Loop quantum gravity (Ashtekar variables, holonomies) | High | — |
| K.1.3 | Spin networks and spin foams | High | — |
| K.1.4 | Loop quantum cosmology | Medium | — |
| K.1.5 | Discrete area and volume spectra | Medium | — |

**Hypothesis.** LQG correctly quantizes GR with discrete spectra for area and volume.

### K.2: String Theory and M-Theory ([#97](https://github.com/konard/physical-unified-theory/issues/97))

Model string actions and equivalences, type-specific fields, compactification and candidate dual observables.

**Verification.** Verify classical action equivalence under its assumptions and controlled AdS/CFT limits. State the full correspondence and swampland proposals explicitly as conjectures.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| K.2.1 | Bosonic string (Nambu-Goto and Polyakov actions) | High | — |
| K.2.2 | Superstring theory (Type I, IIA, IIB, heterotic) | High | — |
| K.2.3 | Compactification (Calabi-Yau, flux) | Medium | — |
| K.2.4 | D-branes and gauge/gravity duality | High | — |
| K.2.5 | AdS/CFT correspondence | **Critical** | — |
| K.2.6 | String phenomenology and landscape | Medium | — |
| K.2.7 | Swampland conjectures | Medium | — |

**Hypothesis.** String theory is the correct theory of quantum gravity; the landscape admits physical selection.

### K.3–K.5: Causal Sets, CDT, Asymptotic Safety ([#98](https://github.com/konard/physical-unified-theory/issues/98))

Model locally finite partially ordered sets, simplicial causal amplitudes and a parameterized RG functional separately.

**Verification.** Verify finite counts and limiting benchmarks. Capture the Hauptvermutung and full non-Gaussian fixed point claims with their unresolved assumptions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| K.3.1 | Causal set definition and partial order | High | — |
| K.3.2 | Hauptvermutung (manifold-likeness) | Medium | — |
| K.3.3 | Dynamics (sequential growth models) | Medium | — |
| K.4.1 | Simplicial quantum gravity | Medium | — |
| K.4.2 | Phase structure and emergent 4D | Medium | — |
| K.5.1 | Functional renormalization group for gravity | Medium | — |
| K.5.2 | Non-Gaussian fixed point | Medium | — |

### K.6–K.12: Additional QG Approaches ([#99](https://github.com/konard/physical-unified-theory/issues/99))

Model spectral action, twistor and emergent constructions on shared L and F primitives. Use specified group field, foliated and higher-spin models.

**Verification.** Verify representative spectra, correspondences, limits and phenomenological scaling laws for each approach.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| K.6.1 | Non-commutative geometry (Connes' spectral action) | Medium | — |
| K.7.1 | Twistor theory (Penrose) | Medium | — |
| K.8.1 | Emergent gravity (Verlinde, Jacobson) | Medium | — |
| K.9.1 | Group field theory and tensor models | Low | — |
| K.10.1 | Hořava-Lifshitz gravity | Low | — |
| K.11.1 | Quantum gravity phenomenology (predictions) | Medium | — |
| K.12.1 | Other approaches (supergravity, higher-spin, etc.) | Low | — |

### L.1: Algebraic Quantum Field Theory (AQFT) ([#100](https://github.com/konard/physical-unified-theory/issues/100))

Use poset nets of operator algebras, locally covariant functors and faithful-state modular dynamics.

**Verification.** Prove isotony, locality and covariance for a concrete free model, then check the stated DHR and Tomita–Takesaki hypotheses.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| L.1.1 | Haag-Kastler axioms (nets of operator algebras) | High | — |
| L.1.2 | Locally covariant QFT on curved spacetime | High | — |
| L.1.3 | DHR superselection theory | Medium | — |
| L.1.4 | Modular theory (Tomita-Takesaki) | Medium | — |

**Hypothesis.** AQFT provides the correct axiomatization; locally covariant formulation is natural for curved spacetime.

### L.2: Topological Quantum Field Theory (TQFT) ([#101](https://github.com/konard/physical-unified-theory/issues/101))

Represent bordisms and symmetric monoidal functors using category theory. Define the invariants and separately model Witten and Schwarz examples.

**Verification.** Check gluing, disjoint union, Chern–Simons gauge-level conditions and a concrete manifold invariant.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| L.2.1 | Atiyah-Segal axioms | High | — |
| L.2.2 | Chern-Simons theory | High | — |
| L.2.3 | Witten-type and Schwarz-type TQFTs | Medium | — |
| L.2.4 | Topological invariants from TQFT | Medium | — |

**Hypothesis.** Every 3D TQFT arises from a modular tensor category.

### L.3–L.5: Categories, NCG, Geometric Quantization ([#102](https://github.com/konard/physical-unified-theory/issues/102))

Reuse monoidal categories and operator algebras. Model spectral triples, polarization, BRST complexes and formal star products independently over shared primitives.

**Verification.** Check functor laws, finite spectral data, polarization conditions and product associativity or differential nilpotence.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| L.3.1 | Functorial QFT (Atiyah-Segal, Baez-Dolan) | Medium | — |
| L.3.2 | Higher gauge theory and higher categories | Medium | — |
| L.3.3 | Categorical quantum mechanics (Abramsky-Coecke) | Medium | — |
| L.4.1 | Spectral triples and Connes' program | Medium | — |
| L.4.2 | Non-commutative Standard Model | Medium | — |
| L.4.3 | Spectral action principle | Medium | — |
| L.5.1 | Prequantization and polarization | Medium | — |
| L.5.2 | BV-BRST formalism | Medium | — |
| L.5.3 | Deformation quantization | Medium | — |

### L.6–L.10: Advanced Mathematical Frameworks ([#103](https://github.com/konard/physical-unified-theory/issues/103))

Build on Mathlib categories, analysis and algebraic topology. Bring in specialist results through explicit statements with domains.

**Verification.** Verify a Lax invariant, von Neumann example, index example, Fisher metric and homotopy-equivalence interpretation.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| L.6.1 | Integrable systems and exact results | Low | — |
| L.7.1 | Von Neumann algebras (Type III₁ for QFT) | Medium | — |
| L.8.1 | Index theorems in physics (Atiyah-Singer) | Medium | — |
| L.9.1 | Information geometry | Low | — |
| L.10.1 | Homotopy type theory and physics | Low | — |

**Hypothesis.** HoTT provides a natural language for gauge equivalence and physics structures.

### M.1: Novel Unification Proposals ([#104](https://github.com/konard/physical-unified-theory/issues/104))

Formalize constructor-theoretic tasks, an entanglement-to-geometry conjecture and positive geometries for scattering.

**Verification.** Verify examples and specify observable predictions and input assumptions for the competing proposals.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| M.1.1 | Information-theoretic physics (it from bit, constructor theory) | Medium | C.1, H.5 |
| M.1.2 | Spacetime from entanglement (ER=EPR, tensor networks) | Medium | C.6, K.2.5 |
| M.1.3 | Amplituhedron and positive geometry | Low | E.2 |

### M.2: Discrete vs. Continuous Spacetime ([#105](https://github.com/konard/physical-unified-theory/issues/105))

Define discrete causal objects and continuous spectral geometry independently, then supply coarse graining and a candidate continuum relation.

**Verification.** Check recovered dimensions, causal order and test invariants in examples. State extension beyond controlled limits as conjecture.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| M.2.1 | Discrete approaches (causal sets, digital physics) | Medium | K.3 |
| M.2.2 | Continuous approaches (NCG) | Medium | L.4 |
| M.2.3 | Formal comparison of discrete and continuous | Low | M.2.1, M.2.2 |

### M.3–M.6: Time, Measurement, Cosmological Constant, Hierarchy ([#106](https://github.com/konard/physical-unified-theory/issues/106))

Encode clock constraints, modular flow, gravity-driven collapse models and the named vacuum-energy and hierarchy mechanisms with explicit inputs.

**Verification.** Verify model-specific reduced dynamics, scale estimates and consistency conditions. Label competing mechanisms and open predictions.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| M.3.1 | Frozen formalism and internal time | Medium | D.6, K.0.3 |
| M.3.2 | Thermal time hypothesis (Connes-Rovelli) | Medium | F.4, L.1.4 |
| M.3.3 | Page-Wootters mechanism | Medium | C.1 |
| M.3.4 | Emergent time | Low | K (various) |
| M.4.1 | Gravitational collapse models (Penrose, Diósi) | Medium | C.1, D.3 |
| M.4.2 | Many-worlds and quantum gravity | Low | O.1, K (various) |
| M.5.1 | Anthropic landscape solution | Medium | K.2.6 |
| M.5.2 | Dynamical relaxation mechanisms | Medium | E.4, G.4 |
| M.5.3 | Sequestering | Low | E.8 |
| M.6.1 | Supersymmetric solutions | Medium | J.4 |
| M.6.2 | Composite Higgs | Low | E.4 |
| M.6.3 | Extra dimensions solutions | Low | J.5 |

### M.7–M.11: Speculative Directions ([#107](https://github.com/konard/physical-unified-theory/issues/107))

State separate model-specific claims with operational or mathematical criteria, and provide conditional consequences for landscape, analog and structural examples.

**Verification.** Check known special cases such as an acoustic horizon and document the present evidence and falsifiability limits of speculative claims.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| M.7.1 | String landscape and multiverse | Low | K.2.6 |
| M.7.2 | Eternal inflation and measure problem | Low | G.2.4 |
| M.8.1 | Consciousness and physics (Orch OR, IIT) | Low | C.1 |
| M.9.1 | Simulation hypothesis | Low | H.6 |
| M.10.1 | Exceptional mathematical structures in physics | Low | A.4 |
| M.10.2 | Number theory and physics | Low | A.4 |
| M.10.3 | Type theory and physical constraints | Low | L.10 |
| M.11.1 | Analog models (acoustic black holes) | Low | D.8, F.7 |

### N.1: Units and Dimensional Analysis ([#108](https://github.com/konard/physical-unified-theory/issues/108))

Implement the seven SI base exponents as a type index and convert a single coherent SI magnitude using positive base scales. Physlib or Astropy supply comparison implementations.

**Verification.** Compile dimension mismatch tests, prove conversion identity and composition, and check SI, electronvolt-based natural units and positive Planck scales.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| N.1.1 | SI unit system formalization | **Critical** | — |
| N.1.2 | Natural units (ℏ = c = 1) | **Critical** | — |
| N.1.3 | Planck units | High | — |
| N.1.4 | Dimensional analysis as type checking | High | — |
| N.1.5 | Unit conversion framework | High | — |

**Hypothesis.** Type-safe units can prevent dimensional errors at compile-time.

### N.2: Fundamental Constants ([#109](https://github.com/konard/physical-unified-theory/issues/109))

Encode BIPM defining values exactly and pin the 2022 CODATA estimates with same-dimension standard uncertainties and explicit coupling conventions.

**Verification.** Verify source transcription and electronvolt/GeV scales, and sample exact values and uncertainties in both proof assistants.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| N.2.1 | Speed of light, Planck's constant, gravitational constant | **Critical** | — |
| N.2.2 | Fine structure constant | High | — |
| N.2.3 | Particle masses and coupling constants | Medium | — |
| N.2.4 | CODATA values with uncertainties | Medium | — |

### N.3–N.5: Precision Tests of QM, GR, and SM ([#110](https://github.com/konard/physical-unified-theory/issues/110))

Model each theory prediction independently of the observation and use a shared uncertainty interface with official QM, GR and SM records.

**Verification.** Check units, central values and error budgets for spectroscopy, Bell tests, relativistic effects, gravitational waves and electroweak/QCD measurements.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| N.3.1 | Hydrogen spectroscopy (Lamb shift) | High | C.2.3 |
| N.3.2 | Electron g-2 (anomalous magnetic moment) | High | C.4, E.3.1 |
| N.3.3 | Casimir effect | Medium | E.1 |
| N.3.4 | Bell test experiments | High | C.6.3 |
| N.4.1 | Mercury perihelion precession | High | D.4.1 |
| N.4.2 | Gravitational light deflection | High | D.4.1 |
| N.4.3 | Gravitational redshift | High | D.3 |
| N.4.4 | Shapiro time delay | Medium | D.4.1 |
| N.4.5 | Frame-dragging (Gravity Probe B) | Medium | D.4.2 |
| N.4.6 | Gravitational wave detection (LIGO/Virgo) | High | D.7 |
| N.5.1 | Electroweak precision tests (Z-pole, W mass) | Medium | E.4.1 |
| N.5.2 | QCD tests (jet physics, running coupling) | Medium | E.4.3 |
| N.5.3 | Higgs boson properties | Medium | E.4.2 |
| N.5.4 | Muon g-2 anomaly | High | E.3.1 |

### N.6–N.10: QG Predictions, Phenomenology, Cosmological Observations ([#111](https://github.com/konard/physical-unified-theory/issues/111))

Use parameterized quantum-gravity observables and cite the experimental assumption behind each bound. Ingest CMB, BAO, cosmic-ray and neutrino data with provenance.

**Verification.** Reproduce selected published intervals or bounds from release files and verify that error propagation and empirical premises remain explicit.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| N.6.1 | LQG predictions (discrete spectra, Immirzi parameter) | Medium | K.1 |
| N.6.2 | String theory predictions (extra dimensions, moduli) | Medium | K.2 |
| N.6.3 | Asymptotic safety predictions | Low | K.5 |
| N.6.4 | Causal set predictions | Low | K.3 |
| N.7.1 | Modified dispersion relations | Medium | K.11 |
| N.7.2 | Lorentz violation bounds | Medium | K.11 |
| N.7.3 | Gravitational decoherence | Medium | C.7, D.3 |
| N.8.1 | CMB power spectrum | Medium | G.2.2 |
| N.8.2 | Baryon acoustic oscillations | Medium | G.6 |
| N.9.1 | Cosmic ray physics | Low | J.6 |
| N.9.2 | Neutrino astronomy | Low | J.1 |
| N.10.1 | Formalized experimental results with error bars | Medium | All |

**Hypothesis.** Formalizing experimental results as theorems with error bars creates a rigorous theory-experiment interface.

### O.1: Quantum Measurement Problem ([#112](https://github.com/konard/physical-unified-theory/issues/112))

Use a shared measurement interaction plus interpretation-specific ontology or stochastic postulates. Formalize the outcome inconsistency as a scoped result.

**Verification.** Verify the measurement model in a finite example and compare assumptions and derived predictions for each interpretation.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| O.1.1 | Formal statement of the measurement problem | **Critical** | C.1 |
| O.1.2 | Copenhagen interpretation | High | C.1 |
| O.1.3 | Many-worlds interpretation (Everett) | High | C.1 |
| O.1.4 | Bohmian mechanics (pilot-wave theory) | High | C.1 |
| O.1.5 | Consistent histories | Medium | C.1 |
| O.1.6 | Relational quantum mechanics | Medium | C.1 |
| O.1.7 | QBism | Medium | C.1 |
| O.1.8 | Collapse theories (GRW, CSL) | Medium | C.1 |

**Hypothesis.** Different QM interpretations make different predictions in extreme regimes (gravity, cosmology).

### O.2: Operational and Reconstructive Approaches ([#113](https://github.com/konard/physical-unified-theory/issues/113))

Define preparations, effects, transformations and composition for GPTs. Formalize Hardy and Chiribella reconstructions separately and connect orthomodular logic to projection lattices.

**Verification.** Check axioms in classical and quantum examples and account for hypotheses used to obtain uniqueness.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| O.2.1 | Hardy's axioms for QM | High | C.1 |
| O.2.2 | Informational axioms (Chiribella et al.) | High | C.1 |
| O.2.3 | Generalized probabilistic theories (GPTs) | High | C.1 |
| O.2.4 | Quantum logic | Medium | A.4 |

**Hypothesis.** QM is uniquely derivable from information-theoretic axioms.

### O.3: Determinism and Indeterminism ([#114](https://github.com/konard/physical-unified-theory/issues/114))

Formalize finite local-hidden-variable models, contextual assignments and ontic-state axioms and encode the named impossibility arguments.

**Verification.** Check Bell/CHSH violation and assumptions, then verify finite Kochen–Specker, PBR and free-will constructions in their respective models.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| O.3.1 | Bell's theorem (formal proof and implications) | **Critical** | C.6 |
| O.3.2 | Kochen-Specker theorem | High | C.1 |
| O.3.3 | PBR theorem (reality of quantum state) | High | C.1 |
| O.3.4 | Free will theorem | Medium | C.6 |
| O.3.5 | Superdeterminism | Low | O.3.1 |

**Hypothesis.** Bell/Kochen-Specker/PBR constraints uniquely determine viable interpretations.

### O.4–O.9: Spacetime, Arrow of Time, Symmetry, QG Foundations ([#115](https://github.com/konard/physical-unified-theory/issues/115))

Reuse covariance, entropy, causal and gauge models to express the hole argument, arrows of time, symmetry results and relational observables.

**Verification.** Check equivalences under diffeomorphisms, monotonicity hypotheses, Wigner/CPT domains and which quantum-gravity or ontology claims require extra premises.

| Task | Requirement | Priority | Prerequisites in issue |
| --- | --- | --- | --- |
| O.4.1 | Substantivalism vs. relationalism | Medium | D.3 |
| O.4.2 | Hole argument (Einstein, Earman-Norton) | Medium | D.3 |
| O.4.3 | Emergent spacetime | Medium | K (various) |
| O.4.4 | Structural realism | Low | O.4.2 |
| O.5.1 | Thermodynamic arrow (second law) | Medium | F.1, F.4 |
| O.5.2 | Cosmological arrow | Medium | G.1 |
| O.5.3 | Radiative arrow | Low | B.5 |
| O.5.4 | Quantum arrow (measurement irreversibility) | Medium | C.1, O.1 |
| O.6.1 | Wigner classification of particles | High | D.1, C.3 |
| O.6.2 | Gauge symmetry: physical vs. mathematical | Medium | E.3 |
| O.6.3 | Noether's theorem (physical interpretation) | Medium | B.2.3 |
| O.6.4 | CPT theorem | Medium | E.1 |
| O.7.1 | Nature of physical laws | Low | — |
| O.8.1 | Measurement problem in quantum gravity | Medium | O.1, K.0 |
| O.8.2 | Observables in quantum gravity | Medium | K.0 |
| O.8.3 | Relational approach to QG | Medium | O.1.6, K.0 |
| O.9.1 | Unreasonable effectiveness of mathematics | Low | — |

**Hypothesis.** QG foundational issues are QM interpretational problems amplified by background independence.
