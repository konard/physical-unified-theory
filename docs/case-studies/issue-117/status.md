# Implementation status and research sources for issue 117

[Requirements and proposed verification](requirements.md) covers the full scope of
[issue 117](https://github.com/konard/physical-unified-theory/issues/117). The
deliverables below are evidence for particular tasks. Issue 117 remains open
and [PR 118](https://github.com/konard/physical-unified-theory/pull/118) remains
a draft.

## Scope of the existing formalization

[PR 116](https://github.com/konard/physical-unified-theory/pull/116) supplied
parts of each Track A issue. The declarations under
[Lean Foundations](../../../lean/PhysicalUnifiedTheory/Foundations) and
[Rocq Foundations](../../../rocq/theories/Foundations) contain a mixture of
general APIs, restricted models and described future constructions. For
example, the topology code refers to characteristic classes in comments, and
the Rocq PDE models include the discriminant of three linear examples and a
scalar Ricci flow model. Those results are insufficient to close #30 or #33.

The existing QM and GR directories cover some of C.1, C.2, C.6, D.1, D.2 and
D.5, including finite-state examples and flat-space calculations. The
[unification basics](../../../lean/PhysicalUnifiedTheory/Unification/Basic.lean)
and [unification background](../../UNIFICATION_CHALLENGES.md) cover some
concepts in K.0. The other planned tracks do not have complete formalizations
in the starting revision. No required issue was found to be fully resolved in
that revision.

The baseline Lean workflow logged compilation failures while passing the build
step. The shell reported the status of `tee` in the build pipeline. The first
errors include obsolete Mathlib imports and a change of the selected Lean
toolchain during the run. [Main workflow run 45973370187](https://github.com/konard/physical-unified-theory/actions/runs/45973370187)

## Implementation and verification

| Requirement | Implementation | Acceptance evidence |
| --- | --- | --- |
| A.1.2 and A.1.3 in part | Lean provides domain-aware operators and adjoints, the continuous functional calculus for bounded self-adjoint operators, and a formula in a Hermitian matrix's eigenbasis. | Lean checks density and closedness for self-adjoint operators, the adjoint of a bounded operator restricted to a dense core, the spectral mapping theorem, the Pauli X square and real self-adjoint expectations. Borel calculus and spectral resolutions for general unbounded operators still need implementation. [LinearAlgebra.lean](../../../lean/PhysicalUnifiedTheory/Foundations/LinearAlgebra.lean) · [HilbertSpaces.lean](../../../lean/PhysicalUnifiedTheory/Foundations/HilbertSpaces.lean) |
| A.1.4–A.1.5 | Lean constructs the Schwartz–L²–tempered-distribution triple on finite-dimensional real inner-product spaces. | Lean checks both continuous linear embeddings for injectivity, the density of the first embedding and the agreement of the two constructions of the distribution for a test function. [Distributions.lean](../../../lean/PhysicalUnifiedTheory/Foundations/Distributions.lean) |
| A.2.5 in part | The Rocq minimal-monopole example requires nonzero electric charge. | Rocq checks denominator cancellation under the charge hypothesis. The wider bundle requirements remain open. |
| A.5.2 and C.1.3 in part | Lean constructs the position probability measure of a normalized L² wave function and the pure-state update for a complementary pair of projective outcomes. | Lean verifies independence from the almost-everywhere representative, absolute continuity, normalization of both outcome laws and certainty when repeating the selected projective measurement. A constant unit wave function recovers every measurable region's reference probability. The general observable and mixed-state update remain outstanding. [MeasureTheory.lean](../../../lean/PhysicalUnifiedTheory/Foundations/MeasureTheory.lean) · [Lean test](../../../lean/tests/PositionMeasurement.lean) |
| C.1.3 and F.2.1 in part | Finite-dimensional Lean density matrices and real two-dimensional Rocq density matrices require a nonnegative quadratic form. | Both tests exclude the trace-one matrix with diagonal entries 1/2 and off-diagonal entries 1. Lean also constructs positive trace-one density matrices from normalized state vectors. [Lean test](../../../lean/tests/DensityMatrix.lean) · [Rocq test](../../../rocq/tests/DensityMatrix.v) |
| C.6.3 and O.3.1 in part | Lean and Rocq formalize the CHSH bound for finite local hidden-variable models and compute the Bell-state score for Pauli-plane measurements. | Both kernels check the bound of 2 and a quantum score of 2√2. The model uses one distribution for all measurement settings. [Lean](../../../lean/PhysicalUnifiedTheory/QuantumMechanics/Bell.lean) · [Rocq](../../../rocq/theories/QuantumMechanics/Bell.v) · [Original CHSH paper](https://doi.org/10.1103/PhysRevLett.23.880) |
| N.1.1 and N.1.4 | The seven SI base dimensions are type indices in both implementations. Quantities carry coherent SI values and typed addition, subtraction, products, quotients and square roots. | Both regression files reject an attempt to add time to length. |
| N.1.2 and N.1.3 | Coherent natural units are parameterized by a positive energy scale. The Planck system uses the energy derived from ℏ, c and the CODATA central estimate for G. The electrical scale uses the elementary charge, and amount and luminous intensity retain their SI scales. | Both kernels check that the central estimate of G has magnitude one in Planck units. Both test suites verify the normalization of c and ℏ and the positivity of Planck length. The Lean tests also cover the electronvolt energy scale. |
| N.1.5 | Conversion operates on a single dimension and supports coherent multiplicative systems. | Both kernels check conversion identity and composition. |
| N.2.1–N.2.4 | SI defining constants and derived ℏ, 2022 CODATA G and fine-structure estimates, representative lepton and nucleon masses, weak mixing and Fermi coupling. The Fermi coupling is expressed in inverse square energy in the conventional natural-unit convention. | Exact values and uncertainty regressions run in both proof assistants. The source edition is pinned explicitly. |

The unit-system model uses positive multiplicative scales. Affine display
scales, such as degrees Celsius, require a separate origin. The measured
constants carry standard uncertainties from the cited CODATA adjustment.
[2022 CODATA adjustment](https://doi.org/10.1103/RevModPhys.97.025002)

The previous scalar constants in the foundations modules retain the fixed
Planck-unit convention of the examples that use them. The SI values, dimensions
and unit conversions are provided by the experimental modules. The remaining
tasks in the inventory still need task-specific implementation or verification.

[Lean Units](../../../lean/PhysicalUnifiedTheory/Experimental/Units.lean) ·
[Lean Constants](../../../lean/PhysicalUnifiedTheory/Experimental/Constants.lean) ·
[Lean tests](../../../lean/tests/Units.lean) ·
[Rocq Units](../../../rocq/theories/Experimental/Units.v) ·
[Rocq Constants](../../../rocq/theories/Experimental/Constants.v) ·
[Rocq tests](../../../rocq/tests/Units.v)

## Research limits

- A.5.3 asks for functional integration, and E.2.4 asks for nonperturbative
  methods. Their related hypotheses concern 4D interacting path integrals
  and the Yang–Mills mass gap. A finite lattice model or a Gaussian free-field
  measure can provide checked examples for those tasks. The continuum mass-gap
  problem asks for construction of the interacting theory and a proof of the
  gap. Those results remain open. A precise statement of the hypotheses and
  a formalization of established nonperturbative methods are still outstanding.
  [Clay Mathematics Institute](https://www.claymath.org/millennium/yang-mills-the-maths-gap/)
- B.8.1 can formalize the Navier–Stokes equations, weak and strong solution
  notions and established restricted results. A general global smoothness
  theorem in three dimensions would exceed those established results.
  [Clay Mathematics Institute](https://www.claymath.org/millennium/navier-stokes-equation/)
- D.5.4 explicitly asks for a conjecture. It needs separate weak and strong
  statements with precise initial data, asymptotic conditions and the chosen
  genericity and regularity assumptions. A formulation is a different
  deliverable from a proof. [Dafermos and Luk, the interior of dynamical vacuum black holes](https://arxiv.org/abs/1710.01722)
- K.2.5 can use Maldacena's stated correspondence and checked classical or
  semiclassical limits. A full formal equivalence needs precise definitions of
  both sides, the regime covered and proofs that their observables agree.
  [Maldacena's original paper](https://arxiv.org/abs/hep-th/9711200)
- G.3, J.6, K, M and N contain model-dependent or observationally unresolved
  claims. Formal statements should expose the model and observable and link
  relevant data, with the scope of the inference explicit. A verified
  conditional result proves the model implication. Establishing the premise
  itself requires further mathematical or experimental evidence.
  [Particle Data Group review and data](https://pdg.lbl.gov/)

## Reuse options

- **Mathlib and MathComp Analysis.** In Lean, reuse the pinned Mathlib
  Hilbert-space, matrix, geometry, category, topology and measure APIs. In Rocq,
  MathComp Analysis is an option for moving beyond the standard-library real
  and finite worked examples. A migration would need an interface between
  existing statements and the external analysis types.
  [Mathlib](https://github.com/leanprover-community/mathlib4) ·
  [MathComp Analysis](https://github.com/math-comp/analysis)
- **Physlib.** Compare its available modules against B, C, D, E, F, G, I, J, K
  and N. Its classical mechanics, relativity, QFT, particle physics and units
  modules offer candidate definitions and prior formalizations. Importing it
  directly would require matching its Lean/Mathlib toolchain and honoring the
  upstream license. The implementation here uses the local APIs and original
  proofs. [Physlib](https://github.com/leanprover-community/physlib)
- **CoqQ and SQIR.** CoqQ supplies a logic and libraries for quantum programs.
  SQIR supplies circuits, matrix semantics and proofs for quantum algorithms
  and program transformations. For H.1–H.3 and finite parts of C, an adapter
  can connect register, matrix and probability conventions. H.4 still needs
  a protocol and its security model.
  [CoqQ](https://github.com/coq-quantum/CoqQ) ·
  [SQIR](https://github.com/inQWIRE/SQIR)
- **Astropy and CAMB.** Astropy offers an independent check of conversions and
  units. CAMB offers numerical predictions for CMB and structure formation
  once inputs and options are fixed. Their numerical results can validate
  reference examples in G and N. Proofs that use those values still need an
  explicit numerical error budget.
  [Astropy](https://github.com/astropy/astropy) ·
  [CAMB](https://github.com/cmbant/CAMB)
- **Reference observations.** Use the source release and units for each
  experimental value. The SI Brochure and 2022 CODATA table ground N.1–N.2.
  Planck frequency products and likelihoods, GWOSC strain and catalogs, ATLAS
  open data, and PDG reviews are candidate inputs for G, J and N. Each derived
  interval should record its sample, calibrated release, confidence or
  credibility convention and model assumptions.
  [BIPM SI Brochure](https://www.bipm.org/en/publications/si-brochure) ·
  [NIST 2022 CODATA table](https://physics.nist.gov/cuu/Constants/Table/allascii.txt) ·
  [Planck Legacy Archive](https://pla.esac.esa.int/) ·
  [Gravitational Wave Open Science Center](https://gwosc.org/) ·
  [ATLAS Open Data](https://opendata.atlas.cern/) ·
  [Particle Data Group](https://pdg.lbl.gov/)
