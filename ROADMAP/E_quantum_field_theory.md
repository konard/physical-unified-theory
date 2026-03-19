# Track E: Quantum Field Theory

**Status**: Not Started
**Goal**: Formalize relativistic quantum theory and the Standard Model
**Dependencies**: Track A (A.1, A.2, A.4, A.5), Track C (C.1, C.9), Track D (D.1)
**Directory**: `lean/PhysicalUnifiedTheory/QuantumFieldTheory/`, `rocq/theories/QuantumFieldTheory/`

---

## E.1 Free Field Theory

### E.1.1 Scalar Fields
- [ ] Klein-Gordon equation (classical and quantized)
- [ ] Real and complex scalar fields
- [ ] Mode expansion and Fock space
- [ ] Propagator (Feynman, retarded, advanced)
- [ ] Causality and microcausality

### E.1.2 Spinor Fields
- [ ] Dirac equation and its solutions
- [ ] Spinor representations of the Lorentz group
- [ ] Weyl and Majorana spinors
- [ ] Quantization of the Dirac field
- [ ] Spin-statistics theorem

### E.1.3 Vector Fields
- [ ] Proca equation (massive vector)
- [ ] Maxwell field quantization
- [ ] Photon as massless spin-1 particle
- [ ] Gauge freedom and gauge fixing

### E.1.4 General Structure
- [ ] Fock spaces and particle interpretation
- [ ] Wightman axioms
- [ ] PCT theorem
- [ ] Cluster decomposition
- [ ] Haag's theorem (non-existence of interaction picture)

**Hypothesis E.1**: *Haag's theorem implies that the interaction picture is mathematically ill-defined, yet perturbation theory works extraordinarily well — a formal resolution of this paradox would deepen our understanding of QFT.*

---

## E.2 Interacting Field Theory

### E.2.1 Perturbation Theory
- [ ] S-matrix and LSZ reduction formula
- [ ] Wick's theorem
- [ ] Feynman rules from Lagrangian
- [ ] Tree-level amplitudes
- [ ] Loop integrals and regularization

### E.2.2 Renormalization
- [ ] UV divergences and power counting
- [ ] Dimensional regularization
- [ ] Minimal subtraction (MS, MS-bar)
- [ ] Renormalization group equations
- [ ] Beta functions and running couplings
- [ ] Asymptotic freedom
- [ ] Renormalizability vs. non-renormalizability
- [ ] Effective field theory approach

### E.2.3 Non-Perturbative Aspects
- [ ] Instantons and tunneling in field theory
- [ ] Solitons and topological defects
- [ ] Confinement (qualitative understanding)
- [ ] Lattice field theory basics
- [ ] Large-N expansion

**Hypothesis E.2**: *A complete non-perturbative definition of Yang-Mills theory in 4 dimensions exists with a mass gap — this is the Yang-Mills Millennium Prize problem, and formal verification can contribute to its eventual resolution.*

---

## E.3 Gauge Theories

### E.3.1 Abelian Gauge Theory
- [ ] U(1) gauge symmetry
- [ ] Gauge-covariant derivative
- [ ] Quantum electrodynamics (QED) Lagrangian
- [ ] QED Feynman rules
- [ ] Anomalous magnetic moment
- [ ] Lamb shift

### E.3.2 Non-Abelian Gauge Theory
- [ ] SU(N) gauge symmetry
- [ ] Yang-Mills Lagrangian
- [ ] Ghost fields (Faddeev-Popov)
- [ ] BRST symmetry and cohomology
- [ ] Gauge fixing (Lorenz, Coulomb, axial)
- [ ] Gribov copies and the Gribov horizon

### E.3.3 Spontaneous Symmetry Breaking
- [ ] Goldstone theorem (global symmetry breaking)
- [ ] Higgs mechanism (local symmetry breaking)
- [ ] Mass generation for gauge bosons
- [ ] Nambu-Goldstone bosons
- [ ] Mexican hat potential

---

## E.4 The Standard Model

### E.4.1 Electroweak Theory
- [ ] SU(2)_L × U(1)_Y gauge group
- [ ] Weinberg-Salam model
- [ ] Electroweak symmetry breaking
- [ ] W and Z boson masses
- [ ] Weak mixing angle
- [ ] Neutrino interactions

### E.4.2 Quantum Chromodynamics
- [ ] SU(3)_c gauge group and color
- [ ] Quark model and hadron spectroscopy
- [ ] Asymptotic freedom proof
- [ ] Confinement hypothesis
- [ ] Chiral symmetry and its breaking
- [ ] QCD phase diagram (deconfinement, quark-gluon plasma)

### E.4.3 Full Standard Model
- [ ] SU(3) × SU(2) × U(1) gauge group
- [ ] Fermion content and representations
- [ ] Yukawa couplings and fermion masses
- [ ] CKM matrix (quark mixing)
- [ ] PMNS matrix (neutrino mixing)
- [ ] CP violation
- [ ] Anomaly cancellation

**Hypothesis E.4**: *The specific gauge group SU(3) × SU(2) × U(1) and fermion representations of the Standard Model are not arbitrary but follow from a deeper principle — a grand unified group, a string compactification, or a mathematical classification theorem.*

---

## E.5 Anomalies

- [ ] Chiral anomaly (ABJ anomaly)
- [ ] Gauge anomalies and anomaly cancellation
- [ ] Global anomalies (Witten SU(2) anomaly)
- [ ] Gravitational anomalies
- [ ] 't Hooft anomaly matching
- [ ] Anomaly inflow

**Hypothesis E.5**: *Anomaly cancellation conditions constrain the possible matter content of consistent quantum field theories so strongly that the Standard Model spectrum is (nearly) uniquely determined.*

---

## E.6 Topological Aspects of QFT

- [ ] Theta vacuum and strong CP problem
- [ ] Instantons in Yang-Mills theory
- [ ] Topological charges and winding numbers
- [ ] Magnetic monopoles ('t Hooft-Polyakov)
- [ ] Cosmic strings and domain walls
- [ ] Topological field theories (Chern-Simons, BF theory)

---

## E.7 Conformal Field Theory

- [ ] Conformal group and conformal transformations
- [ ] Primary operators and operator product expansion
- [ ] 2D CFT: Virasoro algebra, central charge
- [ ] Minimal models
- [ ] Conformal bootstrap
- [ ] Connections to string theory (Track K)

---

## E.8 Effective Field Theories

- [ ] Wilsonian renormalization group
- [ ] Decoupling and matching
- [ ] Chiral perturbation theory
- [ ] Heavy quark effective theory
- [ ] Soft-collinear effective theory
- [ ] Effective field theory of gravity

**Hypothesis E.8**: *All quantum field theories — including quantum gravity — are effective field theories valid below some energy scale, and the search for a "final theory" is misguided; instead, the correct question is what completes each EFT at higher energies.*

---

## Resources

- Peskin & Schroeder, "An Introduction to Quantum Field Theory"
- Weinberg, "The Quantum Theory of Fields" (3 volumes)
- Schwartz, "Quantum Field Theory and the Standard Model"
- Zee, "Quantum Field Theory in a Nutshell"
- [Lean Millennium Prize Problems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) - Yang-Mills formalization
- PhysLean's Wick theorem formalization
