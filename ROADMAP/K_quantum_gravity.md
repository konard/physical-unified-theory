# Track K: Approaches to Quantum Gravity

**Status**: Future
**Goal**: Explore and formalize all known approaches to unifying quantum mechanics and general relativity
**Dependencies**: Track A (all), Track C (C.1), Track D (D.3, D.5, D.6), Track E (E.1, E.2, E.3)
**Directory**: `lean/PhysicalUnifiedTheory/QuantumGravity/`, `rocq/theories/QuantumGravity/`

---

## K.0 The Incompatibility Problem

- [ ] Document the technical incompatibilities:
  - Background dependence (QFT) vs. background independence (GR)
  - Fixed causal structure vs. dynamical causal structure
  - Discrete quantum spectra vs. smooth manifold geometry
  - Problem of time (Hamiltonian constraint H|Ψ⟩ = 0)
  - Non-renormalizability of perturbative quantum gravity
- [ ] Formalize why naive quantization of gravity fails
- [ ] Semiclassical gravity and its limitations
- [ ] Quantum field theory on curved spacetime (as a stepping stone)
- [ ] Hawking radiation and the information paradox

---

## K.1 Canonical Quantum Gravity

### K.1.1 Wheeler-DeWitt Approach
- [ ] ADM formalism quantization
- [ ] Wheeler-DeWitt equation
- [ ] Superspace (space of 3-geometries)
- [ ] Minisuperspace models
- [ ] Problem of time in canonical QG
- [ ] DeWitt metric on superspace

### K.1.2 Loop Quantum Gravity (LQG)
- [ ] Ashtekar variables (connection formulation)
- [ ] Holonomies and fluxes
- [ ] Kinematic Hilbert space
- [ ] Spin network states
- [ ] Area and volume operators
- [ ] Discrete spectra of geometry
- [ ] Thiemann's Hamiltonian constraint
- [ ] Master constraint programme
- [ ] Coherent states and semiclassical limit

### K.1.3 Spin Foams
- [ ] Spin foam models as path integrals for LQG
- [ ] Barrett-Crane model
- [ ] EPRL-FK model
- [ ] Amplitude calculations
- [ ] Relation to Regge calculus
- [ ] Cosmological spin foam models

### K.1.4 Loop Quantum Cosmology
- [ ] Quantum bounce replacing Big Bang singularity
- [ ] Effective equations and phenomenology
- [ ] Observational signatures in CMB
- [ ] Black hole singularity resolution

**Hypothesis K.1a**: *Loop quantum gravity correctly quantizes general relativity, and its prediction of discrete area and volume spectra at the Planck scale is physically realized.*

**Hypothesis K.1b**: *The Big Bang singularity is resolved in loop quantum cosmology, replaced by a "Big Bounce" from a prior contracting phase, and this leaves observable imprints in the cosmic microwave background.*

---

## K.2 String Theory and M-Theory

### K.2.1 Bosonic String Theory
- [ ] Nambu-Goto and Polyakov actions
- [ ] Worldsheet conformal field theory
- [ ] Mode expansion and quantization
- [ ] Critical dimension (D=26)
- [ ] Virasoro algebra and central charge
- [ ] Tachyon and its significance

### K.2.2 Superstring Theory
- [ ] Worldsheet supersymmetry
- [ ] Type IIA and IIB superstrings
- [ ] Heterotic strings (SO(32) and E₈×E₈)
- [ ] Type I string theory
- [ ] Critical dimension (D=10)
- [ ] GSO projection and spacetime supersymmetry

### K.2.3 Compactification
- [ ] Calabi-Yau compactification
- [ ] Flux compactification
- [ ] Moduli stabilization (KKLT, large volume)
- [ ] String landscape (~10⁵⁰⁰ vacua)
- [ ] Swampland conjectures
- [ ] Effective 4D physics from 10D

### K.2.4 D-Branes and Dualities
- [ ] D-branes as dynamical objects
- [ ] Open strings on D-branes
- [ ] T-duality
- [ ] S-duality (strong-weak)
- [ ] M-theory and 11-dimensional supergravity
- [ ] Brane constructions of gauge theories
- [ ] Black hole entropy from D-brane counting (Strominger-Vafa)

### K.2.5 AdS/CFT Correspondence
- [ ] Anti-de Sitter spacetime geometry
- [ ] Conformal field theory on the boundary
- [ ] Dictionary: bulk ↔ boundary operators
- [ ] Holographic entanglement entropy (Ryu-Takayanagi)
- [ ] Holographic renormalization group
- [ ] Applications to strongly coupled systems
- [ ] ER=EPR conjecture
- [ ] Quantum error correction interpretation

### K.2.6 String Phenomenology
- [ ] Standard Model from string compactifications
- [ ] Intersecting brane models
- [ ] F-theory GUTs
- [ ] Moduli and their cosmological role
- [ ] String cosmology

**Hypothesis K.2a**: *String theory is the correct framework for quantum gravity, and the landscape of string vacua contains our universe — but the selection mechanism (anthropic, dynamical, or mathematical) remains to be discovered.*

**Hypothesis K.2b**: *The AdS/CFT correspondence extends to de Sitter space (dS/CFT), providing a non-perturbative definition of quantum gravity in cosmologically relevant spacetimes.*

**Hypothesis K.2c**: *The swampland conjectures — constraints on which effective field theories can be consistently coupled to gravity — are exact and significantly constrain the space of allowed physical theories, potentially ruling out certain cosmological models (e.g., large-field inflation, stable de Sitter vacua).*

---

## K.3 Causal Set Theory

- [ ] Causal sets as partially ordered sets
- [ ] Hauptvermutung (recovery of manifold from causal structure)
- [ ] Dynamics on causal sets (classical sequential growth)
- [ ] Quantum dynamics on causal sets
- [ ] Dimensional estimators
- [ ] Cosmological constant prediction
- [ ] Continuum limit

**Hypothesis K.3**: *Spacetime is fundamentally discrete, described by a causal set (a locally finite partial order), and the continuum of general relativity is an approximation that emerges in a large-number limit — moreover, this discreteness naturally explains the small but nonzero value of the cosmological constant.*

---

## K.4 Causal Dynamical Triangulations (CDT)

- [ ] Simplicial path integral (Regge calculus)
- [ ] Lorentzian vs. Euclidean signature
- [ ] Phase structure (phases A, B, C)
- [ ] Emergence of 4D spacetime from simulations
- [ ] Spectral dimension (scale-dependent dimensionality)
- [ ] Connection to Hořava-Lifshitz gravity

**Hypothesis K.4**: *Causal dynamical triangulations produce a 4-dimensional de Sitter-like universe as a dominant contribution to the gravitational path integral, and the requirement of Lorentzian (causal) structure is essential — Euclidean approaches fail.*

---

## K.5 Asymptotic Safety

- [ ] Functional renormalization group for gravity
- [ ] Effective average action (Wetterich equation)
- [ ] Non-Gaussian UV fixed point
- [ ] Critical exponents and relevant operators
- [ ] Truncation schemes and systematic improvement
- [ ] Predictions for low-energy physics
- [ ] Matter-gravity coupling in the UV

**Hypothesis K.5**: *Quantum gravity is asymptotically safe — it possesses a non-trivial UV fixed point with a finite number of relevant directions, making it non-perturbatively renormalizable and predictive at all energy scales.*

---

## K.6 Non-Commutative Geometry (Connes)

- [ ] Spectral triples and the Dirac operator
- [ ] Non-commutative algebras replacing manifolds
- [ ] Reconstruction of the Standard Model from spectral geometry
- [ ] Spectral action principle
- [ ] Unification of gravity and gauge forces
- [ ] Connections to the Higgs field
- [ ] Non-commutative spacetime and the Planck scale

**Hypothesis K.6**: *The geometry of spacetime at the Planck scale is non-commutative, described by a spectral triple, and the Standard Model of particle physics (including the Higgs) is entirely determined by the algebraic structure of this non-commutative geometry.*

---

## K.7 Twistor Theory

- [ ] Twistor space and the Penrose correspondence
- [ ] Twistor variables for massless particles
- [ ] Scattering amplitudes in twistor space
- [ ] MHV amplitudes and the Parke-Taylor formula
- [ ] BCFW recursion relations
- [ ] Amplituhedron
- [ ] Twistor string theory

**Hypothesis K.7**: *Scattering amplitudes in quantum field theory have a hidden geometric structure (the amplituhedron) that makes locality and unitarity emergent rather than fundamental, suggesting that spacetime itself is emergent from a more fundamental mathematical structure.*

---

## K.8 Emergent Gravity and Entropic Gravity

- [ ] Verlinde's entropic gravity proposal
- [ ] Jacobson's thermodynamic derivation of Einstein equations
- [ ] Padmanabhan's emergent gravity
- [ ] Gravity from entanglement (Van Raamsdonk)
- [ ] Holographic screens and entropy bounds
- [ ] Covariant entropy bound (Bousso)

**Hypothesis K.8**: *Gravity is not a fundamental force but emerges from the thermodynamic/information-theoretic properties of underlying microscopic degrees of freedom — specifically, the Einstein equations are equations of state for the entanglement entropy of quantum fields.*

---

## K.9 Group Field Theory and Tensor Models

- [ ] Group field theory (GFT) as a generalization of matrix models
- [ ] Colored tensor models
- [ ] 1/N expansion for tensor models
- [ ] Relation to spin foams
- [ ] Melonic dominance
- [ ] Continuum limit and phase transitions
- [ ] Sachdev-Ye-Kitaev (SYK) model connections

**Hypothesis K.9**: *Tensor models provide the correct generalization of matrix models (which describe 2D quantum gravity) to higher dimensions, and their large-N limit produces the correct continuum theory of quantum gravity.*

---

## K.10 Hořava-Lifshitz Gravity

- [ ] Anisotropic scaling (space ≠ time at high energies)
- [ ] Detailed balance condition
- [ ] Renormalizability in the UV
- [ ] Recovery of Lorentz invariance in the IR
- [ ] Cosmological applications

**Hypothesis K.10**: *Lorentz invariance is an emergent symmetry that holds only at low energies, and at the Planck scale, space and time scale differently, rendering gravity power-counting renormalizable.*

---

## K.11 Quantum Gravity Phenomenology

- [ ] Planck-scale modifications of dispersion relations
- [ ] Lorentz invariance violation tests (gamma-ray burst timing)
- [ ] Gravitational decoherence
- [ ] Quantum gravity effects in cosmology (CMB signatures)
- [ ] Table-top experiments for quantum gravity
- [ ] Gravitational entanglement (BMV experiment)
- [ ] Black hole echoes (post-merger gravitational waves)

**Hypothesis K.11**: *Quantum gravity effects, though extremely small, leave detectable signatures in astrophysical observations (modified dispersion relations, CMB anomalies) or table-top experiments (gravitational entanglement between masses), and these will be measured within the next few decades.*

---

## K.12 Other Approaches

### K.12.1 Supergravity
- [ ] Local supersymmetry and the gravitino
- [ ] N=1 supergravity in 4D
- [ ] N=8 supergravity (UV finiteness question)
- [ ] Extended supergravity and compactification

### K.12.2 Higher-Spin Gravity
- [ ] Vasiliev theory
- [ ] Higher-spin algebras
- [ ] Holographic duality for higher-spin theories

### K.12.3 Topological Gravity
- [ ] 3D gravity as Chern-Simons theory
- [ ] BTZ black hole
- [ ] 2D dilaton gravity (JT gravity)
- [ ] Connections to matrix models

### K.12.4 Quantum Reference Frames
- [ ] Relational approach to quantum gravity
- [ ] Perspective-neutral framework
- [ ] Quantum covariance

### K.12.5 Gauge-Theoretic Approaches
- [ ] MacDowell-Mansouri gravity
- [ ] BF theory formulation
- [ ] Plebanski action
- [ ] Aalto University gauge-theoretic approach (2025)

---

## Resources

- Kiefer, "Quantum Gravity"
- Rovelli, "Quantum Gravity"
- Polchinski, "String Theory" (2 volumes)
- Becker, Becker & Schwarz, "String Theory and M-Theory"
- Thiemann, "Modern Canonical Quantum General Relativity"
- Oriti (ed.), "Approaches to Quantum Gravity"
- [Stanford Encyclopedia: Quantum Gravity](https://plato.stanford.edu/entries/quantum-gravity/)
