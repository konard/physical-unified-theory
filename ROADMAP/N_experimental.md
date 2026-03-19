# Track N: Experimental Connections and Predictions

**Status**: Not Started
**Goal**: Link formal theory to observation, formalize dimensional analysis, and catalog predictions
**Dependencies**: Track A (A.1), various physics tracks
**Directory**: `lean/PhysicalUnifiedTheory/Experimental/`

---

## N.1 Units and Dimensional Analysis

### N.1.1 Unit Systems
- [ ] SI units formalization (type-safe physical quantities)
- [ ] Natural units (ℏ = c = 1)
- [ ] Planck units (ℏ = c = G = 1)
- [ ] Gaussian/CGS units for electromagnetism
- [ ] Unit conversion proofs

### N.1.2 Dimensional Analysis
- [ ] Buckingham Pi theorem
- [ ] Dimensional homogeneity as a type constraint
- [ ] Dimensional analysis as a proof technique
- [ ] Scale-invariance and scaling laws

**Hypothesis N.1**: *A type-safe unit system in a proof assistant can catch physically meaningless equations at compile time, preventing entire classes of errors in physics computations — this is one of the most immediately practical contributions of formalization to physics.*

---

## N.2 Fundamental Constants

- [ ] Speed of light c (definition and role)
- [ ] Planck's constant ℏ (quantum of action)
- [ ] Gravitational constant G (coupling strength of gravity)
- [ ] Fine structure constant α ≈ 1/137 (electromagnetic coupling)
- [ ] Boltzmann constant k_B (thermal-statistical bridge)
- [ ] Cosmological constant Λ
- [ ] Relationships between constants
- [ ] Time variation of constants (theoretical and observational bounds)

---

## N.3 Precision Tests of QM

- [ ] Spectroscopy of hydrogen and hydrogen-like atoms
- [ ] Anomalous magnetic moment of the electron (g-2)
- [ ] Lamb shift
- [ ] Casimir effect
- [ ] Bell inequality violations
- [ ] Quantum eraser experiments
- [ ] Delayed-choice experiments (Wheeler)
- [ ] Aharonov-Bohm effect

---

## N.4 Precision Tests of GR

- [ ] Perihelion precession of Mercury
- [ ] Gravitational light deflection
- [ ] Shapiro time delay
- [ ] Gravitational redshift (Pound-Rebka)
- [ ] Frame-dragging (Gravity Probe B, LARES)
- [ ] Gravitational waves (LIGO/Virgo/KAGRA)
- [ ] Binary pulsar orbital decay (Hulse-Taylor)
- [ ] Strong-field tests (black hole shadows, EHT)
- [ ] Gravitational lensing

---

## N.5 Precision Tests of the Standard Model

- [ ] Electroweak precision tests (Z pole, W mass)
- [ ] QCD: jet physics, alpha_s running
- [ ] Higgs boson mass and couplings
- [ ] CKM unitarity triangle
- [ ] Rare B and K decays
- [ ] Muon g-2 anomaly
- [ ] Lepton flavor universality tests

---

## N.6 Predictions from Quantum Gravity Approaches

### N.6.1 Loop Quantum Gravity Predictions
- [ ] Discrete area/volume spectra
- [ ] Modified dispersion relations
- [ ] Loop quantum cosmology signatures in CMB
- [ ] Black hole entropy from spin network counting

### N.6.2 String Theory Predictions
- [ ] Extra dimensions (signatures at colliders)
- [ ] String resonances
- [ ] Landscape predictions (statistical approach)
- [ ] Swampland constraints on effective theories

### N.6.3 Asymptotic Safety Predictions
- [ ] UV fixed point values
- [ ] Predictions for Higgs mass, cosmological constant
- [ ] Modified black hole metrics

### N.6.4 Other Approaches
- [ ] Causal set predictions (swerves, Λ prediction)
- [ ] Non-commutative geometry (Higgs mass prediction)
- [ ] CDT predictions (spectral dimension)

---

## N.7 Quantum Gravity Phenomenology

- [ ] Modified dispersion relations and time-of-flight tests (GRBs)
- [ ] Lorentz invariance violation (photon polarization, threshold effects)
- [ ] Gravitational decoherence experiments
- [ ] Neutron interferometry in gravitational fields
- [ ] Quantum clock interferometry
- [ ] Entanglement of masses (BMV experiment)
- [ ] Gravitational Casimir effect

**Hypothesis N.7**: *Current and near-future experiments (gravitational entanglement tests, atom interferometry, GRB observations) are sensitive enough to probe quantum gravity effects, and at least one of these will yield a positive detection within the next 20 years.*

---

## N.8 Cosmological Observations

- [ ] CMB power spectrum and parameters
- [ ] Baryon acoustic oscillations (BAO)
- [ ] Type Ia supernovae and distance ladder
- [ ] Large-scale structure surveys
- [ ] 21cm cosmology
- [ ] Gravitational wave background
- [ ] CMB B-mode polarization (gravitational wave signature)

---

## N.9 Astroparticle Physics

- [ ] Cosmic ray spectrum and composition
- [ ] Neutrino astronomy (IceCube)
- [ ] Gamma-ray astronomy (Fermi, CTA)
- [ ] Dark matter direct detection experiments
- [ ] Dark matter indirect detection
- [ ] Gravitational wave astronomy (LIGO, LISA, PTA)
- [ ] Multi-messenger astronomy

---

## N.10 Formalized Experimental Results

The goal is to express key experimental results as formal theorems:

- [ ] "The measured value of g-2 for the electron agrees with QED prediction to N significant figures"
- [ ] "Mercury's perihelion precession matches GR prediction"
- [ ] "Bell inequality violations rule out local hidden variable theories"
- [ ] "CMB power spectrum is consistent with ΛCDM + inflation"
- [ ] "LIGO observations confirm gravitational wave predictions of GR"

**Hypothesis N.10**: *Formalizing experimental results as theorems with explicit assumptions and error bars creates a rigorous interface between theory and experiment that can prevent misinterpretation and highlight when new observations are genuinely in tension with established theory.*

---

## Resources

- Particle Data Group (pdg.lbl.gov)
- Planck Collaboration results
- LIGO/Virgo/KAGRA scientific papers
- Will, "Theory and Experiment in Gravitational Physics"
- Amelino-Camelia, "Quantum gravity phenomenology"
