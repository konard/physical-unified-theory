# Plan: Track N — Experimental Connections and Predictions

[← Back to Plan Index](../README.md) | [ROADMAP Entry](../../ROADMAP/N_experimental.md) | [Execution Strategy](../EXECUTION_STRATEGY.md)

## Overview

Track N bridges formal theory to observation. It formalizes units, constants, known experimental results, and predictions from each theoretical approach. Some items (N.1, N.2) can start immediately; others depend on the relevant physics tracks.

## Dependencies

**Upstream**:
- [Track A](../A_mathematical_foundations/) — A.1 for type-safe units
- Various physics tracks provide the theories whose predictions are formalized

**Downstream**: N provides the experimental grounding for all theoretical tracks.

**Can start immediately**: N.1 (units), N.2 (constants)

## Task Breakdown

### N.1: Units and Dimensional Analysis (Phase 1 — Immediate Start)
| Task | Description | Priority |
|------|-------------|----------|
| N.1.1 | SI unit system formalization | **Critical** |
| N.1.2 | Natural units (ℏ = c = 1) | **Critical** |
| N.1.3 | Planck units | High |
| N.1.4 | Dimensional analysis as type checking | High |
| N.1.5 | Unit conversion framework | High |

**Hypothesis to formalize**: Type-safe units can prevent dimensional errors at compile-time.

### N.2: Fundamental Constants (Phase 1 — Immediate Start)
| Task | Description | Priority |
|------|-------------|----------|
| N.2.1 | Speed of light, Planck's constant, gravitational constant | **Critical** |
| N.2.2 | Fine structure constant | High |
| N.2.3 | Particle masses and coupling constants | Medium |
| N.2.4 | CODATA values with uncertainties | Medium |

### N.3: Precision Tests of Quantum Mechanics (Phase 4)
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.3.1 | Hydrogen spectroscopy (Lamb shift) | High | C.2.3 |
| N.3.2 | Electron g-2 (anomalous magnetic moment) | High | C.4, E.3.1 |
| N.3.3 | Casimir effect | Medium | E.1 |
| N.3.4 | Bell test experiments | High | C.6.3 |

### N.4: Precision Tests of General Relativity (Phase 4)
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.4.1 | Mercury perihelion precession | High | D.4.1 |
| N.4.2 | Gravitational light deflection | High | D.4.1 |
| N.4.3 | Gravitational redshift | High | D.3 |
| N.4.4 | Shapiro time delay | Medium | D.4.1 |
| N.4.5 | Frame-dragging (Gravity Probe B) | Medium | D.4.2 |
| N.4.6 | Gravitational wave detection (LIGO/Virgo) | High | D.7 |

### N.5: Precision Tests of the Standard Model (Phase 4)
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.5.1 | Electroweak precision tests (Z-pole, W mass) | Medium | E.4.1 |
| N.5.2 | QCD tests (jet physics, running coupling) | Medium | E.4.3 |
| N.5.3 | Higgs boson properties | Medium | E.4.2 |
| N.5.4 | Muon g-2 anomaly | High | E.3.1 |

### N.6: Predictions from Quantum Gravity Approaches (Phase 5)
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.6.1 | LQG predictions (discrete spectra, Immirzi parameter) | Medium | K.1 |
| N.6.2 | String theory predictions (extra dimensions, moduli) | Medium | K.2 |
| N.6.3 | Asymptotic safety predictions | Low | K.5 |
| N.6.4 | Causal set predictions | Low | K.3 |

### N.7: Quantum Gravity Phenomenology (Phase 5)
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.7.1 | Modified dispersion relations | Medium | K.11 |
| N.7.2 | Lorentz violation bounds | Medium | K.11 |
| N.7.3 | Gravitational decoherence | Medium | C.7, D.3 |

### N.8–N.10: Observational Cosmology and Astroparticle (Phase 6)
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.8.1 | CMB power spectrum | Medium | G.2.2 |
| N.8.2 | Baryon acoustic oscillations | Medium | G.6 |
| N.9.1 | Cosmic ray physics | Low | J.6 |
| N.9.2 | Neutrino astronomy | Low | J.1 |
| N.10.1 | Formalized experimental results with error bars | Medium | All |

**Hypothesis to formalize**: Formalizing experimental results as theorems with error bars creates a rigorous theory-experiment interface.

## Implementation Order

```
N.1 (Units) ──► N.2 (Constants) — START IMMEDIATELY
                     │
                     ├──► N.3 (QM Tests) — after Track C
                     ├──► N.4 (GR Tests) — after Track D
                     ├──► N.5 (SM Tests) — after Track E
                     ├──► N.6 (QG Predictions) — after Track K
                     ├──► N.7 (QG Phenomenology) — after Track K
                     └──► N.8–N.10 — after respective tracks
```

## Related Plans

- [Track A Plan](../A_mathematical_foundations/) — type system for units
- [Track C Plan](../C_quantum_mechanics/) — QM predictions to test
- [Track D Plan](../D_general_relativity/) — GR predictions to test
- [Track E Plan](../E_quantum_field_theory/) — SM predictions to test
- [Track K Plan](../K_quantum_gravity/) — QG predictions to test
- [Track G Plan](../G_cosmology/) — cosmological observations
