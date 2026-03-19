# Plan: Track G — Cosmology and Astrophysics

[← Back to Plan Index](../README.md) | [ROADMAP Entry](../../ROADMAP/G_cosmology.md) | [Execution Strategy](../EXECUTION_STRATEGY.md)

## Overview

Track G formalizes large-scale physics of the universe, from the Big Bang to dark energy. It depends heavily on general relativity, quantum field theory, and statistical mechanics.

## Dependencies

**Upstream**:
- [Track D](../D_general_relativity/) — D.3 (Einstein equations), D.4 (FLRW solution)
- [Track E](../E_quantum_field_theory/) — E.4 (Standard Model, for particle cosmology)
- [Track F](../F_statistical_mechanics/) — F.1 (equilibrium stat mech)

**Downstream**:
- [Track K](../K_quantum_gravity/) — G.7 (quantum cosmology) informs K
- [Track M](../M_hypotheses/) — G informs speculative cosmological hypotheses
- [Track N](../N_experimental/) — G provides predictions for N.8 (cosmological observations)

**No conflicts with**: Most other tracks (separate directory)

## Task Breakdown

### G.1: Big Bang Cosmology
| Task | Description | Priority |
|------|-------------|----------|
| G.1.1 | FLRW dynamics (Friedmann equations) | **Critical** |
| G.1.2 | Cosmological redshift and Hubble's law | **Critical** |
| G.1.3 | Thermal history of the universe | High |
| G.1.4 | Big Bang nucleosynthesis | Medium |

### G.2: Inflation
| Task | Description | Priority |
|------|-------------|----------|
| G.2.1 | Slow-roll inflation (single scalar field) | High |
| G.2.2 | Inflationary perturbation theory | High |
| G.2.3 | Observational predictions (spectral index, tensor-to-scalar ratio) | High |
| G.2.4 | Eternal inflation | Medium |

**Hypothesis to formalize**: Cosmic inflation occurred and generated primordial perturbations that seeded structure.

### G.3: Dark Matter
| Task | Description | Priority |
|------|-------------|----------|
| G.3.1 | Evidence and observational constraints | High |
| G.3.2 | CDM model and structure formation | High |
| G.3.3 | Particle dark matter candidates (links to [Track J](../J_particle_physics/)) | Medium |

### G.4: Dark Energy and Cosmological Constant
| Task | Description | Priority |
|------|-------------|----------|
| G.4.1 | Cosmological constant problem | High |
| G.4.2 | Dark energy models (quintessence, w(z)) | Medium |
| G.4.3 | Observational constraints (SNe Ia, BAO, CMB) | Medium |

**Hypothesis to formalize**: The cosmological constant problem is the most important unsolved problem in physics.

### G.5–G.9: Advanced Cosmology
| Task | Description | Priority |
|------|-------------|----------|
| G.5.1 | Primordial gravitational waves | Medium |
| G.5.2 | Baryogenesis | Medium |
| G.6.1 | Linear perturbation theory and structure formation | Medium |
| G.7.1 | Wheeler-DeWitt equation for cosmology | Medium |
| G.7.2 | Hartle-Hawking no-boundary proposal | Low |
| G.8.1 | Astrophysical black holes | Low |
| G.9.1 | Cyclic and bouncing cosmologies | Low |

## Implementation Order

```
G.1 (Big Bang) ──► G.2 (Inflation) ──► G.5 (Primordial)
      │                                       │
      ├──► G.3 (Dark Matter)                  └──► G.6 (Structure Formation)
      ├──► G.4 (Dark Energy)
      └──► G.7 (Quantum Cosmology) — requires Track K progress
```

## Related Plans

- [Track D Plan](../D_general_relativity/) — provides GR foundations (FLRW, Einstein equations)
- [Track E Plan](../E_quantum_field_theory/) — particle physics for cosmology
- [Track F Plan](../F_statistical_mechanics/) — thermal physics
- [Track J Plan](../J_particle_physics/) — dark matter candidates
- [Track K Plan](../K_quantum_gravity/) — quantum cosmology
- [Track N Plan](../N_experimental/) — cosmological observations
