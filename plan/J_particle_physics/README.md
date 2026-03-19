# Plan: Track J — Particle Physics Phenomenology

[← Back to Plan Index](../README.md) | [ROADMAP Entry](../../ROADMAP/J_particle_physics.md) | [Execution Strategy](../EXECUTION_STRATEGY.md)

## Overview

Track J formalizes beyond-Standard-Model physics and connections to experiment. It depends on a mature Standard Model formalization from [Track E](../E_quantum_field_theory/).

## Dependencies

**Upstream**:
- [Track E](../E_quantum_field_theory/) — E.3 (gauge theories), E.4 (Standard Model)

**Downstream**:
- [Track G](../G_cosmology/) — dark matter candidates inform G.3
- [Track K](../K_quantum_gravity/) — GUTs and SUSY inform K
- [Track N](../N_experimental/) — predictions for collider and astroparticle experiments

**No conflicts with**: [Track H](../H_quantum_information/), [Track I](../I_condensed_matter/), [Track L](../L_mathematical_physics/)

## Task Breakdown

### J.1: Neutrino Physics
| Task | Description | Priority |
|------|-------------|----------|
| J.1.1 | Neutrino mass terms (Dirac and Majorana) | High |
| J.1.2 | Neutrino oscillations (PMNS matrix) | High |
| J.1.3 | Seesaw mechanism | Medium |

**Hypothesis to formalize**: Neutrinos are Majorana fermions and the seesaw mechanism explains their small masses.

### J.2: CP Violation and Matter-Antimatter Asymmetry
| Task | Description | Priority |
|------|-------------|----------|
| J.2.1 | CKM matrix and CP violation in quarks | High |
| J.2.2 | Strong CP problem | High |
| J.2.3 | Axions as solution to strong CP | High |
| J.2.4 | Baryogenesis (Sakharov conditions) | Medium |

**Hypothesis to formalize**: Axions solve the strong CP problem and constitute dark matter.

### J.3: Grand Unified Theories
| Task | Description | Priority |
|------|-------------|----------|
| J.3.1 | SU(5) GUT (Georgi-Glashow) | High |
| J.3.2 | SO(10) GUT | High |
| J.3.3 | Proton decay predictions | Medium |
| J.3.4 | Gauge coupling unification | Medium |

**Hypothesis to formalize**: Gauge couplings unify at the GUT scale (~10¹⁶ GeV).

### J.4: Supersymmetry
| Task | Description | Priority |
|------|-------------|----------|
| J.4.1 | SUSY algebra and superfields | High |
| J.4.2 | Minimal Supersymmetric Standard Model (MSSM) | High |
| J.4.3 | SUSY breaking mechanisms | Medium |
| J.4.4 | Naturalness and hierarchy problem | Medium |

### J.5: Extra Dimensions
| Task | Description | Priority |
|------|-------------|----------|
| J.5.1 | Kaluza-Klein theory | Medium |
| J.5.2 | Large extra dimensions (ADD) | Medium |
| J.5.3 | Warped extra dimensions (Randall-Sundrum) | Medium |

### J.6–J.9: Dark Matter, Flavor, Precision Tests, Collider
| Task | Description | Priority |
|------|-------------|----------|
| J.6.1 | WIMP dark matter | Medium |
| J.6.2 | Axion dark matter | Medium |
| J.7.1 | Flavor symmetries | Low |
| J.8.1 | Precision electroweak tests | Low |
| J.9.1 | Collider phenomenology | Low |

## Implementation Order

```
J.1 (Neutrinos) ──► J.2 (CP Violation) ──► J.6 (Dark Matter)
J.3 (GUTs) ──► J.4 (SUSY)
J.5 (Extra Dimensions) — independent
J.7–J.9 — can proceed in any order after E.4
```

## Related Plans

- [Track E Plan](../E_quantum_field_theory/) — provides Standard Model
- [Track G Plan](../G_cosmology/) — dark matter and baryogenesis
- [Track K Plan](../K_quantum_gravity/) — GUTs/SUSY inform quantum gravity
- [Track N Plan](../N_experimental/) — experimental predictions
