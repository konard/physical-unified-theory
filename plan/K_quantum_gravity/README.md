# Plan: Track K — Approaches to Quantum Gravity

[← Back to Plan Index](../README.md) | [ROADMAP Entry](../../ROADMAP/K_quantum_gravity.md) | [Execution Strategy](../EXECUTION_STRATEGY.md)

## Overview

Track K is the **convergence point** of the entire project — it formalizes all known approaches to unifying quantum mechanics and general relativity. It has the deepest dependency chain and represents the project's ultimate research goal.

## Dependencies

**Upstream** (extensive):
- [Track A](../A_mathematical_foundations/) — all sections (especially A.1, A.2, A.4, A.5)
- [Track C](../C_quantum_mechanics/) — C.1 (postulates)
- [Track D](../D_general_relativity/) — D.3 (Einstein equations), D.5 (singularity theorems), D.6 (ADM formalism)
- [Track E](../E_quantum_field_theory/) — E.1 (free fields), E.2 (interactions), E.3 (gauge theories)

**Informed by** (not hard dependencies but conceptually important):
- [Track F](../F_statistical_mechanics/) — F.6 (black hole thermodynamics), F.7 (spacetime thermodynamics)
- [Track H](../H_quantum_information/) — H.3 (error correction), H.5 (entanglement), H.6 (complexity)
- [Track I](../I_condensed_matter/) — I.6 (tensor networks), I.7 (emergent phenomena)
- [Track J](../J_particle_physics/) — J.3 (GUTs), J.4 (SUSY)
- [Track L](../L_mathematical_physics/) — L.1 (AQFT), L.2 (TQFT), L.3 (categories)

**Downstream**:
- [Track M](../M_hypotheses/) — speculative extensions
- [Track N](../N_experimental/) — N.6, N.7 (QG predictions and phenomenology)

## Task Breakdown

### K.0: The Incompatibility Problem
| Task | Description | Priority |
|------|-------------|----------|
| K.0.1 | Formal statement of QM-GR incompatibility | **Critical** |
| K.0.2 | Non-renormalizability of perturbative quantum gravity | **Critical** |
| K.0.3 | Problem of time | High |
| K.0.4 | Background independence requirement | High |

See [docs/UNIFICATION_CHALLENGES.md](../../docs/UNIFICATION_CHALLENGES.md) for background.

### K.1: Canonical Quantum Gravity
| Task | Description | Priority |
|------|-------------|----------|
| K.1.1 | Wheeler-DeWitt equation | High |
| K.1.2 | Loop quantum gravity (Ashtekar variables, holonomies) | High |
| K.1.3 | Spin networks and spin foams | High |
| K.1.4 | Loop quantum cosmology | Medium |
| K.1.5 | Discrete area and volume spectra | Medium |

**Hypothesis to formalize**: LQG correctly quantizes GR with discrete spectra for area and volume.

### K.2: String Theory and M-Theory
| Task | Description | Priority |
|------|-------------|----------|
| K.2.1 | Bosonic string (Nambu-Goto and Polyakov actions) | High |
| K.2.2 | Superstring theory (Type I, IIA, IIB, heterotic) | High |
| K.2.3 | Compactification (Calabi-Yau, flux) | Medium |
| K.2.4 | D-branes and gauge/gravity duality | High |
| K.2.5 | AdS/CFT correspondence | **Critical** |
| K.2.6 | String phenomenology and landscape | Medium |
| K.2.7 | Swampland conjectures | Medium |

**Hypothesis to formalize**: String theory is the correct theory of quantum gravity; the landscape admits physical selection.

### K.3: Causal Set Theory
| Task | Description | Priority |
|------|-------------|----------|
| K.3.1 | Causal set definition and partial order | High |
| K.3.2 | Hauptvermutung (manifold-likeness) | Medium |
| K.3.3 | Dynamics (sequential growth models) | Medium |

### K.4: Causal Dynamical Triangulations
| Task | Description | Priority |
|------|-------------|----------|
| K.4.1 | Simplicial quantum gravity | Medium |
| K.4.2 | Phase structure and emergent 4D | Medium |

### K.5: Asymptotic Safety
| Task | Description | Priority |
|------|-------------|----------|
| K.5.1 | Functional renormalization group for gravity | Medium |
| K.5.2 | Non-Gaussian fixed point | Medium |

### K.6–K.12: Additional Approaches
| Task | Description | Priority |
|------|-------------|----------|
| K.6.1 | Non-commutative geometry (Connes' spectral action) | Medium |
| K.7.1 | Twistor theory (Penrose) | Medium |
| K.8.1 | Emergent gravity (Verlinde, Jacobson) | Medium |
| K.9.1 | Group field theory and tensor models | Low |
| K.10.1 | Hořava-Lifshitz gravity | Low |
| K.11.1 | Quantum gravity phenomenology (predictions) | Medium |
| K.12.1 | Other approaches (supergravity, higher-spin, etc.) | Low |

## Implementation Order

```
K.0 (Incompatibility) ──► K.1 (Canonical QG) ──► K.1.4 (LQC)
                     ──► K.2 (String Theory) ──► K.2.5 (AdS/CFT)
                     ──► K.3 (Causal Sets)
                     ──► K.4 (CDT)
                     ──► K.5 (Asymptotic Safety)

K.6–K.12 can proceed independently after K.0
K.11 (Phenomenology) depends on progress in K.1–K.10
```

## Phasing

- **Phase 5**: K.0–K.5 (core approaches)
- **Phase 6**: K.6–K.12 (additional approaches and integration)

## Related Plans

- [Track C Plan](../C_quantum_mechanics/) — one pillar of the incompatibility
- [Track D Plan](../D_general_relativity/) — the other pillar
- [Track E Plan](../E_quantum_field_theory/) — QFT foundations for QG
- [Track F Plan](../F_statistical_mechanics/) — black hole thermodynamics bridge
- [Track H Plan](../H_quantum_information/) — holographic connections
- [Track I Plan](../I_condensed_matter/) — tensor networks and emergence
- [Track L Plan](../L_mathematical_physics/) — rigorous mathematical frameworks
- [Track M Plan](../M_hypotheses/) — speculative directions
- [Track N Plan](../N_experimental/) — experimental predictions
- [docs/UNIFICATION_CHALLENGES.md](../../docs/UNIFICATION_CHALLENGES.md) — Background on the incompatibility
