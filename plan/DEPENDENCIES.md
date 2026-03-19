# Dependency Graph and Analysis

[← Back to Plan Index](README.md)

This document maps all inter-track and intra-track dependencies to enable conflict-free parallel execution.

## Full Dependency Graph

```
Track A (Mathematical Foundations) ─── ROOT, NO DEPENDENCIES
  │
  ├─► Track B (Classical Physics) ─────────── requires A.1, A.2
  │     ├─► Track F (Statistical Mechanics) ── requires A.1, A.5, B.7, C.1
  │     │     ├─► Track G (Cosmology) ──────── requires D.3, D.4, E.4, F.1
  │     │     └─► Track I (Condensed Matter) ── requires A.1, A.4, C.9, F.2, F.3
  │     └─► Track D (General Relativity) ───── requires A.2, A.6, B.2, B.3
  │           ├─► Track G (Cosmology)
  │           └─► Track K (Quantum Gravity) ◄── CONVERGENCE POINT
  │
  ├─► Track C (Quantum Mechanics) ─────────── requires A.1, A.5
  │     ├─► Track H (Quantum Information) ─── requires A.1, C.1, C.6, C.7
  │     ├─► Track I (Condensed Matter) ◄────── also needs C.9
  │     ├─► Track O (Foundations) ──────────── requires C.1, C.6, D.1, D.5
  │     └─► Track E (Quantum Field Theory) ── requires A.1-A.5, C.1, C.9, D.1
  │           ├─► Track J (Particle Physics) ── requires E.3, E.4
  │           └─► Track K (Quantum Gravity) ◄── also needs E.1, E.2, E.3
  │
  ├─► Track L (Mathematical Physics) ──────── requires A (all), C.1, D.3, E.1, E.3
  │
  ├─► Track M (Hypotheses) ────────────────── cross-cutting, all tracks inform
  ├─► Track N (Experimental) ──────────────── cross-cutting, all tracks inform
  └─► Track O (Foundations) ───────────────── requires C, D
```

## Dependency Matrix

Each cell shows what the **row** track requires from the **column** track.

| Requires → | A | B | C | D | E | F | G | H | I | J | K | L | M | N | O |
|------------|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **A** | — | | | | | | | | | | | | | | |
| **B** | A.1, A.2 | — | | | | | | | | | | | | | |
| **C** | A.1, A.5 | | — | | | | | | | | | | | | |
| **D** | A.2, A.6 | B.2, B.3 | | — | | | | | | | | | | | |
| **E** | A.1–A.5 | | C.1, C.9 | D.1 | — | | | | | | | | | | |
| **F** | A.1, A.5 | B.7 | C.1 | | | — | | | | | | | | | |
| **G** | | | | D.3, D.4 | E.4 | F.1 | — | | | | | | | | |
| **H** | A.1 | | C.1, C.6, C.7 | | | | | — | | | | | | | |
| **I** | A.1, A.4 | | C.9 | | | F.2, F.3 | | | — | | | | | | |
| **J** | | | | | E.3, E.4 | | | | | — | | | | | |
| **K** | all | | C.1 | D.3, D.5, D.6 | E.1–E.3 | | | | | | — | | | | |
| **L** | all | | C.1 | D.3 | E.1, E.3 | | | | | | | — | | | |
| **M** | all tracks inform | | | | | | | | | | | | — | | |
| **N** | A.1 | | various | various | various | | | | | | | | | — | |
| **O** | | | C.1, C.6 | D.1, D.5 | | | | | | | | | | | — |

## Critical Path Analysis

The **critical path** (longest dependency chain) determines the minimum sequential work:

```
A.1–A.2 → B.2–B.3 → D.3 → K (Quantum Gravity)
A.1–A.5 → C.1–C.9 → E.1–E.3 → K (Quantum Gravity)
```

Both paths converge at **Track K**, making it the final integration point.

### Parallelizable Chains

These chains can proceed simultaneously once their immediate prerequisites are met:

| Chain | Prerequisites | Tracks |
|-------|---------------|--------|
| Classical → GR | A.1, A.2 | B → D → G |
| Quantum → QFT | A.1, A.5 | C → E → J |
| Quantum → Info | A.1 | C → H |
| Foundations → StatMech | A.1, A.5, B.7 | F → I |
| Math Physics | A (all) | L (independent) |
| Experimental basics | A.1 | N.1, N.2 (independent) |
| Foundations/Philosophy | C.1 | O (mostly independent) |

## Conflict Zones

Areas where multiple tracks may modify the same files or depend on the same definitions:

### High-Risk Conflicts

| Shared Resource | Tracks Involved | Mitigation |
|----------------|-----------------|------------|
| Hilbert space definitions | A.1, C.1, E.1, H.1 | Define in A.1 first; others import |
| Differential geometry | A.2, D.2, L.5 | Define in A.2 first; others extend |
| Tensor calculus | A.2, D.2, E.1 | Shared module in A.2 |
| Lie groups/algebras | A.4, E.3, K.1 | Define in A.4 first |
| Measure theory | A.5, C.8, E.2 | Define in A.5 first |

### Low-Risk Conflicts

| Shared Resource | Tracks Involved | Mitigation |
|----------------|-----------------|------------|
| Special relativity | D.1, E.1 | Define in D.1; E.1 imports |
| Thermodynamics laws | B.7, F.1 | Define in B.7; F.1 extends |
| Entanglement | C.6, H.5, I.6 | Define in C.6; others import |
| Symmetry groups | C.3, E.3, O.6 | Define in A.4/C.3; others import |

## Recommended Resolution Strategy

1. **Shared definitions go in the earliest track** in the dependency chain
2. **Later tracks import and extend**, never redefine
3. **Interface files** (e.g., `lean/PhysicalUnifiedTheory/Foundations/Interfaces/`) define shared types
4. **PRs touching shared modules** require review from maintainers of dependent tracks
5. **Track-specific files** stay in track-specific directories to avoid conflicts

## Related Documents

- [EXECUTION_STRATEGY.md](EXECUTION_STRATEGY.md) — Phased execution plan
- [README.md](README.md) — Plan index
- [ROADMAP.md](../ROADMAP.md) — Main roadmap
