#!/bin/bash
# Script to create GitHub issues based on plan folder
# Creates parent track issues, sub-issues, and dependency relationships

set -e

REPO="konard/physical-unified-theory"
ISSUE_MAP_FILE="/tmp/gh-issue-solver-1773894909440/issue_map.txt"
> "$ISSUE_MAP_FILE"

create_issue() {
    local title="$1"
    local body="$2"
    local label="$3"

    local result
    if [ -n "$label" ]; then
        result=$(gh issue create --repo "$REPO" --title "$title" --body "$body" --label "$label" 2>&1)
    else
        result=$(gh issue create --repo "$REPO" --title "$title" --body "$body" 2>&1)
    fi

    # Extract issue number from URL
    local num=$(echo "$result" | grep -oP '\d+$')
    echo "$num"
}

get_issue_id() {
    local num="$1"
    gh api graphql -f query="{ repository(owner: \"konard\", name: \"physical-unified-theory\") { issue(number: $num) { id } } }" --jq '.data.repository.issue.id'
}

add_sub_issue() {
    local parent_num="$1"
    local child_num="$2"
    local parent_id=$(get_issue_id "$parent_num")
    local child_id=$(get_issue_id "$child_num")
    gh api graphql -f query="mutation { addSubIssue(input: { issueId: \"$parent_id\", subIssueId: \"$child_id\" }) { issue { id } } }" --silent 2>/dev/null || echo "Warning: Failed to add sub-issue $child_num to parent $parent_num"
}

add_blocked_by() {
    local issue_num="$1"
    local blocking_num="$2"
    local issue_id=$(get_issue_id "$issue_num")
    local blocking_id=$(get_issue_id "$blocking_num")
    gh api graphql -f query="mutation { addBlockedBy(input: { issueId: \"$issue_id\", blockingIssueId: \"$blocking_id\" }) { blockedByIssue { id } } }" --silent 2>/dev/null || echo "Warning: Failed to add dependency $blocking_num blocks $issue_num"
}

save_mapping() {
    local key="$1"
    local num="$2"
    echo "$key=$num" >> "$ISSUE_MAP_FILE"
}

get_mapping() {
    local key="$1"
    grep "^${key}=" "$ISSUE_MAP_FILE" | head -1 | cut -d= -f2
}

echo "=== Creating Parent Track Issues ==="

# Track A
echo "Creating Track A..."
A_NUM=$(create_issue "Track A: Mathematical Foundations" "$(cat <<'BODY'
## Overview

Track A provides the mathematical infrastructure required by **all other tracks**. It is the root of the dependency graph and must be the first track to deliver usable definitions.

**Status**: Foundation — can start immediately
**Dependencies**: None (root track)

## Sub-tasks

- **A.1**: Linear Algebra and Functional Analysis
- **A.2**: Differential Geometry
- **A.3**: Topology
- **A.4**: Algebra
- **A.5**: Measure Theory and Probability
- **A.6**: Partial Differential Equations

## Key Principles

- Track A first: all other tracks depend on A
- A.1.1 (Hilbert spaces) and A.2.1 (Manifolds) are the most critical starting points
- Each Lean formalization should have a corresponding Rocq formalization for cross-verification

## Implementation Order

```
A.1.1 (Hilbert spaces) → A.1.2 (Operators) → A.1.3 (Spectral theory)
A.2.1 (Manifolds) → A.2.2 (Tensors) → A.2.3 (Connections) → A.2.4 (Curvature)
A.5.1 (Measure) → A.5.2 (Probability)
A.4.1 (Lie groups) → A.4.2 (Representations)
All above can proceed in parallel.
```

See [plan/A_mathematical_foundations/README.md](plan/A_mathematical_foundations/README.md) for full details.
BODY
)" "enhancement")
save_mapping "A" "$A_NUM"
echo "  Track A: #$A_NUM"

# Track B
echo "Creating Track B..."
B_NUM=$(create_issue "Track B: Classical Physics" "$(cat <<'BODY'
## Overview

Track B formalizes classical mechanics and field theory. It serves as the foundation for general relativity (Track D) and statistical mechanics (Track F), and provides the classical limit that quantum theories must reproduce.

**Status**: Dependent — partially startable after A.1, A.2
**Upstream dependencies**: Track A (A.1, A.2)

## Sub-tasks

- **B.1**: Newtonian Mechanics
- **B.2**: Lagrangian Mechanics
- **B.3**: Hamiltonian Mechanics
- **B.4**: Symplectic Geometry
- **B.5**: Classical Electromagnetism
- **B.6**: Classical Field Theory
- **B.7**: Classical Thermodynamics
- **B.8–B.9**: Fluid Mechanics and Nonlinear Dynamics

## Implementation Order

```
B.1 (Newton) → B.2 (Lagrangian) → B.3 (Hamiltonian) → B.4 (Symplectic)
                └→ B.6 (Field Theory) → B.5 (Electromagnetism)
B.7 (Thermodynamics) can proceed independently
```

See [plan/B_classical_physics/README.md](plan/B_classical_physics/README.md) for full details.
BODY
)" "enhancement")
save_mapping "B" "$B_NUM"
echo "  Track B: #$B_NUM"

# Track C
echo "Creating Track C..."
C_NUM=$(create_issue "Track C: Quantum Mechanics" "$(cat <<'BODY'
## Overview

Track C formalizes non-relativistic quantum mechanics. It is one of the two pillars (alongside Track D) whose unification is the project's ultimate goal.

**Status**: Dependent — partially startable after A.1
**Upstream dependencies**: Track A (A.1, A.5)

## Sub-tasks

- **C.1**: Fundamental Postulates (most widely depended-upon deliverable)
- **C.2**: Exactly Solvable Systems
- **C.3**: Symmetries in Quantum Mechanics
- **C.4**: Approximation Methods
- **C.5**: Scattering Theory
- **C.6**: Composite Systems and Entanglement
- **C.7**: Open Quantum Systems
- **C.8**: Path Integral Formulation
- **C.9**: Second Quantization
- **C.10**: Quantum Chaos

## Implementation Order

```
C.1 (Postulates) → C.2 (Solvable Systems) → C.4 (Approximations) → C.5 (Scattering)
      ├→ C.3 (Symmetries)
      ├→ C.6 (Entanglement) → C.7 (Open Systems)
      ├→ C.8 (Path Integrals)
      └→ C.9 (Second Quantization)
```

See [plan/C_quantum_mechanics/README.md](plan/C_quantum_mechanics/README.md) for full details.
BODY
)" "enhancement")
save_mapping "C" "$C_NUM"
echo "  Track C: #$C_NUM"

# Track D
echo "Creating Track D..."
D_NUM=$(create_issue "Track D: General Relativity" "$(cat <<'BODY'
## Overview

Track D formalizes Einstein's theory of gravity. Together with Track C (Quantum Mechanics), it forms the two pillars whose unification is explored in Track K.

**Status**: Dependent — partially startable after A.2
**Upstream dependencies**: Track A (A.2, A.6), Track B (B.2, B.3)

## Sub-tasks

- **D.1**: Special Relativity
- **D.2**: Differential Geometry for GR
- **D.3**: Einstein's Field Equations
- **D.4**: Exact Solutions
- **D.5**: Singularity Theorems and Causal Structure
- **D.6**: ADM Formalism and Initial Value Problem
- **D.7**: Gravitational Waves
- **D.8**: Black Hole Physics
- **D.9–D.10**: Alternative Theories and Numerical Methods

## Implementation Order

```
D.1 (Special Relativity) → D.2 (DiffGeo for GR) → D.3 (Einstein Eqs) → D.4 (Solutions)
                                                     ├→ D.5 (Singularities)
                                                     ├→ D.6 (ADM)
                                                     ├→ D.7 (Grav Waves)
                                                     └→ D.8 (Black Holes)
```

See [plan/D_general_relativity/README.md](plan/D_general_relativity/README.md) for full details.
BODY
)" "enhancement")
save_mapping "D" "$D_NUM"
echo "  Track D: #$D_NUM"

# Track E
echo "Creating Track E..."
E_NUM=$(create_issue "Track E: Quantum Field Theory" "$(cat <<'BODY'
## Overview

Track E formalizes relativistic quantum theory, culminating in the Standard Model. It requires substantial prerequisites from Track A, Track C, and Track D.

**Status**: Dependent — cannot start immediately (needs A, C, D.1)
**Upstream dependencies**: Track A (A.1–A.5), Track C (C.1, C.9), Track D (D.1)

## Sub-tasks

- **E.1**: Free Field Theory
- **E.2**: Interacting Field Theory
- **E.3**: Gauge Theories
- **E.4**: The Standard Model
- **E.5–E.8**: Advanced Topics (Anomalies, Topology, CFT, EFT)

## Implementation Order

```
E.1 (Free Fields) → E.2 (Interactions) → E.3 (Gauge Theories) → E.4 (Standard Model)
                                           ├→ E.5 (Anomalies)
                                           ├→ E.6 (Topology)
                                           └→ E.7 (CFT)
E.8 (EFT) can start after E.2
```

See [plan/E_quantum_field_theory/README.md](plan/E_quantum_field_theory/README.md) for full details.
BODY
)" "enhancement")
save_mapping "E" "$E_NUM"
echo "  Track E: #$E_NUM"

# Track F
echo "Creating Track F..."
F_NUM=$(create_issue "Track F: Statistical Mechanics and Thermodynamics" "$(cat <<'BODY'
## Overview

Track F formalizes thermal physics, connecting microscopic quantum mechanics to macroscopic thermodynamics. It bridges to black hole physics and spacetime thermodynamics — key ingredients for Track K.

**Status**: Dependent — partially startable after A.1, A.5
**Upstream dependencies**: Track A (A.1, A.5), Track B (B.7), Track C (C.1)

## Sub-tasks

- **F.1**: Foundations of Statistical Mechanics
- **F.2**: Quantum Statistical Mechanics
- **F.3**: Phase Transitions and Critical Phenomena
- **F.4**: Entropy and Information
- **F.5**: Non-Equilibrium Statistical Mechanics
- **F.6**: Black Hole Thermodynamics (Phase 5, requires D.8)
- **F.7**: Thermodynamics of Spacetime (Phase 5, requires D.3)

## Implementation Order

```
F.1 (Ensembles) → F.2 (Quantum StatMech) → F.3 (Phase Transitions)
      └→ F.4 (Entropy)              └→ F.5 (Non-Equilibrium)
F.6 (BH Thermo) and F.7 (Spacetime Thermo) — Phase 5, after D.8
```

See [plan/F_statistical_mechanics/README.md](plan/F_statistical_mechanics/README.md) for full details.
BODY
)" "enhancement")
save_mapping "F" "$F_NUM"
echo "  Track F: #$F_NUM"

# Track G
echo "Creating Track G..."
G_NUM=$(create_issue "Track G: Cosmology and Astrophysics" "$(cat <<'BODY'
## Overview

Track G formalizes large-scale physics of the universe, from the Big Bang to dark energy. It depends heavily on general relativity, quantum field theory, and statistical mechanics.

**Status**: Dependent — cannot start immediately (needs D, E, F)
**Upstream dependencies**: Track D (D.3, D.4), Track E (E.4), Track F (F.1)

## Sub-tasks

- **G.1**: Big Bang Cosmology
- **G.2**: Inflation
- **G.3**: Dark Matter
- **G.4**: Dark Energy and Cosmological Constant
- **G.5–G.9**: Advanced Cosmology (Primordial GWs, Baryogenesis, Structure Formation, Quantum Cosmology, Cyclic)

## Implementation Order

```
G.1 (Big Bang) → G.2 (Inflation) → G.5 (Primordial) → G.6 (Structure)
      ├→ G.3 (Dark Matter)
      ├→ G.4 (Dark Energy)
      └→ G.7 (Quantum Cosmology) — requires Track K progress
```

See [plan/G_cosmology/README.md](plan/G_cosmology/README.md) for full details.
BODY
)" "enhancement")
save_mapping "G" "$G_NUM"
echo "  Track G: #$G_NUM"

# Track H
echo "Creating Track H..."
H_NUM=$(create_issue "Track H: Quantum Information and Computation" "$(cat <<'BODY'
## Overview

Track H formalizes quantum computing, communication, and information theory. It is relatively independent of other physics tracks (beyond quantum mechanics), making it a good early-start candidate.

**Status**: Dependent — partially startable after A.1, C.1
**Upstream dependencies**: Track A (A.1), Track C (C.1, C.6, C.7)

## Sub-tasks

- **H.1**: Quantum Circuits and Gates
- **H.2**: Quantum Algorithms
- **H.3**: Quantum Error Correction
- **H.4**: Quantum Cryptography
- **H.5**: Entanglement Theory
- **H.6**: Quantum Complexity Theory
- **H.7–H.8**: Channels and Thermodynamics

## Implementation Order

```
H.1 (Circuits/Gates) → H.2 (Algorithms) → H.6 (Complexity)
      ├→ H.3 (Error Correction) → H.4 (Cryptography)
      ├→ H.5 (Entanglement Theory)
      └→ H.7 (Channel Theory) → H.8 (Thermodynamics)
```

See [plan/H_quantum_information/README.md](plan/H_quantum_information/README.md) for full details.
BODY
)" "enhancement")
save_mapping "H" "$H_NUM"
echo "  Track H: #$H_NUM"

# Track I
echo "Creating Track I..."
I_NUM=$(create_issue "Track I: Condensed Matter and Many-Body Physics" "$(cat <<'BODY'
## Overview

Track I formalizes quantum many-body systems and emergent phenomena, from superconductivity to topological phases. It connects to quantum gravity through holographic duality and tensor networks.

**Status**: Dependent — cannot start immediately (needs C.9, F.2)
**Upstream dependencies**: Track A (A.1, A.4), Track C (C.9), Track F (F.2, F.3)

## Sub-tasks

- **I.1**: Second Quantization and Many-Body Techniques
- **I.2**: Superconductivity
- **I.3**: Topological Phases of Matter
- **I.4**: Quantum Magnetism
- **I.5**: Strongly Correlated Systems
- **I.6**: Tensor Networks and Entanglement
- **I.7**: Emergent Phenomena

## Implementation Order

```
I.1 (Many-Body) → I.2 (Superconductivity)
      ├→ I.3 (Topological Phases)
      ├→ I.4 (Magnetism)
      ├→ I.5 (Strongly Correlated)
      └→ I.6 (Tensor Networks) → I.7 (Emergent Phenomena)
```

See [plan/I_condensed_matter/README.md](plan/I_condensed_matter/README.md) for full details.
BODY
)" "enhancement")
save_mapping "I" "$I_NUM"
echo "  Track I: #$I_NUM"

# Track J
echo "Creating Track J..."
J_NUM=$(create_issue "Track J: Particle Physics Phenomenology" "$(cat <<'BODY'
## Overview

Track J formalizes beyond-Standard-Model physics and connections to experiment. It depends on a mature Standard Model formalization from Track E.

**Status**: Dependent — cannot start immediately (needs E.3, E.4)
**Upstream dependencies**: Track E (E.3, E.4)

## Sub-tasks

- **J.1**: Neutrino Physics
- **J.2**: CP Violation and Matter-Antimatter Asymmetry
- **J.3**: Grand Unified Theories
- **J.4**: Supersymmetry
- **J.5**: Extra Dimensions
- **J.6–J.9**: Dark Matter, Flavor, Precision Tests, Collider

## Implementation Order

```
J.1 (Neutrinos) → J.2 (CP Violation) → J.6 (Dark Matter)
J.3 (GUTs) → J.4 (SUSY)
J.5 (Extra Dimensions) — independent
J.7–J.9 — can proceed in any order after E.4
```

See [plan/J_particle_physics/README.md](plan/J_particle_physics/README.md) for full details.
BODY
)" "enhancement")
save_mapping "J" "$J_NUM"
echo "  Track J: #$J_NUM"

# Track K
echo "Creating Track K..."
K_NUM=$(create_issue "Track K: Approaches to Quantum Gravity" "$(cat <<'BODY'
## Overview

Track K is the **convergence point** of the entire project — it formalizes all known approaches to unifying quantum mechanics and general relativity. It has the deepest dependency chain and represents the project's ultimate research goal.

**Status**: Convergence — cannot start immediately (needs D, E, and many others)
**Upstream dependencies**: Track A (all), Track C (C.1), Track D (D.3, D.5, D.6), Track E (E.1–E.3)

## Sub-tasks

- **K.0**: The Incompatibility Problem
- **K.1**: Canonical Quantum Gravity
- **K.2**: String Theory and M-Theory
- **K.3**: Causal Set Theory
- **K.4**: Causal Dynamical Triangulations
- **K.5**: Asymptotic Safety
- **K.6–K.12**: Additional Approaches (NCG, Twistor, Emergent Gravity, GFT, Hořava-Lifshitz, Phenomenology, Others)

## Implementation Order

```
K.0 (Incompatibility) → K.1 (Canonical QG) → K.1.4 (LQC)
                       → K.2 (String Theory) → K.2.5 (AdS/CFT)
                       → K.3 (Causal Sets)
                       → K.4 (CDT)
                       → K.5 (Asymptotic Safety)
K.6–K.12 can proceed independently after K.0
```

See [plan/K_quantum_gravity/README.md](plan/K_quantum_gravity/README.md) for full details.
BODY
)" "enhancement")
save_mapping "K" "$K_NUM"
echo "  Track K: #$K_NUM"

# Track L
echo "Creating Track L..."
L_NUM=$(create_issue "Track L: Mathematical Physics and Structural Approaches" "$(cat <<'BODY'
## Overview

Track L formalizes advanced mathematical frameworks that provide alternative or rigorous formulations of physics. These are particularly relevant for placing quantum field theory and quantum gravity on solid mathematical footing.

**Status**: Dependent — partially startable after A
**Upstream dependencies**: Track A (all), Track C (C.1), Track D (D.3), Track E (E.1, E.3)

## Sub-tasks

- **L.1**: Algebraic Quantum Field Theory (AQFT)
- **L.2**: Topological Quantum Field Theory (TQFT)
- **L.3**: Category-Theoretic Physics
- **L.4**: Non-Commutative Geometry in Physics
- **L.5**: Geometric Quantization
- **L.6–L.10**: Advanced Frameworks (Integrable Systems, Operator Algebras, Index Theorems, Info Geometry, HoTT)

## Implementation Order

```
L.1 (AQFT) → L.7 (Operator Algebras)
L.2 (TQFT) → L.3 (Categories)
L.4 (NCG) — independent after A
L.5 (Geometric Quantization) — after B.4 (symplectic)
L.8 (Index Theorems) — after A.2, A.3
```

See [plan/L_mathematical_physics/README.md](plan/L_mathematical_physics/README.md) for full details.
BODY
)" "enhancement")
save_mapping "L" "$L_NUM"
echo "  Track L: #$L_NUM"

# Track M
echo "Creating Track M..."
M_NUM=$(create_issue "Track M: Hypotheses and Speculative Directions" "$(cat <<'BODY'
## Overview

Track M is a cross-cutting track that explores speculative and novel directions in theoretical physics. Unlike other tracks, it draws from **all** other tracks and does not have a strict sequential dependency — individual items can be explored as soon as the relevant foundations exist.

**Status**: Cross-cutting — partially startable (theory-driven)
**Upstream dependencies**: All tracks inform M (cross-cutting)

## Sub-tasks

- **M.1**: Novel Unification Proposals
- **M.2**: Discrete vs. Continuous Spacetime
- **M.3**: The Problem of Time
- **M.4**: The Measurement Problem and Gravity
- **M.5**: The Cosmological Constant Problem
- **M.6**: The Hierarchy Problem
- **M.7–M.11**: Further Speculative Directions (Multiverse, Consciousness, Simulation, Math Structures, Analog Models)

## Implementation Strategy

Track M does not follow a linear implementation order. Each item is explored when its prerequisites become available. Items are formalized as conjectures with precise statements.

See [plan/M_hypotheses/README.md](plan/M_hypotheses/README.md) for full details.
BODY
)" "enhancement")
save_mapping "M" "$M_NUM"
echo "  Track M: #$M_NUM"

# Track N
echo "Creating Track N..."
N_NUM=$(create_issue "Track N: Experimental Connections and Predictions" "$(cat <<'BODY'
## Overview

Track N bridges formal theory to observation. It formalizes units, constants, known experimental results, and predictions from each theoretical approach. Some items (N.1, N.2) can start immediately; others depend on the relevant physics tracks.

**Status**: Cross-cutting — partially startable (N.1, N.2 immediately)
**Upstream dependencies**: Track A (A.1); various physics tracks for later items

## Sub-tasks

- **N.1**: Units and Dimensional Analysis (Phase 1 — Immediate Start)
- **N.2**: Fundamental Constants (Phase 1 — Immediate Start)
- **N.3**: Precision Tests of Quantum Mechanics (Phase 4)
- **N.4**: Precision Tests of General Relativity (Phase 4)
- **N.5**: Precision Tests of the Standard Model (Phase 4)
- **N.6**: Predictions from Quantum Gravity Approaches (Phase 5)
- **N.7**: Quantum Gravity Phenomenology (Phase 5)
- **N.8–N.10**: Observational Cosmology and Astroparticle (Phase 6)

## Implementation Order

```
N.1 (Units) → N.2 (Constants) — START IMMEDIATELY
                 ├→ N.3 (QM Tests) — after Track C
                 ├→ N.4 (GR Tests) — after Track D
                 ├→ N.5 (SM Tests) — after Track E
                 ├→ N.6 (QG Predictions) — after Track K
                 └→ N.7–N.10 — after respective tracks
```

See [plan/N_experimental/README.md](plan/N_experimental/README.md) for full details.
BODY
)" "enhancement")
save_mapping "N" "$N_NUM"
echo "  Track N: #$N_NUM"

# Track O
echo "Creating Track O..."
O_NUM=$(create_issue "Track O: Foundations and Philosophy of Physics" "$(cat <<'BODY'
## Overview

Track O examines interpretational and foundational questions in physics. It formalizes different interpretations of quantum mechanics, the nature of spacetime, and the arrow of time. These questions become especially important when attempting unification (Track K).

**Status**: Dependent — partially startable after C.1
**Upstream dependencies**: Track C (C.1, C.6), Track D (D.1, D.5)

## Sub-tasks

- **O.1**: Quantum Measurement Problem
- **O.2**: Operational and Reconstructive Approaches
- **O.3**: Determinism and Indeterminism
- **O.4**: Nature of Spacetime
- **O.5**: The Arrow of Time
- **O.6**: Symmetry and Physical Ontology
- **O.7–O.9**: Laws, QG Foundations, Mathematics-Physics

## Implementation Order

```
O.1 (Measurement Problem) → O.8 (QG Foundations)
O.2 (Reconstructions) — independent after C.1
O.3 (Determinism) — independent after C.6
O.4 (Spacetime) — after D.3 and K progress
O.5 (Arrow of Time) — after F.1
O.6 (Symmetry) — after D.1, E.3
```

See [plan/O_foundations/README.md](plan/O_foundations/README.md) for full details.
BODY
)" "enhancement")
save_mapping "O" "$O_NUM"
echo "  Track O: #$O_NUM"

echo ""
echo "=== All parent track issues created ==="
cat "$ISSUE_MAP_FILE"
echo ""
echo "=== Creating Sub-issues ==="

# Now create sub-issues for each track

# ---- Track A sub-issues ----
echo "Creating Track A sub-issues..."

A1_NUM=$(create_issue "A.1: Linear Algebra and Functional Analysis" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| A.1.1 | Hilbert space definitions and basic properties | **Critical** |
| A.1.2 | Bounded and unbounded operators | **Critical** |
| A.1.3 | Spectral theory (spectral theorem, functional calculus) | High |
| A.1.4 | Distribution theory (Schwartz space, tempered distributions) | Medium |
| A.1.5 | Rigged Hilbert spaces (Gelfand triples) | Medium |

**Lean Directory**: `Foundations/LinearAlgebra.lean`, `Foundations/HilbertSpaces.lean`, `Foundations/Distributions.lean`
**Mathlib Status**: Partial (InnerProductSpace available)
**Hypothesis**: Rigged Hilbert spaces resolve continuous spectrum issues in QM (see Track C).

## Downstream consumers
- Track B, C, E, F, H, I, K, L, N all depend on A.1
BODY
)" "enhancement")
save_mapping "A.1" "$A1_NUM"

A2_NUM=$(create_issue "A.2: Differential Geometry" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| A.2.1 | Smooth manifolds and tangent bundles | **Critical** |
| A.2.2 | Tensor fields and tensor calculus | **Critical** |
| A.2.3 | Connections and covariant derivatives | High |
| A.2.4 | Curvature (Riemann, Ricci, scalar) | High |
| A.2.5 | Fiber bundles (principal, associated, vector) | High |
| A.2.6 | Lorentzian geometry and causal structure | High |

**Lean Directory**: `Foundations/DifferentialGeometry.lean`, `Foundations/FiberBundles.lean`
**Hypothesis**: Fiber bundle theory provides a unified framework for gauge theories and GR.

## Downstream consumers
- Track B, D, E, K, L depend on A.2
BODY
)" "enhancement")
save_mapping "A.2" "$A2_NUM"

A3_NUM=$(create_issue "A.3: Topology" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| A.3.1 | Topological spaces and continuity (Mathlib available) | Medium |
| A.3.2 | Algebraic topology (fundamental group, homology) | Medium |
| A.3.3 | Topological invariants relevant to physics (Chern, Pontryagin) | Medium |
BODY
)" "enhancement")
save_mapping "A.3" "$A3_NUM"

A4_NUM=$(create_issue "A.4: Algebra" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| A.4.1 | Lie groups and Lie algebras | **Critical** |
| A.4.2 | Representation theory | High |
| A.4.3 | Clifford algebras and spinors | High |
| A.4.4 | Category theory foundations | Medium |

**Hypothesis**: C*-algebras provide the correct mathematical framework for QM (see Track L).

## Downstream consumers
- Track E, I, K, L depend on A.4
BODY
)" "enhancement")
save_mapping "A.4" "$A4_NUM"

A5_NUM=$(create_issue "A.5: Measure Theory and Probability" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| A.5.1 | Measure spaces and integration (Mathlib available) | **Critical** |
| A.5.2 | Probability theory foundations | High |
| A.5.3 | Functional integration (path integrals) | High |
| A.5.4 | Stochastic processes | Medium |

**Hypothesis**: Rigorous path integrals can be constructed in 4D via constructive QFT methods (see Track E).

## Downstream consumers
- Track C, E, F depend on A.5
BODY
)" "enhancement")
save_mapping "A.5" "$A5_NUM"

A6_NUM=$(create_issue "A.6: Partial Differential Equations" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| A.6.1 | Linear PDEs (elliptic, parabolic, hyperbolic) | High |
| A.6.2 | Nonlinear PDEs | Medium |
| A.6.3 | Geometric PDEs (Ricci flow, Yang-Mills flow) | Medium |

## Downstream consumers
- Track D depends on A.6
BODY
)" "enhancement")
save_mapping "A.6" "$A6_NUM"

# ---- Track B sub-issues ----
echo "Creating Track B sub-issues..."

B1_NUM=$(create_issue "B.1: Newtonian Mechanics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| B.1.1 | Newton's laws as axioms | High |
| B.1.2 | Conservation laws (energy, momentum, angular momentum) | High |
| B.1.3 | Central force problems | Medium |

**Upstream**: Requires A.1 (linear algebra), A.2 (differential geometry)
BODY
)" "enhancement")
save_mapping "B.1" "$B1_NUM"

B2_NUM=$(create_issue "B.2: Lagrangian Mechanics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| B.2.1 | Principle of least action | **Critical** |
| B.2.2 | Euler-Lagrange equations | **Critical** |
| B.2.3 | Noether's theorem | **Critical** |
| B.2.4 | Constrained systems | Medium |

**Key output**: B.2.1–B.2.3 are required by Track D (Einstein-Hilbert action).
BODY
)" "enhancement")
save_mapping "B.2" "$B2_NUM"

B3_NUM=$(create_issue "B.3: Hamiltonian Mechanics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| B.3.1 | Legendre transform and Hamilton's equations | **Critical** |
| B.3.2 | Canonical transformations | High |
| B.3.3 | Hamilton-Jacobi theory | Medium |

**Key output**: B.3.1 is required by Track D (ADM formalism).
BODY
)" "enhancement")
save_mapping "B.3" "$B3_NUM"

B4_NUM=$(create_issue "B.4: Symplectic Geometry" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| B.4.1 | Symplectic manifolds and Poisson brackets | High |
| B.4.2 | Liouville's theorem | High |
| B.4.3 | Geometric quantization connection | Medium |

**Hypothesis**: Geometric quantization provides a rigorous path from classical to quantum (see Track L).
BODY
)" "enhancement")
save_mapping "B.4" "$B4_NUM"

B5_NUM=$(create_issue "B.5: Classical Electromagnetism" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| B.5.1 | Maxwell's equations in differential form | High |
| B.5.2 | Gauge invariance (U(1)) | High |
| B.5.3 | Electromagnetic energy-momentum tensor | High |
BODY
)" "enhancement")
save_mapping "B.5" "$B5_NUM"

B6_NUM=$(create_issue "B.6: Classical Field Theory" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| B.6.1 | Field Lagrangian and Euler-Lagrange for fields | High |
| B.6.2 | Noether's theorem for fields | High |
| B.6.3 | Energy-momentum tensor | High |
BODY
)" "enhancement")
save_mapping "B.6" "$B6_NUM"

B7_NUM=$(create_issue "B.7: Classical Thermodynamics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| B.7.1 | Laws of thermodynamics (0th through 3rd) | High |
| B.7.2 | Thermodynamic potentials | Medium |
| B.7.3 | Phase equilibria | Medium |

**Key output**: B.7.1 is required by Track F (Statistical Mechanics).
BODY
)" "enhancement")
save_mapping "B.7" "$B7_NUM"

B89_NUM=$(create_issue "B.8–B.9: Fluid Mechanics and Nonlinear Dynamics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| B.8.1 | Navier-Stokes equations | Medium |
| B.8.2 | Relativistic fluid dynamics | Medium |
| B.9.1 | Hamiltonian chaos and KAM theory | Low |
BODY
)" "enhancement")
save_mapping "B.89" "$B89_NUM"

# ---- Track C sub-issues ----
echo "Creating Track C sub-issues..."

C1_NUM=$(create_issue "C.1: Fundamental Postulates of Quantum Mechanics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| C.1.1 | State space axiom (Hilbert space, density operators) | **Critical** |
| C.1.2 | Observable axiom (self-adjoint operators) | **Critical** |
| C.1.3 | Measurement axiom (Born rule, projection postulate) | **Critical** |
| C.1.4 | Time evolution (Schrödinger equation, unitary evolution) | **Critical** |
| C.1.5 | Composite systems (tensor products) | **Critical** |

**Key output**: C.1 is the most widely depended-upon deliverable in the entire project.

## Downstream consumers
Track E, H, I, K, L, O all depend on C.1
BODY
)" "enhancement")
save_mapping "C.1" "$C1_NUM"

C2_NUM=$(create_issue "C.2: Exactly Solvable Quantum Systems" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| C.2.1 | Finite-dimensional systems (spin-1/2, qubits) | **Critical** |
| C.2.2 | Quantum harmonic oscillator (creation/annihilation operators) | **Critical** |
| C.2.3 | Hydrogen atom (Coulomb problem) | High |
| C.2.4 | Particle in a box and other 1D problems | High |
| C.2.5 | Angular momentum and spin | High |
BODY
)" "enhancement")
save_mapping "C.2" "$C2_NUM"

C3_NUM=$(create_issue "C.3: Symmetries in Quantum Mechanics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| C.3.1 | Wigner's theorem (symmetries as unitary/antiunitary operators) | High |
| C.3.2 | Rotation group SO(3) and SU(2) representations | High |
| C.3.3 | Translation symmetry and momentum | High |
| C.3.4 | Time-reversal symmetry | Medium |

**Hypothesis**: Superselection structure is determined by symmetry groups.
BODY
)" "enhancement")
save_mapping "C.3" "$C3_NUM"

C4_NUM=$(create_issue "C.4: Approximation Methods" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| C.4.1 | Time-independent perturbation theory | High |
| C.4.2 | Time-dependent perturbation theory (Fermi's golden rule) | High |
| C.4.3 | Variational method | Medium |
| C.4.4 | WKB approximation | Medium |
| C.4.5 | Adiabatic theorem and Berry phase | Medium |
BODY
)" "enhancement")
save_mapping "C.4" "$C4_NUM"

C5_NUM=$(create_issue "C.5: Scattering Theory" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| C.5.1 | S-matrix and T-matrix | High |
| C.5.2 | Born approximation | Medium |
| C.5.3 | Partial wave analysis | Medium |
BODY
)" "enhancement")
save_mapping "C.5" "$C5_NUM"

C6_NUM=$(create_issue "C.6: Composite Systems and Entanglement" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| C.6.1 | Tensor product spaces | **Critical** |
| C.6.2 | Entanglement (Bell states, Schmidt decomposition) | **Critical** |
| C.6.3 | Bell inequalities and non-locality | High |
| C.6.4 | Entanglement measures | Medium |

**Key output**: C.6 is required by Track H (Quantum Information) and Track O (Foundations).
**Hypothesis**: Entanglement is fundamental to spacetime emergence (see Track K, Track M).
BODY
)" "enhancement")
save_mapping "C.6" "$C6_NUM"

C7_NUM=$(create_issue "C.7: Open Quantum Systems" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| C.7.1 | Density matrices and mixed states | High |
| C.7.2 | Quantum channels (CPTP maps) | High |
| C.7.3 | Lindblad master equation | High |
| C.7.4 | Decoherence | Medium |
BODY
)" "enhancement")
save_mapping "C.7" "$C7_NUM"

C8_NUM=$(create_issue "C.8: Path Integral Formulation" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| C.8.1 | Feynman path integral (non-relativistic) | Medium |
| C.8.2 | Connection to operator formalism | Medium |
BODY
)" "enhancement")
save_mapping "C.8" "$C8_NUM"

C9_NUM=$(create_issue "C.9: Second Quantization" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| C.9.1 | Fock space construction | **Critical** |
| C.9.2 | Creation and annihilation operators | **Critical** |
| C.9.3 | Bosonic and fermionic statistics | **Critical** |

**Key output**: C.9 is required by Track E (QFT) and Track I (Condensed Matter).
BODY
)" "enhancement")
save_mapping "C.9" "$C9_NUM"

C10_NUM=$(create_issue "C.10: Quantum Chaos" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| C.10.1 | Random matrix theory | Low |
| C.10.2 | Level statistics | Low |
BODY
)" "enhancement")
save_mapping "C.10" "$C10_NUM"

# ---- Track D sub-issues ----
echo "Creating Track D sub-issues..."

D1_NUM=$(create_issue "D.1: Special Relativity" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| D.1.1 | Minkowski spacetime and metric | **Critical** |
| D.1.2 | Lorentz transformations and Lorentz group | **Critical** |
| D.1.3 | Four-vectors and relativistic kinematics | **Critical** |
| D.1.4 | Relativistic energy-momentum | High |

**Key output**: D.1 is required by Track E (relativistic QFT).
BODY
)" "enhancement")
save_mapping "D.1" "$D1_NUM"

D2_NUM=$(create_issue "D.2: Differential Geometry for GR" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| D.2.1 | Pseudo-Riemannian manifolds | **Critical** |
| D.2.2 | Levi-Civita connection | **Critical** |
| D.2.3 | Geodesic equation | **Critical** |
| D.2.4 | Riemann curvature tensor | **Critical** |
| D.2.5 | Ricci tensor and scalar curvature | **Critical** |
BODY
)" "enhancement")
save_mapping "D.2" "$D2_NUM"

D3_NUM=$(create_issue "D.3: Einstein's Field Equations" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| D.3.1 | Einstein tensor | **Critical** |
| D.3.2 | Stress-energy tensor | **Critical** |
| D.3.3 | Einstein field equations (with cosmological constant) | **Critical** |
| D.3.4 | Einstein-Hilbert action and variational derivation | High |
| D.3.5 | Linearized gravity | High |
BODY
)" "enhancement")
save_mapping "D.3" "$D3_NUM"

D4_NUM=$(create_issue "D.4: Exact Solutions of Einstein Equations" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| D.4.1 | Schwarzschild solution (static spherically symmetric) | **Critical** |
| D.4.2 | Kerr solution (rotating black holes) | High |
| D.4.3 | FLRW metric (cosmological) | High |
| D.4.4 | Reissner-Nordström (charged black holes) | Medium |
| D.4.5 | Gravitational wave solutions (pp-waves) | Medium |

**Hypothesis**: Physically reasonable exact solutions follow a unified classification.
BODY
)" "enhancement")
save_mapping "D.4" "$D4_NUM"

D5_NUM=$(create_issue "D.5: Singularity Theorems and Causal Structure" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| D.5.1 | Causal structure (timelike, spacelike, null) | High |
| D.5.2 | Penrose-Hawking singularity theorems | High |
| D.5.3 | Penrose diagrams (conformal compactification) | Medium |
| D.5.4 | Cosmic censorship conjecture | Medium |

**Hypothesis**: Cosmic censorship holds — naked singularities do not form from generic initial data.
BODY
)" "enhancement")
save_mapping "D.5" "$D5_NUM"

D6_NUM=$(create_issue "D.6: ADM Formalism and Initial Value Problem" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| D.6.1 | 3+1 decomposition (lapse, shift, spatial metric) | High |
| D.6.2 | ADM Hamiltonian and momentum constraints | High |
| D.6.3 | Well-posedness of initial value problem | Medium |

**Key output**: D.6 is required by Track K (canonical quantum gravity).
BODY
)" "enhancement")
save_mapping "D.6" "$D6_NUM"

D7_NUM=$(create_issue "D.7: Gravitational Waves" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| D.7.1 | Linearized theory and wave equation | High |
| D.7.2 | Polarizations (plus and cross) | Medium |
| D.7.3 | Energy radiated (quadrupole formula) | Medium |
BODY
)" "enhancement")
save_mapping "D.7" "$D7_NUM"

D8_NUM=$(create_issue "D.8: Black Hole Physics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| D.8.1 | Event horizons and Killing horizons | High |
| D.8.2 | Black hole mechanics (four laws) | High |
| D.8.3 | Hawking radiation (semiclassical) | Medium |
| D.8.4 | Black hole entropy (Bekenstein-Hawking) | Medium |

**Hypothesis**: Black hole mechanics is identical to thermodynamics (see Track F).
BODY
)" "enhancement")
save_mapping "D.8" "$D8_NUM"

D910_NUM=$(create_issue "D.9–D.10: Alternative Theories and Numerical Methods" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| D.9.1 | f(R) gravity | Low |
| D.9.2 | Scalar-tensor theories (Brans-Dicke) | Low |
| D.10.1 | Numerical GR foundations | Low |
BODY
)" "enhancement")
save_mapping "D.910" "$D910_NUM"

# ---- Track E sub-issues ----
echo "Creating Track E sub-issues..."

E1_NUM=$(create_issue "E.1: Free Field Theory" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| E.1.1 | Free scalar field (Klein-Gordon equation) | **Critical** |
| E.1.2 | Free spinor field (Dirac equation) | **Critical** |
| E.1.3 | Free vector field (Proca and Maxwell) | High |
| E.1.4 | Canonical quantization of free fields | **Critical** |
| E.1.5 | Fock space and particle interpretation | **Critical** |

**Hypothesis**: Haag's theorem is resolvable through better understanding of the interaction picture.
BODY
)" "enhancement")
save_mapping "E.1" "$E1_NUM"

E2_NUM=$(create_issue "E.2: Interacting Field Theory" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| E.2.1 | Perturbation theory and Feynman diagrams | **Critical** |
| E.2.2 | Renormalization (UV divergences, regularization) | **Critical** |
| E.2.3 | Renormalization group | High |
| E.2.4 | Non-perturbative methods (instantons, lattice) | Medium |

**Hypothesis**: Yang-Mills mass gap is solvable via formalization (Millennium Prize).
BODY
)" "enhancement")
save_mapping "E.2" "$E2_NUM"

E3_NUM=$(create_issue "E.3: Gauge Theories" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| E.3.1 | Abelian gauge theory (QED) | **Critical** |
| E.3.2 | Non-Abelian gauge theory (Yang-Mills) | **Critical** |
| E.3.3 | BRST symmetry and ghost fields | High |
| E.3.4 | Gauge fixing and Faddeev-Popov procedure | High |
BODY
)" "enhancement")
save_mapping "E.3" "$E3_NUM"

E4_NUM=$(create_issue "E.4: The Standard Model" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| E.4.1 | Electroweak theory (SU(2) × U(1)) | High |
| E.4.2 | Higgs mechanism and spontaneous symmetry breaking | High |
| E.4.3 | QCD (SU(3) color) | High |
| E.4.4 | Full Standard Model gauge group SU(3) × SU(2) × U(1) | High |
| E.4.5 | Anomaly cancellation | Medium |

**Hypothesis**: The Standard Model gauge group is nearly uniquely determined by anomaly cancellation.
BODY
)" "enhancement")
save_mapping "E.4" "$E4_NUM"

E58_NUM=$(create_issue "E.5–E.8: Advanced QFT Topics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| E.5.1 | Chiral and gauge anomalies | Medium |
| E.6.1 | Topological aspects (instantons, monopoles, theta vacuum) | Medium |
| E.7.1 | Conformal field theory (2D and higher) | Medium |
| E.8.1 | Effective field theory framework | Medium |

**Hypothesis**: All QFTs are effective theories, each valid within an energy domain.
BODY
)" "enhancement")
save_mapping "E.58" "$E58_NUM"

# ---- Track F sub-issues ----
echo "Creating Track F sub-issues..."

F1_NUM=$(create_issue "F.1: Foundations of Statistical Mechanics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| F.1.1 | Microcanonical, canonical, grand canonical ensembles | **Critical** |
| F.1.2 | Partition functions and free energies | **Critical** |
| F.1.3 | Equivalence of ensembles in thermodynamic limit | High |
BODY
)" "enhancement")
save_mapping "F.1" "$F1_NUM"

F2_NUM=$(create_issue "F.2: Quantum Statistical Mechanics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| F.2.1 | Density matrix formulation | High |
| F.2.2 | Bose-Einstein and Fermi-Dirac statistics | **Critical** |
| F.2.3 | Bose-Einstein condensation | High |
| F.2.4 | KMS condition for thermal equilibrium | Medium |

**Hypothesis**: KMS condition characterizes thermal equilibrium in quantum field theory.
BODY
)" "enhancement")
save_mapping "F.2" "$F2_NUM"

F3_NUM=$(create_issue "F.3: Phase Transitions and Critical Phenomena" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| F.3.1 | Ising model and exact solutions | High |
| F.3.2 | Landau theory of phase transitions | High |
| F.3.3 | Renormalization group for critical phenomena | Medium |
| F.3.4 | Universality classes | Medium |

**Hypothesis**: Universality in critical phenomena arises from RG fixed points.
BODY
)" "enhancement")
save_mapping "F.3" "$F3_NUM"

F4_NUM=$(create_issue "F.4: Entropy and Information" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| F.4.1 | Boltzmann entropy and H-theorem | High |
| F.4.2 | Von Neumann entropy | High |
| F.4.3 | Shannon entropy and connections to physics | Medium |
| F.4.4 | Maximum entropy principle | Medium |
BODY
)" "enhancement")
save_mapping "F.4" "$F4_NUM"

F5_NUM=$(create_issue "F.5: Non-Equilibrium Statistical Mechanics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| F.5.1 | Boltzmann equation | Medium |
| F.5.2 | Linear response theory (Kubo formula) | Medium |
| F.5.3 | Fluctuation-dissipation theorem | Medium |
| F.5.4 | Jarzynski equality and Crooks theorem | Low |
BODY
)" "enhancement")
save_mapping "F.5" "$F5_NUM"

F6_NUM=$(create_issue "F.6: Black Hole Thermodynamics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| F.6.1 | Four laws of black hole mechanics | High |
| F.6.2 | Bekenstein-Hawking entropy | High |
| F.6.3 | Information paradox | High |
| F.6.4 | Page curve and unitarity | Medium |

**Note**: Requires Track D D.8 (black hole physics) — Phase 5 task.
**Hypothesis**: Black hole evaporation is unitary; the Page curve is correct.
BODY
)" "enhancement")
save_mapping "F.6" "$F6_NUM"

F7_NUM=$(create_issue "F.7: Thermodynamics of Spacetime" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| F.7.1 | Unruh effect | Medium |
| F.7.2 | Jacobson's derivation of Einstein equations from thermodynamics | Medium |
| F.7.3 | Verlinde's entropic gravity | Low |

**Note**: Requires Track D D.3 — Phase 5 task.
**Hypothesis**: Einstein equations can be derived from thermodynamic relations on local Rindler horizons.
BODY
)" "enhancement")
save_mapping "F.7" "$F7_NUM"

# ---- Track G sub-issues ----
echo "Creating Track G sub-issues..."

G1_NUM=$(create_issue "G.1: Big Bang Cosmology" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| G.1.1 | FLRW dynamics (Friedmann equations) | **Critical** |
| G.1.2 | Cosmological redshift and Hubble's law | **Critical** |
| G.1.3 | Thermal history of the universe | High |
| G.1.4 | Big Bang nucleosynthesis | Medium |
BODY
)" "enhancement")
save_mapping "G.1" "$G1_NUM"

G2_NUM=$(create_issue "G.2: Inflation" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| G.2.1 | Slow-roll inflation (single scalar field) | High |
| G.2.2 | Inflationary perturbation theory | High |
| G.2.3 | Observational predictions (spectral index, tensor-to-scalar ratio) | High |
| G.2.4 | Eternal inflation | Medium |

**Hypothesis**: Cosmic inflation occurred and generated primordial perturbations that seeded structure.
BODY
)" "enhancement")
save_mapping "G.2" "$G2_NUM"

G3_NUM=$(create_issue "G.3: Dark Matter" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| G.3.1 | Evidence and observational constraints | High |
| G.3.2 | CDM model and structure formation | High |
| G.3.3 | Particle dark matter candidates (links to Track J) | Medium |
BODY
)" "enhancement")
save_mapping "G.3" "$G3_NUM"

G4_NUM=$(create_issue "G.4: Dark Energy and Cosmological Constant" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| G.4.1 | Cosmological constant problem | High |
| G.4.2 | Dark energy models (quintessence, w(z)) | Medium |
| G.4.3 | Observational constraints (SNe Ia, BAO, CMB) | Medium |

**Hypothesis**: The cosmological constant problem is the most important unsolved problem in physics.
BODY
)" "enhancement")
save_mapping "G.4" "$G4_NUM"

G59_NUM=$(create_issue "G.5–G.9: Advanced Cosmology" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| G.5.1 | Primordial gravitational waves | Medium |
| G.5.2 | Baryogenesis | Medium |
| G.6.1 | Linear perturbation theory and structure formation | Medium |
| G.7.1 | Wheeler-DeWitt equation for cosmology | Medium |
| G.7.2 | Hartle-Hawking no-boundary proposal | Low |
| G.8.1 | Astrophysical black holes | Low |
| G.9.1 | Cyclic and bouncing cosmologies | Low |
BODY
)" "enhancement")
save_mapping "G.59" "$G59_NUM"

# ---- Track H sub-issues ----
echo "Creating Track H sub-issues..."

H1_NUM=$(create_issue "H.1: Quantum Circuits and Gates" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| H.1.1 | Qubit formalization (Bloch sphere representation) | **Critical** |
| H.1.2 | Single-qubit gates (Pauli, Hadamard, phase, T) | **Critical** |
| H.1.3 | Multi-qubit gates (CNOT, Toffoli, SWAP) | **Critical** |
| H.1.4 | Universal gate sets | High |
| H.1.5 | Circuit model of computation | High |
BODY
)" "enhancement")
save_mapping "H.1" "$H1_NUM"

H2_NUM=$(create_issue "H.2: Quantum Algorithms" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| H.2.1 | Deutsch-Jozsa algorithm | High |
| H.2.2 | Grover's search algorithm | High |
| H.2.3 | Shor's factoring algorithm | High |
| H.2.4 | Quantum simulation algorithms | Medium |
| H.2.5 | Variational quantum algorithms (VQE, QAOA) | Medium |
BODY
)" "enhancement")
save_mapping "H.2" "$H2_NUM"

H3_NUM=$(create_issue "H.3: Quantum Error Correction" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| H.3.1 | Quantum error correction basics (Knill-Laflamme conditions) | High |
| H.3.2 | Stabilizer formalism | High |
| H.3.3 | Surface codes | High |
| H.3.4 | Topological quantum error correction | Medium |

**Hypothesis**: Topological QEC connects to TQFT (Track L) and condensed matter (Track I).
BODY
)" "enhancement")
save_mapping "H.3" "$H3_NUM"

H4_NUM=$(create_issue "H.4: Quantum Cryptography" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| H.4.1 | BB84 protocol | High |
| H.4.2 | Security proofs | Medium |
| H.4.3 | Quantum key distribution | Medium |
BODY
)" "enhancement")
save_mapping "H.4" "$H4_NUM"

H5_NUM=$(create_issue "H.5: Entanglement Theory" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| H.5.1 | Entanglement measures (concurrence, negativity, entropy) | High |
| H.5.2 | Entanglement witnesses | Medium |
| H.5.3 | Entanglement area laws | Medium |
| H.5.4 | Multipartite entanglement | Medium |

**Hypothesis**: Entanglement area laws are fundamental to the gravity-information connection (see Track K).
BODY
)" "enhancement")
save_mapping "H.5" "$H5_NUM"

H68_NUM=$(create_issue "H.6–H.8: Complexity, Channels, and Thermodynamics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| H.6.1 | BQP and complexity classes | Medium |
| H.6.2 | Quantum computational supremacy | Medium |
| H.6.3 | Holographic complexity conjectures | Low |
| H.7.1 | Quantum channel capacity | Medium |
| H.7.2 | Quantum data processing inequality | Medium |
| H.8.1 | Quantum thermodynamic resource theory | Low |

**Hypothesis**: AdS/CFT is a quantum error-correcting code.
BODY
)" "enhancement")
save_mapping "H.68" "$H68_NUM"

# ---- Track I sub-issues ----
echo "Creating Track I sub-issues..."

I1_NUM=$(create_issue "I.1: Second Quantization and Many-Body Techniques" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| I.1.1 | Many-body Fock space (bosonic and fermionic) | **Critical** |
| I.1.2 | Mean-field theory (Hartree-Fock) | High |
| I.1.3 | Green's functions (single-particle, many-body) | High |
| I.1.4 | Feynman diagrams for condensed matter | Medium |
BODY
)" "enhancement")
save_mapping "I.1" "$I1_NUM"

I2_NUM=$(create_issue "I.2: Superconductivity" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| I.2.1 | BCS theory (Cooper pairs, gap equation) | High |
| I.2.2 | Ginzburg-Landau theory | High |
| I.2.3 | Type-I and Type-II superconductors | Medium |
| I.2.4 | Josephson effect | Medium |

**Hypothesis**: High-Tc superconductivity is explained by a single theoretical framework.
BODY
)" "enhancement")
save_mapping "I.2" "$I2_NUM"

I3_NUM=$(create_issue "I.3: Topological Phases of Matter" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| I.3.1 | Topological insulators (Z₂ classification) | High |
| I.3.2 | Integer quantum Hall effect (Chern number) | High |
| I.3.3 | Fractional quantum Hall effect | High |
| I.3.4 | Topological classification (ten-fold way) | Medium |
| I.3.5 | Anyons and topological order | Medium |

**Hypothesis**: Topological phase classification is governed by cobordism/K-theory.
BODY
)" "enhancement")
save_mapping "I.3" "$I3_NUM"

I45_NUM=$(create_issue "I.4–I.5: Quantum Magnetism and Strongly Correlated Systems" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| I.4.1 | Heisenberg model | Medium |
| I.4.2 | Spin waves and magnons | Medium |
| I.4.3 | Frustrated magnets and spin liquids | Low |
| I.5.1 | Hubbard model | Medium |
| I.5.2 | Kondo effect | Low |
| I.5.3 | Heavy fermions | Low |
BODY
)" "enhancement")
save_mapping "I.45" "$I45_NUM"

I6_NUM=$(create_issue "I.6: Tensor Networks and Entanglement" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| I.6.1 | Matrix product states (MPS) | High |
| I.6.2 | DMRG algorithm | Medium |
| I.6.3 | MERA (multiscale entanglement renormalization) | Medium |
| I.6.4 | Tensor network / holography connection | Medium |

**Hypothesis**: MERA encodes AdS geometry, realizing the holographic principle (see Track K).
BODY
)" "enhancement")
save_mapping "I.6" "$I6_NUM"

I7_NUM=$(create_issue "I.7: Emergent Phenomena" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| I.7.1 | Universality and effective theories | Medium |
| I.7.2 | Emergent gauge fields | Low |
| I.7.3 | Gravity as emergent phenomenon | Low |

**Hypothesis**: Gravity is emergent like elasticity — it arises from microscopic degrees of freedom.
BODY
)" "enhancement")
save_mapping "I.7" "$I7_NUM"

# ---- Track J sub-issues ----
echo "Creating Track J sub-issues..."

J1_NUM=$(create_issue "J.1: Neutrino Physics" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| J.1.1 | Neutrino mass terms (Dirac and Majorana) | High |
| J.1.2 | Neutrino oscillations (PMNS matrix) | High |
| J.1.3 | Seesaw mechanism | Medium |

**Hypothesis**: Neutrinos are Majorana fermions and the seesaw mechanism explains their small masses.
BODY
)" "enhancement")
save_mapping "J.1" "$J1_NUM"

J2_NUM=$(create_issue "J.2: CP Violation and Matter-Antimatter Asymmetry" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| J.2.1 | CKM matrix and CP violation in quarks | High |
| J.2.2 | Strong CP problem | High |
| J.2.3 | Axions as solution to strong CP | High |
| J.2.4 | Baryogenesis (Sakharov conditions) | Medium |

**Hypothesis**: Axions solve the strong CP problem and constitute dark matter.
BODY
)" "enhancement")
save_mapping "J.2" "$J2_NUM"

J3_NUM=$(create_issue "J.3: Grand Unified Theories" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| J.3.1 | SU(5) GUT (Georgi-Glashow) | High |
| J.3.2 | SO(10) GUT | High |
| J.3.3 | Proton decay predictions | Medium |
| J.3.4 | Gauge coupling unification | Medium |

**Hypothesis**: Gauge couplings unify at the GUT scale (~10¹⁶ GeV).
BODY
)" "enhancement")
save_mapping "J.3" "$J3_NUM"

J4_NUM=$(create_issue "J.4: Supersymmetry" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| J.4.1 | SUSY algebra and superfields | High |
| J.4.2 | Minimal Supersymmetric Standard Model (MSSM) | High |
| J.4.3 | SUSY breaking mechanisms | Medium |
| J.4.4 | Naturalness and hierarchy problem | Medium |
BODY
)" "enhancement")
save_mapping "J.4" "$J4_NUM"

J59_NUM=$(create_issue "J.5–J.9: Extra Dimensions, Dark Matter, Flavor, Precision, Collider" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| J.5.1 | Kaluza-Klein theory | Medium |
| J.5.2 | Large extra dimensions (ADD) | Medium |
| J.5.3 | Warped extra dimensions (Randall-Sundrum) | Medium |
| J.6.1 | WIMP dark matter | Medium |
| J.6.2 | Axion dark matter | Medium |
| J.7.1 | Flavor symmetries | Low |
| J.8.1 | Precision electroweak tests | Low |
| J.9.1 | Collider phenomenology | Low |
BODY
)" "enhancement")
save_mapping "J.59" "$J59_NUM"

# ---- Track K sub-issues ----
echo "Creating Track K sub-issues..."

K0_NUM=$(create_issue "K.0: The Incompatibility Problem" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| K.0.1 | Formal statement of QM-GR incompatibility | **Critical** |
| K.0.2 | Non-renormalizability of perturbative quantum gravity | **Critical** |
| K.0.3 | Problem of time | High |
| K.0.4 | Background independence requirement | High |

See [docs/UNIFICATION_CHALLENGES.md](docs/UNIFICATION_CHALLENGES.md) for background.
BODY
)" "enhancement")
save_mapping "K.0" "$K0_NUM"

K1_NUM=$(create_issue "K.1: Canonical Quantum Gravity" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| K.1.1 | Wheeler-DeWitt equation | High |
| K.1.2 | Loop quantum gravity (Ashtekar variables, holonomies) | High |
| K.1.3 | Spin networks and spin foams | High |
| K.1.4 | Loop quantum cosmology | Medium |
| K.1.5 | Discrete area and volume spectra | Medium |

**Hypothesis**: LQG correctly quantizes GR with discrete spectra for area and volume.
BODY
)" "enhancement")
save_mapping "K.1" "$K1_NUM"

K2_NUM=$(create_issue "K.2: String Theory and M-Theory" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| K.2.1 | Bosonic string (Nambu-Goto and Polyakov actions) | High |
| K.2.2 | Superstring theory (Type I, IIA, IIB, heterotic) | High |
| K.2.3 | Compactification (Calabi-Yau, flux) | Medium |
| K.2.4 | D-branes and gauge/gravity duality | High |
| K.2.5 | AdS/CFT correspondence | **Critical** |
| K.2.6 | String phenomenology and landscape | Medium |
| K.2.7 | Swampland conjectures | Medium |

**Hypothesis**: String theory is the correct theory of quantum gravity; the landscape admits physical selection.
BODY
)" "enhancement")
save_mapping "K.2" "$K2_NUM"

K35_NUM=$(create_issue "K.3–K.5: Causal Sets, CDT, Asymptotic Safety" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| K.3.1 | Causal set definition and partial order | High |
| K.3.2 | Hauptvermutung (manifold-likeness) | Medium |
| K.3.3 | Dynamics (sequential growth models) | Medium |
| K.4.1 | Simplicial quantum gravity | Medium |
| K.4.2 | Phase structure and emergent 4D | Medium |
| K.5.1 | Functional renormalization group for gravity | Medium |
| K.5.2 | Non-Gaussian fixed point | Medium |
BODY
)" "enhancement")
save_mapping "K.35" "$K35_NUM"

K612_NUM=$(create_issue "K.6–K.12: Additional QG Approaches" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| K.6.1 | Non-commutative geometry (Connes' spectral action) | Medium |
| K.7.1 | Twistor theory (Penrose) | Medium |
| K.8.1 | Emergent gravity (Verlinde, Jacobson) | Medium |
| K.9.1 | Group field theory and tensor models | Low |
| K.10.1 | Hořava-Lifshitz gravity | Low |
| K.11.1 | Quantum gravity phenomenology (predictions) | Medium |
| K.12.1 | Other approaches (supergravity, higher-spin, etc.) | Low |
BODY
)" "enhancement")
save_mapping "K.612" "$K612_NUM"

# ---- Track L sub-issues ----
echo "Creating Track L sub-issues..."

L1_NUM=$(create_issue "L.1: Algebraic Quantum Field Theory (AQFT)" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| L.1.1 | Haag-Kastler axioms (nets of operator algebras) | High |
| L.1.2 | Locally covariant QFT on curved spacetime | High |
| L.1.3 | DHR superselection theory | Medium |
| L.1.4 | Modular theory (Tomita-Takesaki) | Medium |

**Hypothesis**: AQFT provides the correct axiomatization; locally covariant formulation is natural for curved spacetime.
BODY
)" "enhancement")
save_mapping "L.1" "$L1_NUM"

L2_NUM=$(create_issue "L.2: Topological Quantum Field Theory (TQFT)" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| L.2.1 | Atiyah-Segal axioms | High |
| L.2.2 | Chern-Simons theory | High |
| L.2.3 | Witten-type and Schwarz-type TQFTs | Medium |
| L.2.4 | Topological invariants from TQFT | Medium |

**Hypothesis**: Every 3D TQFT arises from a modular tensor category.
BODY
)" "enhancement")
save_mapping "L.2" "$L2_NUM"

L35_NUM=$(create_issue "L.3–L.5: Categories, NCG, Geometric Quantization" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| L.3.1 | Functorial QFT (Atiyah-Segal, Baez-Dolan) | Medium |
| L.3.2 | Higher gauge theory and higher categories | Medium |
| L.3.3 | Categorical quantum mechanics (Abramsky-Coecke) | Medium |
| L.4.1 | Spectral triples and Connes' program | Medium |
| L.4.2 | Non-commutative Standard Model | Medium |
| L.4.3 | Spectral action principle | Medium |
| L.5.1 | Prequantization and polarization | Medium |
| L.5.2 | BV-BRST formalism | Medium |
| L.5.3 | Deformation quantization | Medium |
BODY
)" "enhancement")
save_mapping "L.35" "$L35_NUM"

L610_NUM=$(create_issue "L.6–L.10: Advanced Mathematical Frameworks" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority |
|------|-------------|----------|
| L.6.1 | Integrable systems and exact results | Low |
| L.7.1 | Von Neumann algebras (Type III₁ for QFT) | Medium |
| L.8.1 | Index theorems in physics (Atiyah-Singer) | Medium |
| L.9.1 | Information geometry | Low |
| L.10.1 | Homotopy type theory and physics | Low |

**Hypothesis**: HoTT provides a natural language for gauge equivalence and physics structures.
BODY
)" "enhancement")
save_mapping "L.610" "$L610_NUM"

# ---- Track M sub-issues ----
echo "Creating Track M sub-issues..."

M1_NUM=$(create_issue "M.1: Novel Unification Proposals" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| M.1.1 | Information-theoretic physics (it from bit, constructor theory) | Medium | C.1, H.5 |
| M.1.2 | Spacetime from entanglement (ER=EPR, tensor networks) | Medium | C.6, K.2.5 |
| M.1.3 | Amplituhedron and positive geometry | Low | E.2 |
BODY
)" "enhancement")
save_mapping "M.1" "$M1_NUM"

M2_NUM=$(create_issue "M.2: Discrete vs. Continuous Spacetime" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| M.2.1 | Discrete approaches (causal sets, digital physics) | Medium | K.3 |
| M.2.2 | Continuous approaches (NCG) | Medium | L.4 |
| M.2.3 | Formal comparison of discrete and continuous | Low | M.2.1, M.2.2 |
BODY
)" "enhancement")
save_mapping "M.2" "$M2_NUM"

M36_NUM=$(create_issue "M.3–M.6: Time, Measurement, Cosmological Constant, Hierarchy" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
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
BODY
)" "enhancement")
save_mapping "M.36" "$M36_NUM"

M711_NUM=$(create_issue "M.7–M.11: Speculative Directions" "$(cat <<'BODY'
## Tasks

| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| M.7.1 | String landscape and multiverse | Low | K.2.6 |
| M.7.2 | Eternal inflation and measure problem | Low | G.2.4 |
| M.8.1 | Consciousness and physics (Orch OR, IIT) | Low | C.1 |
| M.9.1 | Simulation hypothesis | Low | H.6 |
| M.10.1 | Exceptional mathematical structures in physics | Low | A.4 |
| M.10.2 | Number theory and physics | Low | A.4 |
| M.10.3 | Type theory and physical constraints | Low | L.10 |
| M.11.1 | Analog models (acoustic black holes) | Low | D.8, F.7 |
BODY
)" "enhancement")
save_mapping "M.711" "$M711_NUM"

# ---- Track N sub-issues ----
echo "Creating Track N sub-issues..."

N1_NUM=$(create_issue "N.1: Units and Dimensional Analysis" "$(cat <<'BODY'
## Tasks (Phase 1 — Immediate Start)

| Task | Description | Priority |
|------|-------------|----------|
| N.1.1 | SI unit system formalization | **Critical** |
| N.1.2 | Natural units (ℏ = c = 1) | **Critical** |
| N.1.3 | Planck units | High |
| N.1.4 | Dimensional analysis as type checking | High |
| N.1.5 | Unit conversion framework | High |

**Hypothesis**: Type-safe units can prevent dimensional errors at compile-time.
BODY
)" "enhancement")
save_mapping "N.1" "$N1_NUM"

N2_NUM=$(create_issue "N.2: Fundamental Constants" "$(cat <<'BODY'
## Tasks (Phase 1 — Immediate Start)

| Task | Description | Priority |
|------|-------------|----------|
| N.2.1 | Speed of light, Planck's constant, gravitational constant | **Critical** |
| N.2.2 | Fine structure constant | High |
| N.2.3 | Particle masses and coupling constants | Medium |
| N.2.4 | CODATA values with uncertainties | Medium |
BODY
)" "enhancement")
save_mapping "N.2" "$N2_NUM"

N35_NUM=$(create_issue "N.3–N.5: Precision Tests of QM, GR, and SM" "$(cat <<'BODY'
## Tasks (Phase 4)

### N.3: Precision Tests of Quantum Mechanics
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.3.1 | Hydrogen spectroscopy (Lamb shift) | High | C.2.3 |
| N.3.2 | Electron g-2 (anomalous magnetic moment) | High | C.4, E.3.1 |
| N.3.3 | Casimir effect | Medium | E.1 |
| N.3.4 | Bell test experiments | High | C.6.3 |

### N.4: Precision Tests of General Relativity
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.4.1 | Mercury perihelion precession | High | D.4.1 |
| N.4.2 | Gravitational light deflection | High | D.4.1 |
| N.4.3 | Gravitational redshift | High | D.3 |
| N.4.4 | Shapiro time delay | Medium | D.4.1 |
| N.4.5 | Frame-dragging (Gravity Probe B) | Medium | D.4.2 |
| N.4.6 | Gravitational wave detection (LIGO/Virgo) | High | D.7 |

### N.5: Precision Tests of the Standard Model
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.5.1 | Electroweak precision tests (Z-pole, W mass) | Medium | E.4.1 |
| N.5.2 | QCD tests (jet physics, running coupling) | Medium | E.4.3 |
| N.5.3 | Higgs boson properties | Medium | E.4.2 |
| N.5.4 | Muon g-2 anomaly | High | E.3.1 |
BODY
)" "enhancement")
save_mapping "N.35" "$N35_NUM"

N610_NUM=$(create_issue "N.6–N.10: QG Predictions, Phenomenology, Cosmological Observations" "$(cat <<'BODY'
## Tasks (Phase 5–6)

### N.6: Predictions from Quantum Gravity Approaches
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.6.1 | LQG predictions (discrete spectra, Immirzi parameter) | Medium | K.1 |
| N.6.2 | String theory predictions (extra dimensions, moduli) | Medium | K.2 |
| N.6.3 | Asymptotic safety predictions | Low | K.5 |
| N.6.4 | Causal set predictions | Low | K.3 |

### N.7: Quantum Gravity Phenomenology
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.7.1 | Modified dispersion relations | Medium | K.11 |
| N.7.2 | Lorentz violation bounds | Medium | K.11 |
| N.7.3 | Gravitational decoherence | Medium | C.7, D.3 |

### N.8–N.10: Observational Cosmology and Astroparticle
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| N.8.1 | CMB power spectrum | Medium | G.2.2 |
| N.8.2 | Baryon acoustic oscillations | Medium | G.6 |
| N.9.1 | Cosmic ray physics | Low | J.6 |
| N.9.2 | Neutrino astronomy | Low | J.1 |
| N.10.1 | Formalized experimental results with error bars | Medium | All |

**Hypothesis**: Formalizing experimental results as theorems with error bars creates a rigorous theory-experiment interface.
BODY
)" "enhancement")
save_mapping "N.610" "$N610_NUM"

# ---- Track O sub-issues ----
echo "Creating Track O sub-issues..."

O1_NUM=$(create_issue "O.1: Quantum Measurement Problem" "$(cat <<'BODY'
## Tasks (Phase 3)

| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| O.1.1 | Formal statement of the measurement problem | **Critical** | C.1 |
| O.1.2 | Copenhagen interpretation | High | C.1 |
| O.1.3 | Many-worlds interpretation (Everett) | High | C.1 |
| O.1.4 | Bohmian mechanics (pilot-wave theory) | High | C.1 |
| O.1.5 | Consistent histories | Medium | C.1 |
| O.1.6 | Relational quantum mechanics | Medium | C.1 |
| O.1.7 | QBism | Medium | C.1 |
| O.1.8 | Collapse theories (GRW, CSL) | Medium | C.1 |

**Hypothesis**: Different QM interpretations make different predictions in extreme regimes (gravity, cosmology).
BODY
)" "enhancement")
save_mapping "O.1" "$O1_NUM"

O2_NUM=$(create_issue "O.2: Operational and Reconstructive Approaches" "$(cat <<'BODY'
## Tasks (Phase 3)

| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| O.2.1 | Hardy's axioms for QM | High | C.1 |
| O.2.2 | Informational axioms (Chiribella et al.) | High | C.1 |
| O.2.3 | Generalized probabilistic theories (GPTs) | High | C.1 |
| O.2.4 | Quantum logic | Medium | A.4 |

**Hypothesis**: QM is uniquely derivable from information-theoretic axioms.
BODY
)" "enhancement")
save_mapping "O.2" "$O2_NUM"

O3_NUM=$(create_issue "O.3: Determinism and Indeterminism" "$(cat <<'BODY'
## Tasks (Phase 3)

| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| O.3.1 | Bell's theorem (formal proof and implications) | **Critical** | C.6 |
| O.3.2 | Kochen-Specker theorem | High | C.1 |
| O.3.3 | PBR theorem (reality of quantum state) | High | C.1 |
| O.3.4 | Free will theorem | Medium | C.6 |
| O.3.5 | Superdeterminism | Low | O.3.1 |

**Hypothesis**: Bell/Kochen-Specker/PBR constraints uniquely determine viable interpretations.
BODY
)" "enhancement")
save_mapping "O.3" "$O3_NUM"

O49_NUM=$(create_issue "O.4–O.9: Spacetime, Arrow of Time, Symmetry, QG Foundations" "$(cat <<'BODY'
## Tasks (Phase 3–5)

### O.4: Nature of Spacetime
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| O.4.1 | Substantivalism vs. relationalism | Medium | D.3 |
| O.4.2 | Hole argument (Einstein, Earman-Norton) | Medium | D.3 |
| O.4.3 | Emergent spacetime | Medium | K (various) |
| O.4.4 | Structural realism | Low | O.4.2 |

### O.5: The Arrow of Time
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| O.5.1 | Thermodynamic arrow (second law) | Medium | F.1, F.4 |
| O.5.2 | Cosmological arrow | Medium | G.1 |
| O.5.3 | Radiative arrow | Low | B.5 |
| O.5.4 | Quantum arrow (measurement irreversibility) | Medium | C.1, O.1 |

### O.6: Symmetry and Physical Ontology
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| O.6.1 | Wigner classification of particles | High | D.1, C.3 |
| O.6.2 | Gauge symmetry: physical vs. mathematical | Medium | E.3 |
| O.6.3 | Noether's theorem (physical interpretation) | Medium | B.2.3 |
| O.6.4 | CPT theorem | Medium | E.1 |

### O.7–O.9: Laws, QG Foundations, Mathematics-Physics
| Task | Description | Priority | Prerequisites |
|------|-------------|----------|---------------|
| O.7.1 | Nature of physical laws | Low | — |
| O.8.1 | Measurement problem in quantum gravity | Medium | O.1, K.0 |
| O.8.2 | Observables in quantum gravity | Medium | K.0 |
| O.8.3 | Relational approach to QG | Medium | O.1.6, K.0 |
| O.9.1 | Unreasonable effectiveness of mathematics | Low | — |

**Hypothesis**: QG foundational issues are QM interpretational problems amplified by background independence.
BODY
)" "enhancement")
save_mapping "O.49" "$O49_NUM"

echo ""
echo "=== All sub-issues created ==="
echo ""
echo "=== Adding sub-issue relationships ==="

# Add sub-issue relationships
echo "Linking Track A sub-issues..."
add_sub_issue "$A_NUM" "$A1_NUM"
add_sub_issue "$A_NUM" "$A2_NUM"
add_sub_issue "$A_NUM" "$A3_NUM"
add_sub_issue "$A_NUM" "$A4_NUM"
add_sub_issue "$A_NUM" "$A5_NUM"
add_sub_issue "$A_NUM" "$A6_NUM"

echo "Linking Track B sub-issues..."
add_sub_issue "$B_NUM" "$B1_NUM"
add_sub_issue "$B_NUM" "$B2_NUM"
add_sub_issue "$B_NUM" "$B3_NUM"
add_sub_issue "$B_NUM" "$B4_NUM"
add_sub_issue "$B_NUM" "$B5_NUM"
add_sub_issue "$B_NUM" "$B6_NUM"
add_sub_issue "$B_NUM" "$B7_NUM"
add_sub_issue "$B_NUM" "$B89_NUM"

echo "Linking Track C sub-issues..."
add_sub_issue "$C_NUM" "$C1_NUM"
add_sub_issue "$C_NUM" "$C2_NUM"
add_sub_issue "$C_NUM" "$C3_NUM"
add_sub_issue "$C_NUM" "$C4_NUM"
add_sub_issue "$C_NUM" "$C5_NUM"
add_sub_issue "$C_NUM" "$C6_NUM"
add_sub_issue "$C_NUM" "$C7_NUM"
add_sub_issue "$C_NUM" "$C8_NUM"
add_sub_issue "$C_NUM" "$C9_NUM"
add_sub_issue "$C_NUM" "$C10_NUM"

echo "Linking Track D sub-issues..."
add_sub_issue "$D_NUM" "$D1_NUM"
add_sub_issue "$D_NUM" "$D2_NUM"
add_sub_issue "$D_NUM" "$D3_NUM"
add_sub_issue "$D_NUM" "$D4_NUM"
add_sub_issue "$D_NUM" "$D5_NUM"
add_sub_issue "$D_NUM" "$D6_NUM"
add_sub_issue "$D_NUM" "$D7_NUM"
add_sub_issue "$D_NUM" "$D8_NUM"
add_sub_issue "$D_NUM" "$D910_NUM"

echo "Linking Track E sub-issues..."
add_sub_issue "$E_NUM" "$E1_NUM"
add_sub_issue "$E_NUM" "$E2_NUM"
add_sub_issue "$E_NUM" "$E3_NUM"
add_sub_issue "$E_NUM" "$E4_NUM"
add_sub_issue "$E_NUM" "$E58_NUM"

echo "Linking Track F sub-issues..."
add_sub_issue "$F_NUM" "$F1_NUM"
add_sub_issue "$F_NUM" "$F2_NUM"
add_sub_issue "$F_NUM" "$F3_NUM"
add_sub_issue "$F_NUM" "$F4_NUM"
add_sub_issue "$F_NUM" "$F5_NUM"
add_sub_issue "$F_NUM" "$F6_NUM"
add_sub_issue "$F_NUM" "$F7_NUM"

echo "Linking Track G sub-issues..."
add_sub_issue "$G_NUM" "$G1_NUM"
add_sub_issue "$G_NUM" "$G2_NUM"
add_sub_issue "$G_NUM" "$G3_NUM"
add_sub_issue "$G_NUM" "$G4_NUM"
add_sub_issue "$G_NUM" "$G59_NUM"

echo "Linking Track H sub-issues..."
add_sub_issue "$H_NUM" "$H1_NUM"
add_sub_issue "$H_NUM" "$H2_NUM"
add_sub_issue "$H_NUM" "$H3_NUM"
add_sub_issue "$H_NUM" "$H4_NUM"
add_sub_issue "$H_NUM" "$H5_NUM"
add_sub_issue "$H_NUM" "$H68_NUM"

echo "Linking Track I sub-issues..."
add_sub_issue "$I_NUM" "$I1_NUM"
add_sub_issue "$I_NUM" "$I2_NUM"
add_sub_issue "$I_NUM" "$I3_NUM"
add_sub_issue "$I_NUM" "$I45_NUM"
add_sub_issue "$I_NUM" "$I6_NUM"
add_sub_issue "$I_NUM" "$I7_NUM"

echo "Linking Track J sub-issues..."
add_sub_issue "$J_NUM" "$J1_NUM"
add_sub_issue "$J_NUM" "$J2_NUM"
add_sub_issue "$J_NUM" "$J3_NUM"
add_sub_issue "$J_NUM" "$J4_NUM"
add_sub_issue "$J_NUM" "$J59_NUM"

echo "Linking Track K sub-issues..."
add_sub_issue "$K_NUM" "$K0_NUM"
add_sub_issue "$K_NUM" "$K1_NUM"
add_sub_issue "$K_NUM" "$K2_NUM"
add_sub_issue "$K_NUM" "$K35_NUM"
add_sub_issue "$K_NUM" "$K612_NUM"

echo "Linking Track L sub-issues..."
add_sub_issue "$L_NUM" "$L1_NUM"
add_sub_issue "$L_NUM" "$L2_NUM"
add_sub_issue "$L_NUM" "$L35_NUM"
add_sub_issue "$L_NUM" "$L610_NUM"

echo "Linking Track M sub-issues..."
add_sub_issue "$M_NUM" "$M1_NUM"
add_sub_issue "$M_NUM" "$M2_NUM"
add_sub_issue "$M_NUM" "$M36_NUM"
add_sub_issue "$M_NUM" "$M711_NUM"

echo "Linking Track N sub-issues..."
add_sub_issue "$N_NUM" "$N1_NUM"
add_sub_issue "$N_NUM" "$N2_NUM"
add_sub_issue "$N_NUM" "$N35_NUM"
add_sub_issue "$N_NUM" "$N610_NUM"

echo "Linking Track O sub-issues..."
add_sub_issue "$O_NUM" "$O1_NUM"
add_sub_issue "$O_NUM" "$O2_NUM"
add_sub_issue "$O_NUM" "$O3_NUM"
add_sub_issue "$O_NUM" "$O49_NUM"

echo ""
echo "=== Adding dependency (blocked-by) relationships ==="

# Track-level dependencies
echo "Adding track-level dependencies..."

# B blocked by A
add_blocked_by "$B_NUM" "$A_NUM"
# C blocked by A
add_blocked_by "$C_NUM" "$A_NUM"
# D blocked by A and B
add_blocked_by "$D_NUM" "$A_NUM"
add_blocked_by "$D_NUM" "$B_NUM"
# E blocked by A, C, D
add_blocked_by "$E_NUM" "$A_NUM"
add_blocked_by "$E_NUM" "$C_NUM"
add_blocked_by "$E_NUM" "$D_NUM"
# F blocked by A, B, C
add_blocked_by "$F_NUM" "$A_NUM"
add_blocked_by "$F_NUM" "$B_NUM"
add_blocked_by "$F_NUM" "$C_NUM"
# G blocked by D, E, F
add_blocked_by "$G_NUM" "$D_NUM"
add_blocked_by "$G_NUM" "$E_NUM"
add_blocked_by "$G_NUM" "$F_NUM"
# H blocked by A, C
add_blocked_by "$H_NUM" "$A_NUM"
add_blocked_by "$H_NUM" "$C_NUM"
# I blocked by A, C, F
add_blocked_by "$I_NUM" "$A_NUM"
add_blocked_by "$I_NUM" "$C_NUM"
add_blocked_by "$I_NUM" "$F_NUM"
# J blocked by E
add_blocked_by "$J_NUM" "$E_NUM"
# K blocked by A, C, D, E
add_blocked_by "$K_NUM" "$A_NUM"
add_blocked_by "$K_NUM" "$C_NUM"
add_blocked_by "$K_NUM" "$D_NUM"
add_blocked_by "$K_NUM" "$E_NUM"
# L blocked by A, C, D, E
add_blocked_by "$L_NUM" "$A_NUM"
add_blocked_by "$L_NUM" "$C_NUM"
add_blocked_by "$L_NUM" "$D_NUM"
add_blocked_by "$L_NUM" "$E_NUM"
# O blocked by C, D
add_blocked_by "$O_NUM" "$C_NUM"
add_blocked_by "$O_NUM" "$D_NUM"

# Sub-issue level dependencies (key ones)
echo "Adding sub-issue level dependencies..."

# B.1 blocked by A.1, A.2
add_blocked_by "$B1_NUM" "$A1_NUM"
add_blocked_by "$B1_NUM" "$A2_NUM"
# B.2 blocked by B.1
add_blocked_by "$B2_NUM" "$B1_NUM"
# B.3 blocked by B.2
add_blocked_by "$B3_NUM" "$B2_NUM"
# B.4 blocked by B.3
add_blocked_by "$B4_NUM" "$B3_NUM"
# B.6 blocked by B.2
add_blocked_by "$B6_NUM" "$B2_NUM"
# B.5 blocked by B.6
add_blocked_by "$B5_NUM" "$B6_NUM"

# C.1 blocked by A.1, A.5
add_blocked_by "$C1_NUM" "$A1_NUM"
add_blocked_by "$C1_NUM" "$A5_NUM"
# C.2 blocked by C.1
add_blocked_by "$C2_NUM" "$C1_NUM"
# C.3 blocked by C.1
add_blocked_by "$C3_NUM" "$C1_NUM"
# C.4 blocked by C.2
add_blocked_by "$C4_NUM" "$C2_NUM"
# C.5 blocked by C.4
add_blocked_by "$C5_NUM" "$C4_NUM"
# C.6 blocked by C.1
add_blocked_by "$C6_NUM" "$C1_NUM"
# C.7 blocked by C.6
add_blocked_by "$C7_NUM" "$C6_NUM"
# C.8 blocked by C.1
add_blocked_by "$C8_NUM" "$C1_NUM"
# C.9 blocked by C.1
add_blocked_by "$C9_NUM" "$C1_NUM"

# D.1 blocked by A.2
add_blocked_by "$D1_NUM" "$A2_NUM"
# D.2 blocked by D.1, A.2
add_blocked_by "$D2_NUM" "$D1_NUM"
add_blocked_by "$D2_NUM" "$A2_NUM"
# D.3 blocked by D.2, B.2, B.3
add_blocked_by "$D3_NUM" "$D2_NUM"
add_blocked_by "$D3_NUM" "$B2_NUM"
add_blocked_by "$D3_NUM" "$B3_NUM"
# D.4 blocked by D.3
add_blocked_by "$D4_NUM" "$D3_NUM"
# D.5 blocked by D.3
add_blocked_by "$D5_NUM" "$D3_NUM"
# D.6 blocked by D.3
add_blocked_by "$D6_NUM" "$D3_NUM"
# D.7 blocked by D.3
add_blocked_by "$D7_NUM" "$D3_NUM"
# D.8 blocked by D.4
add_blocked_by "$D8_NUM" "$D4_NUM"

# E.1 blocked by C.1, C.9, D.1
add_blocked_by "$E1_NUM" "$C1_NUM"
add_blocked_by "$E1_NUM" "$C9_NUM"
add_blocked_by "$E1_NUM" "$D1_NUM"
# E.2 blocked by E.1
add_blocked_by "$E2_NUM" "$E1_NUM"
# E.3 blocked by E.2
add_blocked_by "$E3_NUM" "$E2_NUM"
# E.4 blocked by E.3
add_blocked_by "$E4_NUM" "$E3_NUM"

# F.1 blocked by A.1, A.5, B.7
add_blocked_by "$F1_NUM" "$A1_NUM"
add_blocked_by "$F1_NUM" "$A5_NUM"
add_blocked_by "$F1_NUM" "$B7_NUM"
# F.2 blocked by F.1, C.1
add_blocked_by "$F2_NUM" "$F1_NUM"
add_blocked_by "$F2_NUM" "$C1_NUM"
# F.3 blocked by F.2
add_blocked_by "$F3_NUM" "$F2_NUM"
# F.4 blocked by F.1
add_blocked_by "$F4_NUM" "$F1_NUM"
# F.5 blocked by F.2
add_blocked_by "$F5_NUM" "$F2_NUM"
# F.6 blocked by D.8
add_blocked_by "$F6_NUM" "$D8_NUM"
# F.7 blocked by D.3
add_blocked_by "$F7_NUM" "$D3_NUM"

# G.1 blocked by D.3, D.4, F.1
add_blocked_by "$G1_NUM" "$D3_NUM"
add_blocked_by "$G1_NUM" "$D4_NUM"
add_blocked_by "$G1_NUM" "$F1_NUM"
# G.2 blocked by G.1
add_blocked_by "$G2_NUM" "$G1_NUM"
# G.3 blocked by G.1
add_blocked_by "$G3_NUM" "$G1_NUM"
# G.4 blocked by G.1
add_blocked_by "$G4_NUM" "$G1_NUM"

# H.1 blocked by A.1, C.1
add_blocked_by "$H1_NUM" "$A1_NUM"
add_blocked_by "$H1_NUM" "$C1_NUM"
# H.2 blocked by H.1
add_blocked_by "$H2_NUM" "$H1_NUM"
# H.3 blocked by H.1
add_blocked_by "$H3_NUM" "$H1_NUM"
# H.4 blocked by H.3
add_blocked_by "$H4_NUM" "$H3_NUM"
# H.5 blocked by C.6
add_blocked_by "$H5_NUM" "$C6_NUM"

# I.1 blocked by C.9, F.2
add_blocked_by "$I1_NUM" "$C9_NUM"
add_blocked_by "$I1_NUM" "$F2_NUM"
# I.2 blocked by I.1
add_blocked_by "$I2_NUM" "$I1_NUM"
# I.3 blocked by I.1
add_blocked_by "$I3_NUM" "$I1_NUM"
# I.6 blocked by I.1
add_blocked_by "$I6_NUM" "$I1_NUM"
# I.7 blocked by I.6
add_blocked_by "$I7_NUM" "$I6_NUM"

# J.1 blocked by E.3, E.4
add_blocked_by "$J1_NUM" "$E3_NUM"
add_blocked_by "$J1_NUM" "$E4_NUM"
# J.2 blocked by J.1
add_blocked_by "$J2_NUM" "$J1_NUM"
# J.3 blocked by E.4
add_blocked_by "$J3_NUM" "$E4_NUM"
# J.4 blocked by J.3
add_blocked_by "$J4_NUM" "$J3_NUM"

# K.0 blocked by C.1, D.3, E.1
add_blocked_by "$K0_NUM" "$C1_NUM"
add_blocked_by "$K0_NUM" "$D3_NUM"
add_blocked_by "$K0_NUM" "$E1_NUM"
# K.1 blocked by K.0, D.6
add_blocked_by "$K1_NUM" "$K0_NUM"
add_blocked_by "$K1_NUM" "$D6_NUM"
# K.2 blocked by K.0, E.3
add_blocked_by "$K2_NUM" "$K0_NUM"
add_blocked_by "$K2_NUM" "$E3_NUM"

# L.1 blocked by E.1
add_blocked_by "$L1_NUM" "$E1_NUM"
# L.2 blocked by A.3
add_blocked_by "$L2_NUM" "$A3_NUM"

# O.1 blocked by C.1
add_blocked_by "$O1_NUM" "$C1_NUM"
# O.2 blocked by C.1
add_blocked_by "$O2_NUM" "$C1_NUM"
# O.3 blocked by C.6
add_blocked_by "$O3_NUM" "$C6_NUM"

# N.1 blocked by A.1
add_blocked_by "$N1_NUM" "$A1_NUM"

echo ""
echo "=== DONE ==="
echo "Issue mapping:"
cat "$ISSUE_MAP_FILE"
