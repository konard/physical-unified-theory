# Repository requirements and delivery status

This register covers every GitHub issue present in the repository inventory,
including closed issues. Issue state records GitHub workflow history.
**Verified** requires evidence for the listed scope. **Partial** records a
checked subset. **Open** requires implementation or acceptance evidence.
**Blocked** identifies a specific unresolved prerequisite or unavailable source.
Only **Verified** satisfies the delivery check.

Each numeric ID is a GitHub issue. The suffix after `/` identifies an original
roadmap task, an explicit hypothesis (`H1`, `H2`, and so on), or a criterion
extracted from issue prose or PR feedback. Issue-level rows include the scope in
their linked issue, including child issues, prerequisites and implementation
order. A hypothesis is verified when its stated scope is established or ruled
out with evidence.

The register draws on the [roadmap and priorities](../ROADMAP.md), [execution
plans](../plan/README.md), [415-task and 41-hypothesis audit](case-studies/issue-117/requirements.md),
[issue closure audit](case-studies/issue-119/issue-117.md), and the
[requirement from PR #120](https://github.com/konard/physical-unified-theory/pull/120#issuecomment-7218705686).
Evidence can document the gap for an unverified row. For a roadmap task
without a more specific link, the audit gives its precise original scope,
candidate implementation and proposed acceptance checks.

## Checking delivery

Passing CI is an acceptance condition evaluated by the workflows. The delivery
check requires every row to be verified, and the proof workflows provide
independent build and test results.

On every pull request to and push to `main`, the [requirements
workflow](../.github/workflows/requirements.yml) checks this file against the
paginated GitHub issue inventory and preserves IDs already recorded on the base
branch. The check fails if it finds missing rows, invalid or duplicate statuses
or IDs, invalid local evidence links, or any unverified row. Its log lists each
unverified ID. Lean and Rocq still run their own proof checks.

To reproduce the check with the live issue inventory:

```sh
gh api --paginate --slurp --method GET repos/konard/physical-unified-theory/issues   -f state=all -f per_page=100 > /tmp/physical-unified-theory-issues.json
python3 scripts/check_requirements.py /tmp/physical-unified-theory-issues.json
python3 -m unittest discover -s experiments -p test_requirements.py -v
```

When updating the register, read issue descriptions and discussion for prose
criteria, then add stable IDs and link the check, proof or artifact for each
verified row. The checker can recognize structured task IDs and hypothesis
markers in issue descriptions. Assessing new prose and the adequacy of
evidence requires review.


## Repository setup and planning

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #1 | [Make ROADMAP to the grand physical theory of everything](https://github.com/konard/physical-unified-theory/issues/1) | Partial | [Roadmap](../ROADMAP.md) · [Track files](../ROADMAP) · [Lean and Rocq sources](../README.md#project-structure) |
| #1/roadmap | Create the formal physics roadmap and publish extensive topic documentation informed by existing literature | Verified | [Roadmap](../ROADMAP.md) · [Track files](../ROADMAP) |
| #1/builds | Set up Lean and Rocq verification using the p-vs-np repository as a CI example | Verified | [Lean CI](../.github/workflows/lean.yml) · [Rocq CI](../.github/workflows/rocq.yml) · [PR #2](https://github.com/konard/physical-unified-theory/pull/2) |
| #1/quantum | Fully define quantum theory in Lean and Rocq | Partial | [Delivery audit](case-studies/issue-119/issue-117.md) |
| #1/relativity | Fully define general relativity in Lean and Rocq | Partial | [Delivery audit](case-studies/issue-119/issue-117.md) |
| #1/unification | Unify the completed theories in the same formal language | Open | [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #3 | [Fix CI/CD error](https://github.com/konard/physical-unified-theory/issues/3) | Partial | [Case study](case-studies/issue-3/analysis.md) |
| #3/repair | Reproduce and repair the missing Coquelicot import in the standard Rocq image | Verified | [Passing repair run](https://github.com/konard/physical-unified-theory/actions/runs/21453960907) · [Case study](case-studies/issue-3/analysis.md) |
| #3/logs | Preserve all original CI logs and related data in the case study | Blocked | GitHub returns HTTP 410 for the original log archive. [Case study](case-studies/issue-3/analysis.md) |
| #3/study | Reconstruct the timeline and root cause, research comparable failures and libraries, and document remedies with reproduction steps | Verified | [Case study](case-studies/issue-3/analysis.md) |
| #3/upstream | Determine upstream applicability and report an upstream defect with a reproducer, workaround and fix when applicable | Verified | The recorded cause was an undeclared project dependency in the selected image. [Case study](case-studies/issue-3/analysis.md) |
| #5 | [Extend roadmap with all possible exploration/research paths, and as much hypotheses as possible](https://github.com/konard/physical-unified-theory/issues/5) | Partial | [Roadmap](../ROADMAP.md) · [Track files](../ROADMAP) |
| #5/research-paths | Cover known formalized, unformalized and unexplored directions and hypotheses | Partial | [Roadmap](../ROADMAP.md) · [Track files](../ROADMAP) |
| #5/organization | Split the roadmap when necessary and support parallel work with minimal conflicts | Verified | [Roadmap](../ROADMAP.md) · [Track files](../ROADMAP) · [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #6 | [Detailed plan for roadmap with dependencies to plan conflict free execution of tasks](https://github.com/konard/physical-unified-theory/issues/6) | Verified | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #6/plans | Provide separate detailed plans for every roadmap direction and item in the plan directory | Verified | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #6/dependencies | Document dependencies and cross-link related Markdown documents | Verified | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #8 | [Fix license](https://github.com/konard/physical-unified-theory/issues/8) | Verified | [The Unlicense](../LICENSE) · [Licensing rationale](../README.md#license) · [Contributor terms](../CONTRIBUTING.md#license) |
| #8/dedication | Apply The Unlicense public domain dedication throughout the repository | Verified | [License](../LICENSE) · [Contributor terms](../CONTRIBUTING.md#license) |
| #8/comparison | Explain the benefits and scope of the public domain dedication compared with other models | Verified | [Licensing rationale](../README.md#license) |
| #11 | [Create issues in this repository based on plan folder](https://github.com/konard/physical-unified-theory/issues/11) | Partial | [Issue graph audit](case-studies/issue-119/issue-117.md#issue-registration-and-relationships) |
| #11/issues | Use gh to register every track and all task groups, splitting large issues | Verified | [Issue creation script](../create_issues.sh) · [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #11/sub-issues | Represent the planning hierarchy using native GitHub sub-issue links | Partial | [Issue graph audit](case-studies/issue-119/issue-117.md#issue-registration-and-relationships) |
| #11/dependencies | Represent the plan's applicable dependencies on all issues and sub-issues | Partial | [Issue graph audit](case-studies/issue-119/issue-117.md#issue-registration-and-relationships) |

## Roadmap tracks

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #13 | [Track A: Mathematical Foundations](https://github.com/konard/physical-unified-theory/issues/13) | Partial | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #13/foundation-order | Put usable Hilbert-space and manifold infrastructure first and respect the stated foundation dependency order | Partial | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) · [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #13/both-kernels | Cross-verify every Lean foundations formalization with its Rocq counterpart | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #14 | [Track B: Classical Physics](https://github.com/konard/physical-unified-theory/issues/14) | Open | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #15 | [Track C: Quantum Mechanics](https://github.com/konard/physical-unified-theory/issues/15) | Partial | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #16 | [Track D: General Relativity](https://github.com/konard/physical-unified-theory/issues/16) | Partial | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #17 | [Track E: Quantum Field Theory](https://github.com/konard/physical-unified-theory/issues/17) | Partial | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #18 | [Track F: Statistical Mechanics and Thermodynamics](https://github.com/konard/physical-unified-theory/issues/18) | Partial | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #19 | [Track G: Cosmology and Astrophysics](https://github.com/konard/physical-unified-theory/issues/19) | Open | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #20 | [Track H: Quantum Information and Computation](https://github.com/konard/physical-unified-theory/issues/20) | Open | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #21 | [Track I: Condensed Matter and Many-Body Physics](https://github.com/konard/physical-unified-theory/issues/21) | Open | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #22 | [Track J: Particle Physics Phenomenology](https://github.com/konard/physical-unified-theory/issues/22) | Open | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #23 | [Track K: Approaches to Quantum Gravity](https://github.com/konard/physical-unified-theory/issues/23) | Open | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #24 | [Track L: Mathematical Physics and Structural Approaches](https://github.com/konard/physical-unified-theory/issues/24) | Open | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #25 | [Track M: Hypotheses and Speculative Directions](https://github.com/konard/physical-unified-theory/issues/25) | Open | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #26 | [Track N: Experimental Connections and Predictions](https://github.com/konard/physical-unified-theory/issues/26) | Partial | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |
| #27 | [Track O: Foundations and Philosophy of Physics](https://github.com/konard/physical-unified-theory/issues/27) | Partial | [Execution plans](../plan/README.md) · [Dependency graph](../plan/DEPENDENCIES.md) |

## Mathematical foundations

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #28 | [A.1: Linear Algebra and Functional Analysis](https://github.com/konard/physical-unified-theory/issues/28) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #28/A.1.1 | Hilbert space definitions and basic properties | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #28/A.1.2 | Bounded and unbounded operators | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #28/A.1.3 | Spectral theory (spectral theorem, functional calculus) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #28/A.1.4 | Distribution theory (Schwartz space, tempered distributions) | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #28/A.1.5 | Rigged Hilbert spaces (Gelfand triples) | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #28/H1 | Hypothesis. Rigged Hilbert spaces resolve continuous spectrum issues in QM (see Track C). | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #29 | [A.2: Differential Geometry](https://github.com/konard/physical-unified-theory/issues/29) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #29/A.2.1 | Smooth manifolds and tangent bundles | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #29/A.2.2 | Tensor fields and tensor calculus | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #29/A.2.3 | Connections and covariant derivatives | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #29/A.2.4 | Curvature (Riemann, Ricci, scalar) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #29/A.2.5 | Fiber bundles (principal, associated, vector) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #29/A.2.6 | Lorentzian geometry and causal structure | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #29/H1 | Hypothesis. Fiber bundle theory provides a unified framework for gauge theories and GR. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #30 | [A.3: Topology](https://github.com/konard/physical-unified-theory/issues/30) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #30/A.3.1 | Topological spaces and continuity (Mathlib available) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #30/A.3.2 | Algebraic topology (fundamental group, homology) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #30/A.3.3 | Topological invariants relevant to physics (Chern, Pontryagin) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #31 | [A.4: Algebra](https://github.com/konard/physical-unified-theory/issues/31) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #31/A.4.1 | Lie groups and Lie algebras | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #31/A.4.2 | Representation theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #31/A.4.3 | Clifford algebras and spinors | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #31/A.4.4 | Category theory foundations | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #31/H1 | Hypothesis. C*-algebras provide the correct mathematical framework for QM (see Track L). | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #32 | [A.5: Measure Theory and Probability](https://github.com/konard/physical-unified-theory/issues/32) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #32/A.5.1 | Measure spaces and integration (Mathlib available) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #32/A.5.2 | Probability theory foundations | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #32/A.5.3 | Functional integration (path integrals) | Open | [Available constructions and continuum research limits](case-studies/issue-117/status.md#research-limits) |
| #32/A.5.4 | Stochastic processes | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #32/H1 | Hypothesis. Rigorous path integrals can be constructed in 4D via constructive QFT methods (see Track E). | Blocked | General claim remains open. [Research limits](case-studies/issue-117/status.md#research-limits) |
| #33 | [A.6: Partial Differential Equations](https://github.com/konard/physical-unified-theory/issues/33) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #33/A.6.1 | Linear PDEs (elliptic, parabolic, hyperbolic) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #33/A.6.2 | Nonlinear PDEs | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #33/A.6.3 | Geometric PDEs (Ricci flow, Yang-Mills flow) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |

## Classical physics

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #34 | [B.1: Newtonian Mechanics](https://github.com/konard/physical-unified-theory/issues/34) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #34/B.1.1 | Newton's laws as axioms | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #34/B.1.2 | Conservation laws (energy, momentum, angular momentum) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #34/B.1.3 | Central force problems | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #35 | [B.2: Lagrangian Mechanics](https://github.com/konard/physical-unified-theory/issues/35) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #35/B.2.1 | Principle of least action | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #35/B.2.2 | Euler-Lagrange equations | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #35/B.2.3 | Noether's theorem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #35/B.2.4 | Constrained systems | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #36 | [B.3: Hamiltonian Mechanics](https://github.com/konard/physical-unified-theory/issues/36) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #36/B.3.1 | Legendre transform and Hamilton's equations | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #36/B.3.2 | Canonical transformations | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #36/B.3.3 | Hamilton-Jacobi theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #37 | [B.4: Symplectic Geometry](https://github.com/konard/physical-unified-theory/issues/37) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #37/B.4.1 | Symplectic manifolds and Poisson brackets | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #37/B.4.2 | Liouville's theorem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #37/B.4.3 | Geometric quantization connection | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #37/H1 | Hypothesis. Geometric quantization provides a rigorous path from classical to quantum (see Track L). | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #38 | [B.5: Classical Electromagnetism](https://github.com/konard/physical-unified-theory/issues/38) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #38/B.5.1 | Maxwell's equations in differential form | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #38/B.5.2 | Gauge invariance (U(1)) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #38/B.5.3 | Electromagnetic energy-momentum tensor | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #39 | [B.6: Classical Field Theory](https://github.com/konard/physical-unified-theory/issues/39) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #39/B.6.1 | Field Lagrangian and Euler-Lagrange for fields | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #39/B.6.2 | Noether's theorem for fields | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #39/B.6.3 | Energy-momentum tensor | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #40 | [B.7: Classical Thermodynamics](https://github.com/konard/physical-unified-theory/issues/40) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #40/B.7.1 | Laws of thermodynamics (0th through 3rd) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #40/B.7.2 | Thermodynamic potentials | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #40/B.7.3 | Phase equilibria | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #41 | [B.8–B.9: Fluid Mechanics and Nonlinear Dynamics](https://github.com/konard/physical-unified-theory/issues/41) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #41/B.8.1 | Navier-Stokes equations | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #41/B.8.2 | Relativistic fluid dynamics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #41/B.9.1 | Hamiltonian chaos and KAM theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Quantum mechanics

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #42 | [C.1: Fundamental Postulates of Quantum Mechanics](https://github.com/konard/physical-unified-theory/issues/42) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #42/C.1.1 | State space axiom (Hilbert space, density operators) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #42/C.1.2 | Observable axiom (self-adjoint operators) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #42/C.1.3 | Measurement axiom (Born rule, projection postulate) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #42/C.1.4 | Time evolution (Schrödinger equation, unitary evolution) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #42/C.1.5 | Composite systems (tensor products) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #43 | [C.2: Exactly Solvable Quantum Systems](https://github.com/konard/physical-unified-theory/issues/43) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #43/C.2.1 | Finite-dimensional systems (spin-1/2, qubits) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #43/C.2.2 | Quantum harmonic oscillator (creation/annihilation operators) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #43/C.2.3 | Hydrogen atom (Coulomb problem) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #43/C.2.4 | Particle in a box and other 1D problems | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #43/C.2.5 | Angular momentum and spin | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #44 | [C.3: Symmetries in Quantum Mechanics](https://github.com/konard/physical-unified-theory/issues/44) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #44/C.3.1 | Wigner's theorem (symmetries as unitary/antiunitary operators) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #44/C.3.2 | Rotation group SO(3) and SU(2) representations | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #44/C.3.3 | Translation symmetry and momentum | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #44/C.3.4 | Time-reversal symmetry | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #44/H1 | Hypothesis. Superselection structure is determined by symmetry groups. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #45 | [C.4: Approximation Methods](https://github.com/konard/physical-unified-theory/issues/45) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #45/C.4.1 | Time-independent perturbation theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #45/C.4.2 | Time-dependent perturbation theory (Fermi's golden rule) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #45/C.4.3 | Variational method | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #45/C.4.4 | WKB approximation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #45/C.4.5 | Adiabatic theorem and Berry phase | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #46 | [C.5: Scattering Theory](https://github.com/konard/physical-unified-theory/issues/46) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #46/C.5.1 | S-matrix and T-matrix | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #46/C.5.2 | Born approximation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #46/C.5.3 | Partial wave analysis | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #47 | [C.6: Composite Systems and Entanglement](https://github.com/konard/physical-unified-theory/issues/47) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #47/C.6.1 | Tensor product spaces | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #47/C.6.2 | Entanglement (Bell states, Schmidt decomposition) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #47/C.6.3 | Bell inequalities and non-locality | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #47/C.6.4 | Entanglement measures | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #47/H1 | Hypothesis. Entanglement is fundamental to spacetime emergence (see Track K, Track M). | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #48 | [C.7: Open Quantum Systems](https://github.com/konard/physical-unified-theory/issues/48) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #48/C.7.1 | Density matrices and mixed states | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #48/C.7.2 | Quantum channels (CPTP maps) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #48/C.7.3 | Lindblad master equation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #48/C.7.4 | Decoherence | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #49 | [C.8: Path Integral Formulation](https://github.com/konard/physical-unified-theory/issues/49) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #49/C.8.1 | Feynman path integral (non-relativistic) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #49/C.8.2 | Connection to operator formalism | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #50 | [C.9: Second Quantization](https://github.com/konard/physical-unified-theory/issues/50) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #50/C.9.1 | Fock space construction | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #50/C.9.2 | Creation and annihilation operators | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #50/C.9.3 | Bosonic and fermionic statistics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #51 | [C.10: Quantum Chaos](https://github.com/konard/physical-unified-theory/issues/51) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #51/C.10.1 | Random matrix theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #51/C.10.2 | Level statistics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## General relativity

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #52 | [D.1: Special Relativity](https://github.com/konard/physical-unified-theory/issues/52) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #52/D.1.1 | Minkowski spacetime and metric | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #52/D.1.2 | Lorentz transformations and Lorentz group | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #52/D.1.3 | Four-vectors and relativistic kinematics | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #52/D.1.4 | Relativistic energy-momentum | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #53 | [D.2: Differential Geometry for GR](https://github.com/konard/physical-unified-theory/issues/53) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #53/D.2.1 | Pseudo-Riemannian manifolds | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #53/D.2.2 | Levi-Civita connection | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #53/D.2.3 | Geodesic equation | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #53/D.2.4 | Riemann curvature tensor | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #53/D.2.5 | Ricci tensor and scalar curvature | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #54 | [D.3: Einstein's Field Equations](https://github.com/konard/physical-unified-theory/issues/54) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #54/D.3.1 | Einstein tensor | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #54/D.3.2 | Stress-energy tensor | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #54/D.3.3 | Einstein field equations (with cosmological constant) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #54/D.3.4 | Einstein-Hilbert action and variational derivation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #54/D.3.5 | Linearized gravity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #55 | [D.4: Exact Solutions of Einstein Equations](https://github.com/konard/physical-unified-theory/issues/55) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #55/D.4.1 | Schwarzschild solution (static spherically symmetric) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #55/D.4.2 | Kerr solution (rotating black holes) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #55/D.4.3 | FLRW metric (cosmological) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #55/D.4.4 | Reissner-Nordström (charged black holes) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #55/D.4.5 | Gravitational wave solutions (pp-waves) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #55/H1 | Hypothesis. Physically reasonable exact solutions follow a unified classification. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #56 | [D.5: Singularity Theorems and Causal Structure](https://github.com/konard/physical-unified-theory/issues/56) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #56/D.5.1 | Causal structure (timelike, spacelike, null) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #56/D.5.2 | Penrose-Hawking singularity theorems | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #56/D.5.3 | Penrose diagrams (conformal compactification) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #56/D.5.4 | Cosmic censorship conjecture | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #56/H1 | Hypothesis. Cosmic censorship holds — naked singularities do not form from generic initial data. | Blocked | General claim remains open. [Research limits](case-studies/issue-117/status.md#research-limits) |
| #57 | [D.6: ADM Formalism and Initial Value Problem](https://github.com/konard/physical-unified-theory/issues/57) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #57/D.6.1 | 3+1 decomposition (lapse, shift, spatial metric) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #57/D.6.2 | ADM Hamiltonian and momentum constraints | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #57/D.6.3 | Well-posedness of initial value problem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #58 | [D.7: Gravitational Waves](https://github.com/konard/physical-unified-theory/issues/58) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #58/D.7.1 | Linearized theory and wave equation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #58/D.7.2 | Polarizations (plus and cross) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #58/D.7.3 | Energy radiated (quadrupole formula) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #59 | [D.8: Black Hole Physics](https://github.com/konard/physical-unified-theory/issues/59) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #59/D.8.1 | Event horizons and Killing horizons | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #59/D.8.2 | Black hole mechanics (four laws) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #59/D.8.3 | Hawking radiation (semiclassical) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #59/D.8.4 | Black hole entropy (Bekenstein-Hawking) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #59/H1 | Hypothesis. Black hole mechanics is identical to thermodynamics (see Track F). | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #60 | [D.9–D.10: Alternative Theories and Numerical Methods](https://github.com/konard/physical-unified-theory/issues/60) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #60/D.9.1 | f(R) gravity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #60/D.9.2 | Scalar-tensor theories (Brans-Dicke) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #60/D.10.1 | Numerical GR foundations | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Quantum field theory

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #61 | [E.1: Free Field Theory](https://github.com/konard/physical-unified-theory/issues/61) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #61/E.1.1 | Free scalar field (Klein-Gordon equation) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #61/E.1.2 | Free spinor field (Dirac equation) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #61/E.1.3 | Free vector field (Proca and Maxwell) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #61/E.1.4 | Canonical quantization of free fields | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #61/E.1.5 | Fock space and particle interpretation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #61/H1 | Hypothesis. Haag's theorem is resolvable through better understanding of the interaction picture. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #62 | [E.2: Interacting Field Theory](https://github.com/konard/physical-unified-theory/issues/62) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #62/E.2.1 | Perturbation theory and Feynman diagrams | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #62/E.2.2 | Renormalization (UV divergences, regularization) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #62/E.2.3 | Renormalization group | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #62/E.2.4 | Non-perturbative methods (instantons, lattice) | Open | [Available constructions and continuum research limits](case-studies/issue-117/status.md#research-limits) |
| #62/H1 | Hypothesis. Yang-Mills mass gap is solvable via formalization (Millennium Prize). | Blocked | General claim remains open. [Research limits](case-studies/issue-117/status.md#research-limits) |
| #63 | [E.3: Gauge Theories](https://github.com/konard/physical-unified-theory/issues/63) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #63/E.3.1 | Abelian gauge theory (QED) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #63/E.3.2 | Non-Abelian gauge theory (Yang-Mills) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #63/E.3.3 | BRST symmetry and ghost fields | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #63/E.3.4 | Gauge fixing and Faddeev-Popov procedure | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #64 | [E.4: The Standard Model](https://github.com/konard/physical-unified-theory/issues/64) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #64/E.4.1 | Electroweak theory (SU(2) × U(1)) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #64/E.4.2 | Higgs mechanism and spontaneous symmetry breaking | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #64/E.4.3 | QCD (SU(3) color) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #64/E.4.4 | Full Standard Model gauge group SU(3) × SU(2) × U(1) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #64/E.4.5 | Anomaly cancellation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #64/H1 | Hypothesis. The Standard Model gauge group is nearly uniquely determined by anomaly cancellation. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #65 | [E.5–E.8: Advanced QFT Topics](https://github.com/konard/physical-unified-theory/issues/65) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #65/E.5.1 | Chiral and gauge anomalies | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #65/E.6.1 | Topological aspects (instantons, monopoles, theta vacuum) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #65/E.7.1 | Conformal field theory (2D and higher) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #65/E.8.1 | Effective field theory framework | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #65/H1 | Hypothesis. All QFTs are effective theories, each valid within an energy domain. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Statistical mechanics

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #66 | [F.1: Foundations of Statistical Mechanics](https://github.com/konard/physical-unified-theory/issues/66) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #66/F.1.1 | Microcanonical, canonical, grand canonical ensembles | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #66/F.1.2 | Partition functions and free energies | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #66/F.1.3 | Equivalence of ensembles in thermodynamic limit | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #67 | [F.2: Quantum Statistical Mechanics](https://github.com/konard/physical-unified-theory/issues/67) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #67/F.2.1 | Density matrix formulation | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #67/F.2.2 | Bose-Einstein and Fermi-Dirac statistics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #67/F.2.3 | Bose-Einstein condensation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #67/F.2.4 | KMS condition for thermal equilibrium | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #67/H1 | Hypothesis. KMS condition characterizes thermal equilibrium in quantum field theory. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #68 | [F.3: Phase Transitions and Critical Phenomena](https://github.com/konard/physical-unified-theory/issues/68) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #68/F.3.1 | Ising model and exact solutions | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #68/F.3.2 | Landau theory of phase transitions | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #68/F.3.3 | Renormalization group for critical phenomena | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #68/F.3.4 | Universality classes | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #68/H1 | Hypothesis. Universality in critical phenomena arises from RG fixed points. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #69 | [F.4: Entropy and Information](https://github.com/konard/physical-unified-theory/issues/69) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #69/F.4.1 | Boltzmann entropy and H-theorem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #69/F.4.2 | Von Neumann entropy | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #69/F.4.3 | Shannon entropy and connections to physics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #69/F.4.4 | Maximum entropy principle | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #70 | [F.5: Non-Equilibrium Statistical Mechanics](https://github.com/konard/physical-unified-theory/issues/70) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #70/F.5.1 | Boltzmann equation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #70/F.5.2 | Linear response theory (Kubo formula) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #70/F.5.3 | Fluctuation-dissipation theorem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #70/F.5.4 | Jarzynski equality and Crooks theorem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #71 | [F.6: Black Hole Thermodynamics](https://github.com/konard/physical-unified-theory/issues/71) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #71/F.6.1 | Four laws of black hole mechanics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #71/F.6.2 | Bekenstein-Hawking entropy | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #71/F.6.3 | Information paradox | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #71/F.6.4 | Page curve and unitarity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #71/H1 | Hypothesis. Black hole evaporation is unitary; the Page curve is correct. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #72 | [F.7: Thermodynamics of Spacetime](https://github.com/konard/physical-unified-theory/issues/72) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #72/F.7.1 | Unruh effect | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #72/F.7.2 | Jacobson's derivation of Einstein equations from thermodynamics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #72/F.7.3 | Verlinde's entropic gravity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #72/H1 | Hypothesis. Einstein equations can be derived from thermodynamic relations on local Rindler horizons. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Cosmology and astrophysics

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #73 | [G.1: Big Bang Cosmology](https://github.com/konard/physical-unified-theory/issues/73) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #73/G.1.1 | FLRW dynamics (Friedmann equations) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #73/G.1.2 | Cosmological redshift and Hubble's law | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #73/G.1.3 | Thermal history of the universe | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #73/G.1.4 | Big Bang nucleosynthesis | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #74 | [G.2: Inflation](https://github.com/konard/physical-unified-theory/issues/74) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #74/G.2.1 | Slow-roll inflation (single scalar field) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #74/G.2.2 | Inflationary perturbation theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #74/G.2.3 | Observational predictions (spectral index, tensor-to-scalar ratio) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #74/G.2.4 | Eternal inflation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #74/H1 | Hypothesis. Cosmic inflation occurred and generated primordial perturbations that seeded structure. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #75 | [G.3: Dark Matter](https://github.com/konard/physical-unified-theory/issues/75) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #75/G.3.1 | Evidence and observational constraints | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #75/G.3.2 | CDM model and structure formation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #75/G.3.3 | Particle dark matter candidates (links to Track J) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #76 | [G.4: Dark Energy and Cosmological Constant](https://github.com/konard/physical-unified-theory/issues/76) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #76/G.4.1 | Cosmological constant problem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #76/G.4.2 | Dark energy models (quintessence, w(z)) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #76/G.4.3 | Observational constraints (SNe Ia, BAO, CMB) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #76/H1 | Hypothesis. The cosmological constant problem is the most important unsolved problem in physics. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #77 | [G.5–G.9: Advanced Cosmology](https://github.com/konard/physical-unified-theory/issues/77) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #77/G.5.1 | Primordial gravitational waves | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #77/G.5.2 | Baryogenesis | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #77/G.6.1 | Linear perturbation theory and structure formation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #77/G.7.1 | Wheeler-DeWitt equation for cosmology | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #77/G.7.2 | Hartle-Hawking no-boundary proposal | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #77/G.8.1 | Astrophysical black holes | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #77/G.9.1 | Cyclic and bouncing cosmologies | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Quantum information

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #78 | [H.1: Quantum Circuits and Gates](https://github.com/konard/physical-unified-theory/issues/78) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #78/H.1.1 | Qubit formalization (Bloch sphere representation) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #78/H.1.2 | Single-qubit gates (Pauli, Hadamard, phase, T) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #78/H.1.3 | Multi-qubit gates (CNOT, Toffoli, SWAP) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #78/H.1.4 | Universal gate sets | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #78/H.1.5 | Circuit model of computation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #79 | [H.2: Quantum Algorithms](https://github.com/konard/physical-unified-theory/issues/79) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #79/H.2.1 | Deutsch-Jozsa algorithm | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #79/H.2.2 | Grover's search algorithm | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #79/H.2.3 | Shor's factoring algorithm | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #79/H.2.4 | Quantum simulation algorithms | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #79/H.2.5 | Variational quantum algorithms (VQE, QAOA) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #80 | [H.3: Quantum Error Correction](https://github.com/konard/physical-unified-theory/issues/80) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #80/H.3.1 | Quantum error correction basics (Knill-Laflamme conditions) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #80/H.3.2 | Stabilizer formalism | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #80/H.3.3 | Surface codes | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #80/H.3.4 | Topological quantum error correction | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #80/H1 | Hypothesis. Topological QEC connects to TQFT (Track L) and condensed matter (Track I). | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #81 | [H.4: Quantum Cryptography](https://github.com/konard/physical-unified-theory/issues/81) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #81/H.4.1 | BB84 protocol | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #81/H.4.2 | Security proofs | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #81/H.4.3 | Quantum key distribution | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #82 | [H.5: Entanglement Theory](https://github.com/konard/physical-unified-theory/issues/82) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #82/H.5.1 | Entanglement measures (concurrence, negativity, entropy) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #82/H.5.2 | Entanglement witnesses | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #82/H.5.3 | Entanglement area laws | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #82/H.5.4 | Multipartite entanglement | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #82/H1 | Hypothesis. Entanglement area laws are fundamental to the gravity-information connection (see Track K). | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #83 | [H.6–H.8: Complexity, Channels, and Thermodynamics](https://github.com/konard/physical-unified-theory/issues/83) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #83/H.6.1 | BQP and complexity classes | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #83/H.6.2 | Quantum computational supremacy | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #83/H.6.3 | Holographic complexity conjectures | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #83/H.7.1 | Quantum channel capacity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #83/H.7.2 | Quantum data processing inequality | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #83/H.8.1 | Quantum thermodynamic resource theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #83/H1 | Hypothesis. AdS/CFT is a quantum error-correcting code. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Many-body physics

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #84 | [I.1: Second Quantization and Many-Body Techniques](https://github.com/konard/physical-unified-theory/issues/84) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #84/I.1.1 | Many-body Fock space (bosonic and fermionic) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #84/I.1.2 | Mean-field theory (Hartree-Fock) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #84/I.1.3 | Green's functions (single-particle, many-body) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #84/I.1.4 | Feynman diagrams for condensed matter | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #85 | [I.2: Superconductivity](https://github.com/konard/physical-unified-theory/issues/85) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #85/I.2.1 | BCS theory (Cooper pairs, gap equation) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #85/I.2.2 | Ginzburg-Landau theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #85/I.2.3 | Type-I and Type-II superconductors | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #85/I.2.4 | Josephson effect | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #85/H1 | Hypothesis. High-Tc superconductivity is explained by a single theoretical framework. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #86 | [I.3: Topological Phases of Matter](https://github.com/konard/physical-unified-theory/issues/86) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #86/I.3.1 | Topological insulators (Z₂ classification) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #86/I.3.2 | Integer quantum Hall effect (Chern number) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #86/I.3.3 | Fractional quantum Hall effect | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #86/I.3.4 | Topological classification (ten-fold way) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #86/I.3.5 | Anyons and topological order | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #86/H1 | Hypothesis. Topological phase classification is governed by cobordism/K-theory. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #87 | [I.4–I.5: Quantum Magnetism and Strongly Correlated Systems](https://github.com/konard/physical-unified-theory/issues/87) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #87/I.4.1 | Heisenberg model | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #87/I.4.2 | Spin waves and magnons | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #87/I.4.3 | Frustrated magnets and spin liquids | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #87/I.5.1 | Hubbard model | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #87/I.5.2 | Kondo effect | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #87/I.5.3 | Heavy fermions | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #88 | [I.6: Tensor Networks and Entanglement](https://github.com/konard/physical-unified-theory/issues/88) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #88/I.6.1 | Matrix product states (MPS) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #88/I.6.2 | DMRG algorithm | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #88/I.6.3 | MERA (multiscale entanglement renormalization) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #88/I.6.4 | Tensor network / holography connection | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #88/H1 | Hypothesis. MERA encodes AdS geometry, realizing the holographic principle (see Track K). | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #89 | [I.7: Emergent Phenomena](https://github.com/konard/physical-unified-theory/issues/89) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #89/I.7.1 | Universality and effective theories | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #89/I.7.2 | Emergent gauge fields | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #89/I.7.3 | Gravity as emergent phenomenon | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #89/H1 | Hypothesis. Gravity is emergent like elasticity — it arises from microscopic degrees of freedom. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Particle physics

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #90 | [J.1: Neutrino Physics](https://github.com/konard/physical-unified-theory/issues/90) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #90/J.1.1 | Neutrino mass terms (Dirac and Majorana) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #90/J.1.2 | Neutrino oscillations (PMNS matrix) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #90/J.1.3 | Seesaw mechanism | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #90/H1 | Hypothesis. Neutrinos are Majorana fermions and the seesaw mechanism explains their small masses. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #91 | [J.2: CP Violation and Matter-Antimatter Asymmetry](https://github.com/konard/physical-unified-theory/issues/91) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #91/J.2.1 | CKM matrix and CP violation in quarks | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #91/J.2.2 | Strong CP problem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #91/J.2.3 | Axions as solution to strong CP | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #91/J.2.4 | Baryogenesis (Sakharov conditions) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #91/H1 | Hypothesis. Axions solve the strong CP problem and constitute dark matter. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #92 | [J.3: Grand Unified Theories](https://github.com/konard/physical-unified-theory/issues/92) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #92/J.3.1 | SU(5) GUT (Georgi-Glashow) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #92/J.3.2 | SO(10) GUT | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #92/J.3.3 | Proton decay predictions | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #92/J.3.4 | Gauge coupling unification | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #92/H1 | Hypothesis. Gauge couplings unify at the GUT scale (~10¹⁶ GeV). | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #93 | [J.4: Supersymmetry](https://github.com/konard/physical-unified-theory/issues/93) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #93/J.4.1 | SUSY algebra and superfields | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #93/J.4.2 | Minimal Supersymmetric Standard Model (MSSM) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #93/J.4.3 | SUSY breaking mechanisms | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #93/J.4.4 | Naturalness and hierarchy problem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #94 | [J.5–J.9: Extra Dimensions, Dark Matter, Flavor, Precision, Collider](https://github.com/konard/physical-unified-theory/issues/94) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #94/J.5.1 | Kaluza-Klein theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #94/J.5.2 | Large extra dimensions (ADD) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #94/J.5.3 | Warped extra dimensions (Randall-Sundrum) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #94/J.6.1 | WIMP dark matter | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #94/J.6.2 | Axion dark matter | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #94/J.7.1 | Flavor symmetries | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #94/J.8.1 | Precision electroweak tests | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #94/J.9.1 | Collider phenomenology | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Quantum gravity

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #95 | [K.0: The Incompatibility Problem](https://github.com/konard/physical-unified-theory/issues/95) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #95/K.0.1 | Formal statement of QM-GR incompatibility | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #95/K.0.2 | Non-renormalizability of perturbative quantum gravity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #95/K.0.3 | Problem of time | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #95/K.0.4 | Background independence requirement | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #96 | [K.1: Canonical Quantum Gravity](https://github.com/konard/physical-unified-theory/issues/96) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #96/K.1.1 | Wheeler-DeWitt equation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #96/K.1.2 | Loop quantum gravity (Ashtekar variables, holonomies) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #96/K.1.3 | Spin networks and spin foams | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #96/K.1.4 | Loop quantum cosmology | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #96/K.1.5 | Discrete area and volume spectra | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #96/H1 | Hypothesis. LQG correctly quantizes GR with discrete spectra for area and volume. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #97 | [K.2: String Theory and M-Theory](https://github.com/konard/physical-unified-theory/issues/97) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #97/K.2.1 | Bosonic string (Nambu-Goto and Polyakov actions) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #97/K.2.2 | Superstring theory (Type I, IIA, IIB, heterotic) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #97/K.2.3 | Compactification (Calabi-Yau, flux) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #97/K.2.4 | D-branes and gauge/gravity duality | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #97/K.2.5 | AdS/CFT correspondence | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #97/K.2.6 | String phenomenology and landscape | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #97/K.2.7 | Swampland conjectures | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #97/H1 | Hypothesis. String theory is the correct theory of quantum gravity; the landscape admits physical selection. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #98 | [K.3–K.5: Causal Sets, CDT, Asymptotic Safety](https://github.com/konard/physical-unified-theory/issues/98) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #98/K.3.1 | Causal set definition and partial order | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #98/K.3.2 | Hauptvermutung (manifold-likeness) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #98/K.3.3 | Dynamics (sequential growth models) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #98/K.4.1 | Simplicial quantum gravity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #98/K.4.2 | Phase structure and emergent 4D | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #98/K.5.1 | Functional renormalization group for gravity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #98/K.5.2 | Non-Gaussian fixed point | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #99 | [K.6–K.12: Additional QG Approaches](https://github.com/konard/physical-unified-theory/issues/99) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #99/K.6.1 | Non-commutative geometry (Connes' spectral action) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #99/K.7.1 | Twistor theory (Penrose) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #99/K.8.1 | Emergent gravity (Verlinde, Jacobson) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #99/K.9.1 | Group field theory and tensor models | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #99/K.10.1 | Hořava-Lifshitz gravity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #99/K.11.1 | Quantum gravity phenomenology (predictions) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #99/K.12.1 | Other approaches (supergravity, higher-spin, etc.) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Mathematical physics

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #100 | [L.1: Algebraic Quantum Field Theory (AQFT)](https://github.com/konard/physical-unified-theory/issues/100) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #100/L.1.1 | Haag-Kastler axioms (nets of operator algebras) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #100/L.1.2 | Locally covariant QFT on curved spacetime | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #100/L.1.3 | DHR superselection theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #100/L.1.4 | Modular theory (Tomita-Takesaki) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #100/H1 | Hypothesis. AQFT provides the correct axiomatization; locally covariant formulation is natural for curved spacetime. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #101 | [L.2: Topological Quantum Field Theory (TQFT)](https://github.com/konard/physical-unified-theory/issues/101) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #101/L.2.1 | Atiyah-Segal axioms | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #101/L.2.2 | Chern-Simons theory | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #101/L.2.3 | Witten-type and Schwarz-type TQFTs | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #101/L.2.4 | Topological invariants from TQFT | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #101/H1 | Hypothesis. Every 3D TQFT arises from a modular tensor category. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #102 | [L.3–L.5: Categories, NCG, Geometric Quantization](https://github.com/konard/physical-unified-theory/issues/102) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #102/L.3.1 | Functorial QFT (Atiyah-Segal, Baez-Dolan) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #102/L.3.2 | Higher gauge theory and higher categories | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #102/L.3.3 | Categorical quantum mechanics (Abramsky-Coecke) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #102/L.4.1 | Spectral triples and Connes' program | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #102/L.4.2 | Non-commutative Standard Model | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #102/L.4.3 | Spectral action principle | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #102/L.5.1 | Prequantization and polarization | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #102/L.5.2 | BV-BRST formalism | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #102/L.5.3 | Deformation quantization | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #103 | [L.6–L.10: Advanced Mathematical Frameworks](https://github.com/konard/physical-unified-theory/issues/103) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #103/L.6.1 | Integrable systems and exact results | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #103/L.7.1 | Von Neumann algebras (Type III₁ for QFT) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #103/L.8.1 | Index theorems in physics (Atiyah-Singer) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #103/L.9.1 | Information geometry | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #103/L.10.1 | Homotopy type theory and physics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #103/H1 | Hypothesis. HoTT provides a natural language for gauge equivalence and physics structures. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Speculative research

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #104 | [M.1: Novel Unification Proposals](https://github.com/konard/physical-unified-theory/issues/104) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #104/M.1.1 | Information-theoretic physics (it from bit, constructor theory) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #104/M.1.2 | Spacetime from entanglement (ER=EPR, tensor networks) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #104/M.1.3 | Amplituhedron and positive geometry | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #105 | [M.2: Discrete vs. Continuous Spacetime](https://github.com/konard/physical-unified-theory/issues/105) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #105/M.2.1 | Discrete approaches (causal sets, digital physics) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #105/M.2.2 | Continuous approaches (NCG) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #105/M.2.3 | Formal comparison of discrete and continuous | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106 | [M.3–M.6: Time, Measurement, Cosmological Constant, Hierarchy](https://github.com/konard/physical-unified-theory/issues/106) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.3.1 | Frozen formalism and internal time | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.3.2 | Thermal time hypothesis (Connes-Rovelli) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.3.3 | Page-Wootters mechanism | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.3.4 | Emergent time | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.4.1 | Gravitational collapse models (Penrose, Diósi) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.4.2 | Many-worlds and quantum gravity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.5.1 | Anthropic landscape solution | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.5.2 | Dynamical relaxation mechanisms | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.5.3 | Sequestering | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.6.1 | Supersymmetric solutions | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.6.2 | Composite Higgs | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #106/M.6.3 | Extra dimensions solutions | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #107 | [M.7–M.11: Speculative Directions](https://github.com/konard/physical-unified-theory/issues/107) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #107/M.7.1 | String landscape and multiverse | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #107/M.7.2 | Eternal inflation and measure problem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #107/M.8.1 | Consciousness and physics (Orch OR, IIT) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #107/M.9.1 | Simulation hypothesis | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #107/M.10.1 | Exceptional mathematical structures in physics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #107/M.10.2 | Number theory and physics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #107/M.10.3 | Type theory and physical constraints | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #107/M.11.1 | Analog models (acoustic black holes) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Experiments and predictions

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #108 | [N.1: Units and Dimensional Analysis](https://github.com/konard/physical-unified-theory/issues/108) | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #108/N.1.1 | SI unit system formalization | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #108/N.1.2 | Natural units (ℏ = c = 1) | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #108/N.1.3 | Planck units | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #108/N.1.4 | Dimensional analysis as type checking | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #108/N.1.5 | Unit conversion framework | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #108/H1 | Hypothesis. Type-safe units can prevent dimensional errors at compile-time. | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #109 | [N.2: Fundamental Constants](https://github.com/konard/physical-unified-theory/issues/109) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #109/N.2.1 | Speed of light, Planck's constant, gravitational constant | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #109/N.2.2 | Fine structure constant | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #109/N.2.3 | Particle masses and coupling constants | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #109/N.2.4 | CODATA values with uncertainties | Verified | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #110 | [N.3–N.5: Precision Tests of QM, GR, and SM](https://github.com/konard/physical-unified-theory/issues/110) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.3.1 | Hydrogen spectroscopy (Lamb shift) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.3.2 | Electron g-2 (anomalous magnetic moment) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.3.3 | Casimir effect | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.3.4 | Bell test experiments | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.4.1 | Mercury perihelion precession | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.4.2 | Gravitational light deflection | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.4.3 | Gravitational redshift | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.4.4 | Shapiro time delay | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.4.5 | Frame-dragging (Gravity Probe B) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.4.6 | Gravitational wave detection (LIGO/Virgo) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.5.1 | Electroweak precision tests (Z-pole, W mass) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.5.2 | QCD tests (jet physics, running coupling) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.5.3 | Higgs boson properties | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #110/N.5.4 | Muon g-2 anomaly | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111 | [N.6–N.10: QG Predictions, Phenomenology, Cosmological Observations](https://github.com/konard/physical-unified-theory/issues/111) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.6.1 | LQG predictions (discrete spectra, Immirzi parameter) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.6.2 | String theory predictions (extra dimensions, moduli) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.6.3 | Asymptotic safety predictions | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.6.4 | Causal set predictions | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.7.1 | Modified dispersion relations | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.7.2 | Lorentz violation bounds | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.7.3 | Gravitational decoherence | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.8.1 | CMB power spectrum | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.8.2 | Baryon acoustic oscillations | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.9.1 | Cosmic ray physics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.9.2 | Neutrino astronomy | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/N.10.1 | Formalized experimental results with error bars | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #111/H1 | Hypothesis. Formalizing experimental results as theorems with error bars creates a rigorous theory-experiment interface. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Foundations of physics

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #112 | [O.1: Quantum Measurement Problem](https://github.com/konard/physical-unified-theory/issues/112) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #112/O.1.1 | Formal statement of the measurement problem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #112/O.1.2 | Copenhagen interpretation | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #112/O.1.3 | Many-worlds interpretation (Everett) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #112/O.1.4 | Bohmian mechanics (pilot-wave theory) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #112/O.1.5 | Consistent histories | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #112/O.1.6 | Relational quantum mechanics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #112/O.1.7 | QBism | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #112/O.1.8 | Collapse theories (GRW, CSL) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #112/H1 | Hypothesis. Different QM interpretations make different predictions in extreme regimes (gravity, cosmology). | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #113 | [O.2: Operational and Reconstructive Approaches](https://github.com/konard/physical-unified-theory/issues/113) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #113/O.2.1 | Hardy's axioms for QM | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #113/O.2.2 | Informational axioms (Chiribella et al.) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #113/O.2.3 | Generalized probabilistic theories (GPTs) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #113/O.2.4 | Quantum logic | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #113/H1 | Hypothesis. QM is uniquely derivable from information-theoretic axioms. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #114 | [O.3: Determinism and Indeterminism](https://github.com/konard/physical-unified-theory/issues/114) | Partial | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #114/O.3.1 | Bell's theorem (formal proof and implications) | Partial | [Formalization evidence](case-studies/issue-117/status.md#implementation-and-verification) |
| #114/O.3.2 | Kochen-Specker theorem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #114/O.3.3 | PBR theorem (reality of quantum state) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #114/O.3.4 | Free will theorem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #114/O.3.5 | Superdeterminism | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #114/H1 | Hypothesis. Bell/Kochen-Specker/PBR constraints uniquely determine viable interpretations. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115 | [O.4–O.9: Spacetime, Arrow of Time, Symmetry, QG Foundations](https://github.com/konard/physical-unified-theory/issues/115) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.4.1 | Substantivalism vs. relationalism | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.4.2 | Hole argument (Einstein, Earman-Norton) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.4.3 | Emergent spacetime | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.4.4 | Structural realism | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.5.1 | Thermodynamic arrow (second law) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.5.2 | Cosmological arrow | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.5.3 | Radiative arrow | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.5.4 | Quantum arrow (measurement irreversibility) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.6.1 | Wigner classification of particles | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.6.2 | Gauge symmetry: physical vs. mathematical | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.6.3 | Noether's theorem (physical interpretation) | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.6.4 | CPT theorem | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.7.1 | Nature of physical laws | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.8.1 | Measurement problem in quantum gravity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.8.2 | Observables in quantum gravity | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.8.3 | Relational approach to QG | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/O.9.1 | Unreasonable effectiveness of mathematics | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |
| #115/H1 | Hypothesis. QG foundational issues are QM interpretational problems amplified by background independence. | Open | [Task scope](case-studies/issue-117/requirements.md) · [Implementation audit](case-studies/issue-117/status.md) |

## Repository delivery audit

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #117 | [Address all 102 open issues in konard/physical-unified-theory](https://github.com/konard/physical-unified-theory/issues/117) | Partial | [Delivery audit](case-studies/issue-119/issue-117.md) |
| #117/inventory | Read all 102 requested issues and their comments, including the descendants outside direct attachments | Verified | [Delivery audit](case-studies/issue-119/issue-117.md) |
| #117/delivery | Implement and verify all 102 required issues within PR #118 | Partial | [Delivery audit](case-studies/issue-119/issue-117.md) |
| #117/closing-references | Give the parent and all 102 required issues a positive GitHub closing reference each | Verified | [PR #118 description and merge](https://github.com/konard/physical-unified-theory/pull/118) |
| #117/existing-resolution | Record any previously resolved or unreproducible item explicitly in the same PR description | Verified | The audit found no required issue already fully resolved or a repro-only exception. [Original audit](case-studies/issue-117/status.md) |

## Null-cone quantization and delivery check

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| #119 | [Use all tools we have to verify https://arxiv.org/abs/2611.34924](https://github.com/konard/physical-unified-theory/issues/119) | Partial | [Case study](case-studies/issue-119/README.md) |
| #119/evidence | Compile versioned issue evidence under docs/case-studies/issue-119 | Verified | [Case study](case-studies/issue-119/README.md) |
| #119/research | Analyze the whole paper and search additional primary sources | Verified | [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) · [Sources](case-studies/issue-119/sources.md) |
| #119/solutions | List each requirement with implementation options, reusable libraries, and a verification plan | Verified | [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) · [Libraries](case-studies/issue-119/sources.md) |
| #119/issue-117-audit | Independently verify what #117 delivered | Verified | [Delivery audit](case-studies/issue-119/issue-117.md) |
| #119/abstract-claims | Reformalize the open-gluing and cutoff-domain arguments and verify counterexamples to the abstract implications | Verified | [Reproduction and tests](case-studies/issue-119/verification.md) |
| #119/radial-clock-test | Test whether the benchmark Gaussian covariance alone can support a clock with radial gradient energy | Verified | [Commuting radial construction](case-studies/issue-119/analysis.md#a-commuting-radial-clock-with-the-benchmark-covariance) · [Rocq and numerical checks](case-studies/issue-119/verification.md) |
| #119/fixed-area-bound | Derive the fixed-area quantum form inequality from exact density normalization and the ordered clock | Verified | [Fixed-area proof and domain assumptions](case-studies/issue-119/analysis.md#classical-clock-and-the-jt-control) |
| #119/jt-control | Derive the specified JT control including boundary charges, matter zero modes and dynamical evolution | Partial | [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/classical-evolution | Construct the reduced characteristic Einstein solution, variations, constraints, Hamiltonian and matching | Partial | [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/continuum-representation | Construct the actual continuum positive state, observable representation and unitary evolution | Blocked | The continuum representation with the required domains and dynamics is missing. [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/clock-projection | Prove clock form convergence, area compatibility and the required preparation weight in the actual model | Blocked | The positive finite-cut overlaps can vanish in the limit. The specified preparation needs a uniform spectral estimate. [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/open-amplitudes | Derive gravitational transition amplitudes and establish admissible cut independence and cutoff restoration | Partial | [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/closed-trace | Identify exact closed gluing with convergent cuts or a positive exact replica limit and conclude finite rank | Blocked | The exact identification is missing. Bounded open gluing permits even a divergent closed trace. [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/spectra | Derive area multiplicities and AdS energy and heat trace bounds in the exact construction | Blocked | The joint cut sums require independent unconditional convergence. [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/entropy | Establish exact spectral growth and match the ensemble and graviton/ghost determinants | Partial | [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/topology | Establish the physical norm, topology identification and comparison of two-sided correlators | Blocked | Requires exact closed gluing and a constructed physical norm. [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/backreaction | Verify gauge-compatible dynamics, renormalized quadratic source, and the retarded and Bianchi identities | Partial | [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/amplitude-axioms | Construct the amplitude theory and verify finite closures, analytic continuation and reflection positivity | Blocked | Appendix E assumes the finite closed amplitudes that the gravitational realization must construct. [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/verdict | Produce a proof or disproof of the specified four-dimensional quantization and assess the proposed unification | Blocked | The checked countermodels leave the exact gravitational construction undecided. [Equation-level checks and remaining proof obligations](case-studies/issue-119/analysis.md) |
| #119/single-pr | Implement and verify all requirements in PR #120 with no deferred work | Partial | [PR #120](https://github.com/konard/physical-unified-theory/pull/120) |
| #119/register | Maintain one Markdown register covering every registered issue and each identified task, hypothesis and acceptance condition | Verified | [PR requirement](https://github.com/konard/physical-unified-theory/pull/120#issuecomment-7218705686) · [Coverage checker](../scripts/check_requirements.py) |
| #119/gate | Fail CI while any requirement is missing, unfinished or unsupported and keep verified-delivery evidence in sync | Verified | [Workflow](../.github/workflows/requirements.yml) · [Gate regressions](../experiments/test_requirements.py) |
| #119/consistency | Keep repository changes, documentation, tests and verification evidence consistent with all discussed requirements | Partial | The register and gate cover repository delivery. Scientific and implementation gaps remain. [Verification record](case-studies/issue-119/verification.md) |
