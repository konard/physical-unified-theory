# Verification of null-cone quantization

Venkatesa Chandrasekaran proposes a quantization of four-dimensional Lorentzian **vacuum** general relativity using finite regions bounded in part by null cones. The paper also introduces a two-dimensional JT gravity example coupled to matter. A four-dimensional matter-coupled model and distinguishing empirical predictions lie outside the scope of the proposal. [An algebraic quantization of gravity from the null cone](https://arxiv.org/abs/2611.34924v1)

Two checked counterexamples resolve questions about the proposed verification. A bounded positive operator can satisfy every absolute open gluing bound and have an infinite closed trace. Increasing positive forms can converge to a form whose domain omits the entire initial state. These examples disprove the corresponding implications from the abstract assumptions. A verdict on the specific four-dimensional model still requires an exact gravitational construction that supplies the missing hypotheses, or a contradiction that holds for that construction. The audit gives equations and acceptance tests for these obligations. [Argument audit](analysis.md)

Issue #117 was partially delivered. The merged PR provides real, independently checkable foundations and unit tests. GitHub closed all 102 tracked issues even though its committed inventory records substantial unfinished work. The earlier implementation does not supply the continuum foundations needed by the new paper. [Issue #117 audit](issue-117.md)

## Evidence and requirements

The [repository requirements register](../../REQUIREMENTS.md) includes the
acceptance criteria from the latest PR discussion and the earlier roadmap
issues. CI verifies inventory coverage and fails when any row is unverified.

The source snapshot is arXiv:2611.34924v1, submitted 2026-11-25 18:58:55 UTC. The arXiv versioned PDF retrieved for this audit had SHA-256 `d17caccbee57cfbee6fc2eeed2e5a53467c9401be979fd2952aa2bf92d5443af`. The analysis uses the full text including Appendices A–E and the figures relevant to the arguments. Equation links target the versioned HTML. The issue had zero comments and zero registered sub-issues when inventoried. PR #120 had no conversation comments, inline comments or reviews at the initial inspection. [Paper PDF](https://arxiv.org/pdf/2611.34924v1) · [Paper HTML](https://arxiv.org/html/2611.34924v1) · [Issue #119](https://github.com/konard/physical-unified-theory/issues/119) · [PR #120](https://github.com/konard/physical-unified-theory/pull/120)

| Requirement in #119 | Approach and verification evidence | Status |
| --- | --- | --- |
| Compile issue-related data under `docs/case-studies/issue-119`. | Record the source version, primary literature, available repository components, prior PR evidence and reproduction commands in this directory. | Delivered |
| Do a deep case study and search online for additional facts and data. | Trace §§2–6 and Appendices A–E, including the distinction between open and closed gluing. Compare with characteristic evolution, Lorentzian replicas, Euclidean axioms and one-loop entropy literature. | Delivered |
| List every requirement and propose solutions and plans. | Map the paper’s dependencies and claims to executable checks and explicit conditions for accepting the remaining claims. | Delivered |
| Check existing libraries and components that can help. | Compare the repository, pinned Mathlib, Physlib and Rocq options against the proof obligations. | Delivered |
| Independently reformalize what is needed to prove or disprove the proposed unification. | Use two kernels for tractable real identities, Lean for actual Hilbert-space and convergence results, exact finite countermodels and a bounded numerical experiment. Develop the full characteristic and continuum quantum model and close the domain and trace obligations identified below. | Partial. No full four-dimensional construction or disproof of that construction. |
| Double-check delivery of #117. | Compare its issue tree and closure state with PR #118, CI, sources and its task-level implementation record. | Delivered. #117 itself was partial. |
| Plan and execute in one pull request. | Keep the audit, checked results, regression tests and unresolved acceptance criteria in PR #120. | Partial while the full verification criterion is open. |

[Primary sources and library choices](sources.md) · [Claim-by-claim analysis and proof plan](analysis.md) · [Reproducing the checks](verification.md)
