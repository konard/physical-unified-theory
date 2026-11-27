# Reproduce the checks

## Kernel checks and bounded experiment

From the repository root, use its pinned Lean toolchain and Mathlib revision. CI fetches the cached imports, builds the library, then checks the new regression file alongside the existing tests.

```sh
cd lean
lake build
lake env lean tests/NullCone.lean
```

For a focused local check after fetching the relevant Mathlib objects, build just the module and check the regression file in the project environment.

```sh
cd lean
mkdir -p .lake/build/lib/lean/PhysicalUnifiedTheory/Unification
lake env lean -o .lake/build/lib/lean/PhysicalUnifiedTheory/Unification/NullCone.olean \
  PhysicalUnifiedTheory/Unification/NullCone.lean
lake env lean tests/NullCone.lean
```

The Lean module also checks the integrating factor in (3.26), the error from inserting finitely many contractions in (4.31), the exact resolvent tangent deficit, the eventual trace bound from a positive replica limit, and the finite covariance contraction in (6.12)–(6.13). These theorems expose their assumptions in their signatures.

Rocq CI runs the entries in `_CoqProject` under Rocq 9.0. The independent real-number proofs and their regressions can be checked directly.

```sh
cd rocq
rocq compile -R theories PhysicalUnifiedTheory theories/Unification/NullCone.v
rocq compile -R theories PhysicalUnifiedTheory tests/NullCone.v
```

The numerical experiment uses Python’s standard library, fixed cutoffs no larger than 8192, and exact rational calculations for the trace, clock countermodel and entropy coefficient. The radial comparisons are floating point with a small roundoff allowance. Run it from the repository root.

```sh
python3 experiments/null_cone.py -v
```

| Check | Reproduction result |
| --- | --- |
| Fixed-area radial sum | Compare cutoffs $N$ and $2N$ at $s=0.5,\,2,\,100$ with $N=16,\,128,\,1024$. The difference stays within $1/(2s^2N)$. |
| Cubic quotient near zero coupling | At $t=10^{-7}$ and $N=16,\,128,\,1024,\,8192$, the negative imaginary quotient agrees with the positive harmonic sum within the sine Taylor test bound and increases with $N$. |
| Trace and replica ratio | With weight $2/3$, increasing the cut from 16 to 128 raises the trace from $32/3$ to $256/3$ and decreases exact purity from $1/16$ to $1/128$. |
| Clock resolvent | At $L=3$, cutoff 16 has overlap $3/19$ and cutoff 1024 has overlap $3/1027$. Each overlap is positive and the Lean limit is zero. |
| Entropy coefficient | The fixed-mass arithmetic reproduces $106/45$ exactly. |

[Lean theorems](../../../lean/PhysicalUnifiedTheory/Unification/NullCone.lean) · [Lean regressions](../../../lean/tests/NullCone.lean) · [Rocq theorems](../../../rocq/theories/Unification/NullCone.v) · [Rocq regressions](../../../rocq/tests/NullCone.v) · [Experiment](../../../experiments/null_cone.py)

## GitHub and source evidence

The issue metadata and three categories of review on PR #120 can be fetched independently. The same API paths on #117 and #118 reproduce the earlier status audit. Recursing through the 20 direct children of #117 yields #34 through #115 without duplicates.

```sh
gh issue view https://github.com/konard/physical-unified-theory/issues/119
gh api repos/konard/physical-unified-theory/issues/119/comments --paginate
gh api repos/konard/physical-unified-theory/issues/119/sub_issues --paginate
gh api repos/konard/physical-unified-theory/issues/120/comments --paginate
gh api repos/konard/physical-unified-theory/pulls/120/comments --paginate
gh api repos/konard/physical-unified-theory/pulls/120/reviews --paginate

gh api repos/konard/physical-unified-theory/issues/117/sub_issues --paginate \
  --jq '.[].number'
gh pr view 118 --repo konard/physical-unified-theory --json closingIssuesReferences,mergeCommit
git diff --stat d575b3cd^1 d575b3cd
```

The PDF checksum in the [case-study overview](README.md) can be reproduced by downloading the versioned PDF from arXiv and running `sha256sum` on it. The repository keeps the detailed findings, direct links and experiments. arXiv hosts the full versioned source.
