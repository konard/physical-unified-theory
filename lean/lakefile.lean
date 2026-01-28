import Lake
open Lake DSL

package «physical-unified-theory» where
  -- Grand unified theory of physics formalization
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- Pretty-print `fun a => ...` as `λ a => ...`
    ⟨`autoImplicit, false⟩  -- Disable auto-implicit arguments for clarity
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «PhysicalUnifiedTheory» where
  globs := #[.submodules `PhysicalUnifiedTheory]
  -- Automatically discovers and builds all .lean files in PhysicalUnifiedTheory/
