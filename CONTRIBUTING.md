# Contributing to Physical Unified Theory

Thank you for your interest in contributing to this project! We welcome contributions from physicists, mathematicians, and formal verification enthusiasts.

## Project Overview

This project aims to formalize quantum mechanics and general relativity in the Lean and Rocq proof assistants, with the ultimate goal of exploring their unification.

## Getting Started

### Prerequisites

#### For Lean Development
1. Install [Elan](https://github.com/leanprover/elan) (Lean version manager):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. Build the project:
   ```bash
   cd lean
   lake build
   ```

#### For Rocq Development
1. Install Rocq via [opam](https://opam.ocaml.org/):
   ```bash
   opam install rocq
   ```

   Or use Docker:
   ```bash
   docker pull rocq/rocq-prover:9.0
   ```

2. Build the project:
   ```bash
   cd rocq
   rocq makefile -f _CoqProject -o Makefile.coq
   make -f Makefile.coq
   ```

### Understanding the Codebase

- `ROADMAP.md` - Overall project roadmap and phases
- `docs/` - Background documentation
- `lean/` - Lean 4 formalizations
- `rocq/` - Rocq formalizations

## How to Contribute

### 1. Pick an Item from the Roadmap

The `ROADMAP.md` contains detailed phases with specific items. Look for unchecked items (`[ ]`) that match your interests and expertise.

### 2. Open an Issue to Discuss

Before starting significant work:
1. Open an issue describing what you plan to work on
2. Discuss the approach with maintainers
3. Get feedback before investing significant time

### 3. Fork and Create a Branch

```bash
git checkout -b feature/your-feature-name
```

### 4. Write Your Code

Follow the existing code style:
- Use meaningful names for definitions and lemmas
- Add documentation comments
- Include references to relevant physics/math literature

### 5. Ensure CI Passes

Before submitting:
- Lean: `lake build` succeeds
- Rocq: `make -f Makefile.coq` succeeds
- All existing tests pass

### 6. Submit a Pull Request

- Provide a clear description of your changes
- Reference any related issues
- Be responsive to review feedback

## Code Style Guidelines

### Lean

```lean
/-!
# Section Title

Brief description of this file.

## Main Definitions

* `FooBar` - description
* `baz_theorem` - description

## References

* [Author, "Paper Title"]
-/

/-- A brief docstring for the definition.
More details if needed. -/
def someDefinition : Type := ...

/-- Brief theorem statement.
Proof idea or reference. -/
theorem some_theorem : ... := by
  -- tactics here
  sorry
```

### Rocq

```coq
(** * Section Title

    Brief description of this file.

    Main definitions:
    - [foo_bar]: description
    - [baz_theorem]: description

    References:
    - Author, "Paper Title"
*)

(** [some_definition] is ... *)
Definition some_definition : Type := ...

(** [some_theorem] states that ...

    Proof idea: ... *)
Theorem some_theorem : ...
Proof.
  (* tactics here *)
Admitted.
```

## Physics Conventions

### Units

We use **natural units** where:
- ℏ = 1 (reduced Planck constant)
- c = 1 (speed of light)
- G = 1 (gravitational constant, unless comparing scales)

### Metric Signature

We use the **(-,+,+,+)** convention for spacetime:
- Timelike: ds² < 0
- Spacelike: ds² > 0
- Lightlike: ds² = 0

### Notation

- Quantum states: |ψ⟩ (Dirac notation in comments)
- Operators: A, B (in code), Â, B̂ (in documentation)
- Tensors: Standard index notation in documentation

## Priority Areas

We especially welcome contributions in:

1. **Mathematical Foundations**
   - Hilbert space infrastructure
   - Differential geometry additions
   - Tensor algebra

2. **Quantum Mechanics**
   - Basic quantum systems
   - Quantum gates and circuits
   - Measurement theory

3. **Special Relativity**
   - Lorentz transformations
   - Four-vector formalism

4. **Documentation**
   - Improving existing docs
   - Adding examples
   - Tutorials

## Communication

- **Issues**: For bug reports, feature requests, and discussions
- **Pull Requests**: For code contributions
- **Discussions**: For broader topics and questions

## License

By contributing, you agree that your contributions will be licensed under the MIT License.

## Questions?

If you have questions about:
- The project direction: Open an issue
- Technical setup: Check the README or open an issue
- Specific physics/math: Reference the `docs/` directory or ask

We appreciate your contribution to this ambitious project!
