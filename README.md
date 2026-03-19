# Physical Unified Theory

A formalization project toward the grand unified theory of physics in the **Lean** and **Rocq** proof assistants.

## Vision

Create rigorous, machine-verified formalizations of:

1. **Quantum Mechanics** - From postulates to quantum field theory
2. **General Relativity** - From special relativity to Einstein's equations
3. **Unification** - Explore approaches to merging these theories

## Why Formal Verification?

- **Mathematical Rigor**: Every step is verified by the proof assistant
- **Reproducibility**: Proofs can be checked and built upon by anyone
- **Clarity**: Formal definitions expose hidden assumptions
- **Foundation**: A solid base for exploring unification approaches

## Project Structure

```
physical-unified-theory/
├── lean/                          # Lean 4 formalizations
│   ├── PhysicalUnifiedTheory/
│   │   ├── Foundations/           # Hilbert spaces, differential geometry
│   │   ├── QuantumMechanics/      # QM postulates, operators, systems
│   │   ├── GeneralRelativity/     # Spacetime, metrics, Einstein equations
│   │   └── Unification/           # Approaches to quantum gravity
│   ├── lakefile.lean
│   └── lean-toolchain
├── rocq/                          # Rocq (Coq) formalizations
│   ├── theories/
│   │   ├── Foundations/
│   │   ├── QuantumMechanics/
│   │   ├── GeneralRelativity/
│   │   └── Unification/
│   └── _CoqProject
├── docs/                          # Documentation
│   ├── GLOSSARY.md
│   ├── QUANTUM_MECHANICS.md
│   ├── GENERAL_RELATIVITY.md
│   └── UNIFICATION_CHALLENGES.md
├── ROADMAP.md                     # Detailed project roadmap
├── CONTRIBUTING.md                # How to contribute
└── LICENSE
```

## Getting Started

### Lean 4

```bash
# Install Elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build the project
cd lean
lake build
```

### Rocq

```bash
# Using Docker
docker run -it --rm -v $(pwd)/rocq:/work -w /work rocq/rocq-prover:9.0 \
  bash -c "rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq"

# Or install locally via opam
opam install rocq
cd rocq
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

## Current Status

This is an early-stage project. We are currently working on:

- [x] Project structure and CI/CD setup
- [x] Basic Lean 4 formalization infrastructure
- [x] Basic Rocq formalization infrastructure
- [x] Documentation of roadmap and physics background
- [ ] Mathematical foundations (Hilbert spaces, manifolds)
- [ ] Quantum mechanics basics (qubits, gates, measurement)
- [ ] Special relativity (Minkowski spacetime, Lorentz transformations)

See [ROADMAP.md](ROADMAP.md) for the detailed plan.

## Documentation

- [ROADMAP.md](ROADMAP.md) - Full project roadmap with phases
- [docs/GLOSSARY.md](docs/GLOSSARY.md) - Key physics and math terms
- [docs/QUANTUM_MECHANICS.md](docs/QUANTUM_MECHANICS.md) - QM formalization guide
- [docs/GENERAL_RELATIVITY.md](docs/GENERAL_RELATIVITY.md) - GR formalization guide
- [docs/UNIFICATION_CHALLENGES.md](docs/UNIFICATION_CHALLENGES.md) - The unification problem

## Related Projects

- [Mathlib](https://github.com/leanprover-community/mathlib4) - Mathematical library for Lean 4
- [PhysLean](https://physlean.com/) - Physics formalization in Lean
- [Lean-QuantumInfo](https://github.com/duckki/lean-quantum) - Quantum computing in Lean
- [Mathematical Components](https://math-comp.github.io/) - Rocq/Coq math library

## Contributing

We welcome contributions! See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

Priority areas:
- Mathematical foundations
- Simple quantum systems
- Special relativity
- Documentation improvements

## References

### Physics
- Sakurai, "Modern Quantum Mechanics"
- Wald, "General Relativity"
- Kiefer, "Quantum Gravity"

### Formalization
- [PhysLean: Digitalizing Physics](https://physlean.com/)
- [Elements of Differential Geometry in Lean](https://arxiv.org/abs/2108.00484)
- [Index Notation in Lean 4](https://arxiv.org/abs/2411.07667)

## License

This project is released into the **public domain** under [The Unlicense](LICENSE).

### Why The Unlicense?

The Unlicense is a public domain dedication with key advantages over other license models:

- **No restrictions**: Unlike MIT, Apache, or GPL, The Unlicense imposes **zero obligations** on users. No attribution required, no license file to carry around, no conditions to comply with.
- **Maximum freedom**: Anyone can copy, modify, publish, use, compile, sell, or distribute this work — for any purpose, commercial or non-commercial — without asking permission.
- **Truly free for AI/ML training**: Other licenses (even permissive ones like MIT) may require attribution in derivative works, which is complex for model training datasets. The Unlicense removes this barrier entirely.
- **No copyright headers needed**: Contributors don't need to add copyright notices to source files. The work belongs to everyone.
- **Simpler than Creative Commons Zero (CC0)**: The Unlicense is specifically designed for software and is simpler and more widely understood in the software community than CC0.
- **Encourages open science**: For a scientific formalization project, maximum openness accelerates research — anyone can build on this work without legal friction.

In short: The Unlicense is the most permissive option available, making this project as open as possible for researchers, educators, and developers worldwide.

---

*"The universe is not only queerer than we suppose, but queerer than we can suppose."*
— J.B.S. Haldane

*Let us at least make it as rigorous as we can verify.*
