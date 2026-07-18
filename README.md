<!-- FILENAME: README.md -->

# Chiral Gauge Dynamics (CGD)

[![DOI](https://zenodo.org/badge/DOI/PLACEHOLDER.svg)](https://doi.org/10.5281/zenodo.PLACEHOLDER)

Chiral Gauge Dynamics (CGD) is a background-independent formulation of physics derived entirely from a classical $\text{Spin}(4, \mathbb{C})$ gauge connection.

This repository contains the rigorous mathematical proofs of the theory, formalized in the Lean4 interactive theorem prover, alongside the LaTeX source for the resulting scientific manuscripts.

**[Read the Foundational Paper (PDF)](papers/cgd-foundations/paper.pdf)**

## Key Formalized Results

By treating the universe strictly as a continuous gauge field, CGD bypasses the need for fundamental quantization, extra dimensions, or an independent spacetime metric. The Lean4 formalization proves that the following phenomena natively emerge from the classical topology of the field:

*   **Emergent Gravity:** General Relativity (specifically unimodular gravity) intrinsically emerges from the self-dual chiral sector via the Urbantke metric.
*   **Particles & Mass Gap:** Fermions are not fundamental 0-dimensional points; they are topologically stable knots in the anti-self-dual sector. A positive mass gap is geometrically guaranteed by the Cartan-Maurer topological integral.
*   **Self-Interacting Dark Matter (SIDM):** Topological defects in the self-dual (gravity) sector natively decouple from normal matter and light, yielding exact kinematic profiles for SIDM.
*   **Quantum Mechanics from Geometry:** The Dirac equation, quantum entanglement bounds (the CHSH Tsirelson bound), and the Born rule emerge without requiring Hilbert space quantization.
*   **Hadronic Phenomenology:** The formalization geometrically derives the kinematic sign-flips for the Sivers and Boer-Mulders effects. Furthermore, the topology strictly mandates the existence of an axial-vector condensate, yielding a vacuum screening model that aligns with high-$Q^2$ polarization transfer data from the proton radius puzzle.

## The Philosophy: Math Dictates Viability, Data Dictates Reality

For decades, the foundational assumption of theoretical physics has been that the universe *must* be fundamentally quantized. The primary goal of this repository is to mathematically demonstrate that a classical theory is a viable alternative. By formalizing the geometry of $\text{Spin}(4, \mathbb{C})$ in Lean4, we demonstrate that phenomena traditionally assumed to require explicit quantization emerge from the classical topology of the field.

**We do not claim that the universe *is* classical.**
Making definitive claims about the fundamental ontology of the universe is the provenance of experimentalists and hard data.

However, we are publishing this because the mathematical structures that pop out of this specific connection are strikingly similar to our observed universe. There is no way we would have subjected ourselves to the process of formalizing this entire theory in Lean4 if the math didn't heavily imply that this *could* be our universe.

The formalization eliminates derivation errors. The next step is determining if this geometry maps to experimental data.

## Getting Started

### 1. Installation
This project uses [Nix](https://nixos.org/download) to ensure a perfectly reproducible environment, avoiding Lean/Lake version mismatch hell.

```bash
# Enter the reproducible shell (downloads Lean4 and dependencies automatically)
nix develop

# Build the Lean4 formalization
lake build

# View a list of theorems
cgd-report --dashboard
```

### 2. Litlib Dependencies
This project relies heavily on **[Litlib](https://github.com/LoganEvans/litlib4)** to bridge the gap between unformalized peer-reviewed literature and strict Lean4 theorems.

If you are browsing the code, you will frequently see `@[litlib_track]` macros and theorem signatures explicitly requesting `Litlib` typeclasses. This ensures that any time CGD relies on a historical mathematical physics paper (e.g., Papapetrou, Belavin, Urbantke), the boundary conditions are explicitly parameterized and auditable.
