# Logic Field Theory – Lean 4 Formalization

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.16788881.svg)](https://doi.org/10.5281/zenodo.16788881)
[![License: CC BY-NC-SA 4.0](https://img.shields.io/badge/Theory-CC%20BY--NC--SA%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by-nc-sa/4.0/)
[![License: MIT](https://img.shields.io/badge/Code-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Overview

This repository contains the **machine-verifiable formalization** of *Logic Field Theory (LFT)* in **Lean 4**, based on the v3.0 paper:

> **Logic Field Theory: Deriving Quantum Mechanics from the Three Fundamental Laws of Logic**  
> James D. Longmire  
> Northrop Grumman Fellow (unaffiliated research)  
> ORCID: 0009-0009-1383-7698  
> August 10, 2025

LFT is a **logic-first derivation** of quantum mechanics. It shows that the mathematical structure of QM—complex Hilbert spaces, unitary evolution, and the Born rule—emerges **necessarily** from the requirement that reality remain logically consistent under superposition, given the **Three Fundamental Laws of Logic (3FLL)**:

1. **Identity**: $A = A$
2. **Non-Contradiction**: $\neg (A \land \neg A)$
3. **Excluded Middle**: $A \lor \neg A$

Unlike interpretations of QM that assume the formalism, LFT derives it from **graph-theoretic logical structures** and a **strain functional** $D(G)$ defined via maximum entropy principles.

## 📚 Citation

If you use Logic Field Theory in your research, please cite:

```bibtex
@misc{longmire2025lft,
  author       = {Longmire, James D.},
  title        = {Logic Field Theory: Deriving Quantum Mechanics from the Three 
                   Fundamental Laws of Logic (v3.0)},
  year         = {2025},
  month        = {8},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.16788881},
  url          = {https://doi.org/10.5281/zenodo.16788881},
  version      = {3.0}
}
```

## 🔗 Quick Links

- 📖 [Read the Paper (v3.0)](Working_Papers/Logic_Field_Theory___Foundations_v3.0.pdf)
- 🔢 [View on Zenodo](https://zenodo.org/uploads/16788881)  
- 🏗️ [Lean Proofs](LFT/)
- 📊 [Experimental Predictions](docs/predictions.md)

## Project Goals

* **Primary:** Fully mechanize the LFT derivation in Lean 4, from logical axioms to testable quantum predictions.
* **Secondary:** Provide a modular library for formal reasoning about pre-quantum logical structures.
* **Tertiary:** Support experimental and theoretical research by producing machine-verified lemmas and theorems from the LFT framework.

## Repository Structure

```
LFT/
  Basic.lean       # Three Fundamental Laws of Logic as axioms
  Graphs.lean      # Directed graph structures, entailment relations, admissibility
  Strain.lean      # Logical strain functional scaffold (vI, vN, vE)
  Dynamics.lean    # Hilbert space emergence, unitary evolution, Schrödinger derivation
  Tests.lean       # Unit tests for definitions and proofs
```

* **`LFT/Basic.lean`**  
  Encodes the 3FLL in Lean as foundational axioms.

* **`LFT/Graphs.lean`**  
  Defines **logical graphs**: vertices as propositions, directed edges as entailment. Includes admissibility checks for 3FLL compliance and graph operations (tensor product, superposition).

* **`LFT/Strain.lean`**  
  Implements the **strain functional**:

  $$D(G) = w_I v_I(G) + w_N v_N(G) + w_E v_E(G)$$

  with placeholders for:
  * `vI` – **Identity violations** (path-proximity metric, Eq. (8) in paper)
  * `vN` – **Non-decidability** (entropy measure, Eq. (9))
  * `vE` – **Environmental misfit** (boundary mismatch, Eq. (10))

* **`LFT/Dynamics.lean`**  
  Will implement:
  * Hilbert space emergence (Section 5)
  * Logical Lagrangian and Schrödinger equation (Section 6.2–6.3)
  * Born rule derivation (Sections 6.6 & 7.5)

## Current Status

### **Branch**
`main`

### **Build**
✅ Clean compile:
```bash
lake build
lake build LFT.Strain
```

### **Checkpoint Tag**
`lft-lean4-checkpoint` – safe rollback point.

### **Implemented**
* Graph scaffold (`Graphs.lean`)
* Strain functional skeleton with weighted components (`Strain.lean`)
* 3FLL axioms (`Basic.lean`)
* Minimal tests and lemmas

### **Placeholders Remaining**
* Full path-proximity metric for `vI`
* Entropy-based calculation for `vN`
* Observational mismatch metric for `vE`
* Proofs of convexity, metric properties, and compositional additivity

## Roadmap

### **Phase 1 – Core Definitions**
1. Implement `vI`, `vN`, and `vE` per v3.0 paper definitions (Section 4.3).
2. Prove `D(G) = 0` iff $G$ is classically consistent.
3. Define admissible graph space $\Omega$.

### **Phase 2 – Hilbert Space Embedding**
4. Formalize graph superposition (Section 3.5.1).
5. Prove complex necessity from Excluded Middle (Section 5.3).
6. Derive Hermitian inner product from logical distinguishability.

### **Phase 3 – Dynamics**
7. Implement Logical Lagrangian (Eq. (30)).
8. Derive Schrödinger equation (Eq. (31)).
9. Prove unitarity and energy-strain correspondence.

### **Phase 4 – Measurement & Predictions**
10. Implement measurement threshold criterion (Eq. (44)).
11. Formalize Born rule derivation with strain corrections (Eq. (55)).
12. Encode testable predictions for simulation.

## How to Build

```bash
# Install Lean 4 and Lake
lake update

# Build the project
lake build

# Run all tests
lake exe test
```

## 📄 License

This project uses a dual licensing approach:

### Theory Paper

<a href="https://github.com/jdlongmire/logic_field_theory_foundations_lean/blob/main/Working_Papers/Logic_Field_Theory___Foundations_v3.0.pdf">Logic Field Theory: Deriving Quantum Mechanics from the Three Fundamental Laws of Logic</a> © 2025 by <a href="https://github.com/jdlongmire">James D. Longmire</a> is licensed under <a href="https://creativecommons.org/licenses/by-nc-sa/4.0/">CC BY-NC-SA 4.0</a> <img src="https://mirrors.creativecommons.org/presskit/icons/cc.svg" alt="" style="height:22px!important;margin-left:3px;vertical-align:text-bottom;"><img src="https://mirrors.creativecommons.org/presskit/icons/by.svg" alt="" style="height:22px!important;margin-left:3px;vertical-align:text-bottom;"><img src="https://mirrors.creativecommons.org/presskit/icons/nc.svg" alt="" style="height:22px!important;margin-left:3px;vertical-align:text-bottom;"><img src="https://mirrors.creativecommons.org/presskit/icons/sa.svg" alt="" style="height:22px!important;margin-left:3px;vertical-align:text-bottom;">

**This means you can:**
- ✅ Share and adapt the theory with attribution
- ✅ Use for non-commercial research and education  
- ✅ Build upon the work if you share under the same license
- ✅ Translate and create derivative works

**Restrictions:**
- ❌ Commercial use requires permission
- ❌ Must give appropriate credit
- ❌ Must share adaptations under CC BY-NC-SA 4.0

### Lean Code

All Lean formalizations in this repository are licensed under the [MIT License](LICENSE) for maximum reusability in formal verification projects.

### Contributing

By contributing to this repository, you agree that your contributions to the Lean code will be licensed under MIT, while contributions to the theory documentation will be licensed under CC BY-NC-SA 4.0.

## References

This formalization tracks directly to:

* Longmire, J.D. *Logic Field Theory: Deriving Quantum Mechanics from the Three Fundamental Laws of Logic*, v3.0, 2025. DOI: [10.5281/zenodo.16788881](https://doi.org/10.5281/zenodo.16788881)
* [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)

For full theoretical background, see **Sections 2–8** of the LFT v3.0 paper, which define all constructs formalized here.

## Contributing

We are looking for collaborators interested in:

* Lean 4 theorem proving
* Quantum foundations
* Graph theory and category theory
* Information theory

## 📧 Contact & Author

### About the Author

**James (JD) Longmire** is a **Northrop Grumman Fellow** (unaffiliated research), **Senior Systems Architect**, and **AI researcher** with extensive experience in complex systems integration, artificial intelligence, and emergent organizational structures. This interdisciplinary background in digital engineering ecosystems, AI development, and systems architecture informs the systematic analytical methodology applied to foundational questions about reality's organizational hierarchy.

**Contact Information:**

* **ORCID:** [0009-0009-1383-7698](https://orcid.org/0009-0009-1383-7698)
* **Email:** [longmire.jd@gmail.com](mailto:longmire.jd@gmail.com)
* **GitHub:** [@jdlongmire](https://github.com/jdlongmire)
