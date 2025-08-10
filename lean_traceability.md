# LFT Lean 4 Traceability Matrix

This document maps:
1. **Reviewer feedback priorities** from *LFT Paper Revision Summary – Priority Improvements*
2. **Collaborator Lean development tasks** from *Lean Development Guidance for LFT*
3. **Our current Lean Next Steps plan**
4. **Status / Action**

---

| Reviewer Priority (Paper) | Collaborator Lean Task | Our Current Lean Next Step | Status / Action |
|---------------------------|------------------------|----------------------------|-----------------|
| Remove circular derivations (Hilbert, Born rule) | Priority 2 – `complex_from_excluded_middle` theorem | Section 4.4 proof stub in Lean; derive complex necessity without QM postulates | **Pending** – start after core strain components complete |
| Quantitative worked examples for strain | Priority 1 – `StrainExamples.lean` with sample graphs | Step 6 – Golden tests for small graphs | **To Do** – can implement in parallel with `vI` |
| Max-entropy weight derivation (1:2:1) | Priority 2 – `strain_weights_unique` theorem | Will follow once `vI`, `vN`, `vE` formalized | **Deferred** until all three components are implemented |
| Stronger measurement/threshold section | Priority 1 – Implement `Measurement.lean` and `ForkGraph` | Not in current immediate plan; will follow after strain core | **Pending** – start after Step 6 golden tests |
| Explicit experimental prediction tables | Priority 3 – `Predictions.lean` for null outcomes | Outside current Lean scope; reference only for paper | **Deferred** – post-measurement work |
| Better link between theory and empirical test | Priority 1 – Annotate lemmas with experimental hooks | Could tag lemmas in `Strain.lean` with comments mapping to paper | **Optional now** – can annotate as we go |
| Clarify role of PEM in complex structure | Priority 2 – `complex_from_excluded_middle` theorem | Section 4.4 target | **Same as first row** – treat as single milestone |
| Reduce claim strength; emphasize falsifiability | Not a Lean coding item | N/A | **Handled in paper only** |
| More visual aids & conceptual examples | Priority 4 – `Examples.lean` with diagram exports | Golden tests + docstrings could cover minimal need | **Partial** – focus on testable examples now |

---

## Suggested Execution Order in Lean
1. Finish **Graph helpers** → `vI` → `vN` → `vE` (Steps 1–4)
2. Implement **Golden tests / StrainExamples.lean** (ties to reviewer “worked examples”)
3. Once strain complete, move to **Measurement.lean** with `ForkGraph` (ties to reviewer “measurement/threshold”)
4. Only then tackle **complex_from_excluded_middle** and **weight uniqueness** theorems (ties to circularity removal and max-entropy)
5. After that, integrate **Predictions.lean** and any experimental mapping

---

## Maintenance
- Update this table whenever a task moves from **Pending** → **In Progress** → **Done**.
- Cross-link to corresponding Lean commit hashes when implemented.
- Ensure paper revisions stay consistent with formal Lean proofs.

