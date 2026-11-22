# Technical submission for JSP-000237

This repository accompanies the submission for Erdős problem 278 in the Justin Sun Prize Lean formalization category. The catalogue entry asks for the maximum and minimum densities covered by one residue class per prescribed modulus. [Prize submission (PR #5626)](https://github.com/TheJustinSunPrize/awards/pull/5626)

## Material for review

| Item | Public record |
| --- | --- |
| Original Lean proof | [Commit 717bb98 on the submitting repository’s main branch](https://github.com/jackanderson123456/jsp000237-lean/commit/717bb98f744ba6f17c662dfbfe1134aa5ad5d1de) |
| Standalone English proof cited in the PR | [Manuscript at commit 3b38f8a](https://github.com/jackanderson123456/jsp000237-lean/blob/3b38f8aa5d8efb2953ef823be8b6886f1b3f8050/PROOF.md) |
| Local reproduction | [Build commands and expected checks](README.md#reproduce) |

## Scope and requested review

For any finite list of positive moduli, `ResidueCoverage.jsp000237` proves that the greatest and least natural densities of the union are both attained. The residues may be arbitrary integers. Every common residue attains the minimum. Here natural density is the limit of the fraction of covered integers in the initial segment from zero to $N-1$ as $N$ tends to infinity. [Main Lean theorem](Prize.lean#L55) · [Proof of the density limit](PROOF.md#one-period-gives-the-natural-density)

The maximum is obtained from a finite sum in the moduli alone. In base $B$, each digit of this sum counts the choices attaining a given density. The highest occupied digit determines the maximum. Direct evaluation involves $2^L$ subsets, where $L$ is the least common multiple of the moduli. We ask reviewers to assess this characterization in light of the catalogue question and the scope of earlier formalizations. [Mathematical derivation](PROOF.md#maximum-and-counts-at-each-density) · [Lean digit theorem](Histogram.lean#L49)

## Attribution and verification

The submitting account is `jackanderson123456`. The user initiated the research, and OpenAI Codex developed the Lean code and wrote the proof. Rogers and Simpson are credited for the classical minimum. Onishi’s September 2026 Lean project already proves an attained general maximum using a different characterization. The requested review concerns the joint result on both extrema and the formula for the full distribution of coverage counts. [Prior work and attribution](PRIORITY.md)

The six proof modules were checked with Lean 4.14.0 and the pinned mathlib revision. The axiom reports for the main theorem and the digit theorem list only `propext`, `Classical.choice`, and `Quot.sound`. The independent enumeration agrees on all 62 sample inputs. [Toolchain](lean-toolchain) · [Dependency lock](lake-manifest.json) · [Enumeration script](verify_examples.py)
