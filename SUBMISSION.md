# Draft for technical review of JSP-000237

## Requested evaluation

Please evaluate the Lean formalization against the catalogue question about the maximum and minimum covered densities for prescribed moduli, corresponding to Erdős problem 278. Please assess the admissibility of the finite formula and the scope of earlier formalizations before making any priority decision. This request concerns formalization credit. Rogers, Simpson and the authors of earlier maximum-density results are credited in [the prior-evidence record](PRIORITY.md).

## Scope and result

Given any finite list of positive integers and any integer residue for each one, `ResidueCoverage.jsp000237` in `Prize.lean` proves the greatest attainable natural density and the least attainable natural density. It proves the minimum is attained at every common integer residue, and the maximum is attained by at least one choice. The density is explicitly a limit of counts on initial integer segments.

The formula for the maximum uses only the moduli, a finite sum over subsets of one period, and an integer logarithm. The companion theorem `ResidueCoverage.coverage_histogram` counts choices at every coverage level, including levels with count zero. The sum has one term for each of the `2^L` subsets of the least-common-multiple period. Whether this characterization answers the intended extremal question to the committee’s standard is a matter for mathematical review. [Formula, argument and reproduction](README.md)

## Provenance and verification

The proof code was written in this local project using OpenAI Codex. The September 2026 Onishi repository gives an earlier Lean formalization for the maximum using a different characterization. This draft makes no claim to priority for formalizing that extremum in isolation. The main theorem and the histogram theorem were checked using Lean 4.14.0 and the pinned mathlib with the three standard axioms.

## Release record

This is a private pre-submission draft. The package contains the original source, dependency lock, and reproduction commands. For an actual application the applicant's public repository URL, branch, full proof commit, independently checkable public history, and attributable public identity would need to be recorded. Those facts can be added after an authorized public release. This draft provides no identity or payment information.

