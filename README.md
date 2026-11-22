# JSP-000237 · Extremal densities of residue classes

For a finite list of positive moduli, choose one residue class per modulus. This Lean package gives the greatest and least possible natural densities of their union. The main theorem also proves that every common integer residue attains the minimum. Arbitrary integer representatives, repeated moduli, modulus one, and the empty family are included.

## Result

Let `L` be the least common multiple, `X = {0,…,L−1}`, and `B = 1 + ∏ᵢ nᵢ`. For each subset `S ⊆ X`, put

```text
A(S) = ∏ᵢ (nᵢ − |{x mod nᵢ : x ∈ S}|)
W = Σ_{S ⊆ X} (1−B)^|S| B^(L−|S|) A(S).
```

The maximum covered density is `floor(log_B W) / L`. The minimum is `|{x ∈ X : some nᵢ divides x}| / L`. The digit in position `k` of the base-`B` expansion of `W` counts the residue tuples that cover exactly `k` positions in a period. Position zero is the units digit. In particular, missing density levels appear as zero digits. Integer arithmetic suffices for all these formulas.

For moduli `(2,3,4,6)`, the period is 12. Of the 144 choices, 48 cover 8 positions, 72 cover 10, and 24 cover 11. The two extrema are 2/3 and 11/12. The natural density in the statement is the limit of the proportion in `[0,N)` as `N` tends to infinity.

## Proof

Fix a residue tuple. Write `U` for its set of missed positions. It contributes to `A(S)` precisely when `S ⊆ U`. Its total contribution to the signed sum is `B^(L−|U|)` by the binomial theorem on the subsets of `U`. Summing over tuples proves the digit formula because their total number is less than the base. Enumerating the formula visits `2^L` subsets. This can be substantially more expensive than direct enumeration or the published algorithms for sparse interactions.

For the minimum, first consider a prime-power period. Its divisors form a chain, so the union of the zero classes is the largest such class. A translate of that class alone already has the same size. For a period that is a product of coprime factors, the Chinese remainder theorem turns each class into a rectangle. Fix a point in one coordinate and apply the induction hypothesis to precisely the classes active there. Summation permits compressing the two coordinates successively to zero. Translation preserves the resulting cardinality. Finally, full periods and a remainder of length less than `L` give the natural-density limit.

## Reproduce

Use Lean 4.14.0 and the dependency revisions in `lake-manifest.json`. Start from this directory with the Lean toolchain manager and Git available.

```sh
lake exe cache get
lake build
lake env lean --trust=0 Prize.lean
lake env lean --trust=0 Histogram.lean
python verify_examples.py
```

The two axiom audits should list only `propext`, `Classical.choice`, and `Quot.sound`. The Python check uses only the standard library. It independently compares every histogram entry with exhaustive enumeration for 62 inputs. The uniform Lean proof supplies the result for arbitrary moduli.

| File | Verified result |
| --- | --- |
| `Prize.lean` | `ResidueCoverage.jsp000237` states both extrema for integer residue choices and the limit for every common shift. |
| `Main.lean` | Connects the integer logarithm formula to congruences and proves an optimizer exists. |
| `Coverage.lean` | Double-counting identity, exact integer sum, and extraction of the greatest attained exponent. |
| `Histogram.lean` | `ResidueCoverage.coverage_histogram` extracts the exact multiplicity of every attainable level. |
| `Minimum.lean` | Independent formal proof of the classical Rogers minimum and translation invariance. |
| `Density.lean` | Ordinary natural-density limit from counts on initial segments. |

See [prior evidence](PRIORITY.md) and the [review draft](SUBMISSION.md) for attribution, scope, and eligibility.

