# Extremal densities of unions of residue classes

Given positive integers $n_1,\ldots,n_r$, choose one residue class modulo each. How much of the integer line can their union cover, and how little? This Lean 4 project proves both extrema for **Erdős problem 278 (JSP-000237)**. It also counts how many choices give each possible density.

[Read the mathematical proof](PROOF.md) · [Inspect the main Lean theorem](Prize.lean#L55) · [View the prize submission (PR #5626)](https://github.com/TheJustinSunPrize/awards/pull/5626)

## Result

Every choice repeats with period $L=\operatorname{lcm}(n_1,\ldots,n_r)$. Its natural density is the fraction of positions it covers in $X=\{0,\ldots,L-1\}$. Thus a tuple covering $k$ positions in one period has density $k/L$.

**Minimum.** Choose residue zero at every modulus. The union then consists of the integers divisible by at least one of the moduli. The Rogers–Simpson minimum theorem says that this choice attains the least possible density. Choosing the same integer $t$ at every modulus translates the union and gives the same minimum.

**Maximum.** The following integer $W$ encodes every coverage count. Let $T=\prod_i n_i$ be the number of labelled residue tuples, $B=T+1$, and $e_i(S)$ the number of distinct residues modulo $n_i$ represented by the elements of $S$. Set

```math
W=\sum_{S\subseteq X}(1-B)^{|S|} B^{L-|S|}
       \prod_{i=1}^{r}\bigl(n_i-e_i(S)\bigr).
```

The base-$B$ digit of $W$ in position $k$ counts the tuples with density $k/L$, with position zero denoting the units digit. The highest occupied position therefore gives the maximum. In formulas,

```math
\min_a d(a)=\frac{|\{x\in X:n_i\mid x\text{ for some }i\}|}{L},
\qquad
\max_a d(a)=\frac{\lfloor\log_B W\rfloor}{L}.
```

Both extrema are attained. The theorem permits arbitrary integer representatives, repeated moduli, the modulus one, and the empty family. Direct evaluation of $W$ uses integer arithmetic and has $2^L$ subset terms.

### Example

For moduli $(2,3,4,6)$ there are $144$ residue tuples and the period is $12$. Only three densities occur.

| Positions covered in one period | Natural density | Number of tuples |
| ---: | ---: | ---: |
| 8 | 2/3 | 48 |
| 10 | 5/6 | 72 |
| 11 | 11/12 | 24 |

The tuple $(0,0,0,0)$ attains the minimum of $2/3$. The tuple $(0,0,1,1)$ attains the maximum of $11/12$ and misses only the residue $11$ modulo $12$. [Derivation of all three counts](PROOF.md#a-worked-example)

## Proof

For the maximum, the product in the sum counts tuples missing every point of $S$. Grouping the terms by tuple shows that a tuple covering $k$ positions contributes exactly $B^k$. Since only $B-1$ tuples exist, their counts fit in the base-$B$ digits of $W$. [Maximum and digit formula](PROOF.md#maximum-and-counts-at-each-density)

For the minimum, the divisors of a prime power form a chain. The largest chosen class already has as many elements as the union of the zero classes. For a product of coprime periods, the Chinese remainder theorem expresses each class as a rectangle. Applying the smaller-period inequality first to each row and then to each column shows that moving all residues to zero can only decrease the union size. [Minimum and the common residue](PROOF.md#minimum-and-the-common-residue)

## Reproduce

From the repository root, use the pinned Lean 4.14.0 toolchain and mathlib dependencies. The last command runs an independent enumeration with Python 3.9 or later and uses only the standard library.

```sh
lake exe cache get
lake build
lake env lean --trust=0 Prize.lean
lake env lean --trust=0 Histogram.lean
python verify_examples.py
```

The axiom reports for both theorems list only `propext`, `Classical.choice`, and `Quot.sound`. The Python script compares the complete histogram against direct enumeration on 62 small inputs, including the example above.

| Lean source | What it proves |
| --- | --- |
| [Prize.lean](Prize.lean#L55) | `ResidueCoverage.jsp000237` gives both attained extrema for integer residue choices and the limit for each common shift. |
| [Histogram.lean](Histogram.lean#L49) | `ResidueCoverage.coverage_histogram` extracts the multiplicity at each level, including zero counts. |
| [Coverage.lean](Coverage.lean) | The double-counting identity and the signed sum encoding coverage. |
| [Main.lean](Main.lean) | The maximum-density formula for residue classes and the existence of a maximizing choice. |
| [Minimum.lean](Minimum.lean) | The classical minimum over one period and its invariance under a common shift. |
| [Density.lean](Density.lean) | Convergence of the proportions on initial segments to the covered fraction of a period. |

The submission requests review in the Lean formalization category. Onishi previously formalized the general maximum. The submission record identifies the proof version, and the attribution notes describe the earlier mathematics and Lean results. [Submission record](SUBMISSION.md) · [Prior work and attribution](PRIORITY.md)
