# Extremal densities of unions of residue classes

**JSP-000237 · Erdős problem 278**

Given positive moduli $n_1,\ldots,n_r$, choose one residue class modulo each. What are the largest and smallest possible natural densities of their union? We give a formula in the moduli alone for each extremum. The formula for the maximum also counts how many choices attain each density. The minimum is the classical theorem of Rogers and Simpson. In the original formulation using the density *missed*, the least missed density is one minus the greatest covered density, and conversely. [Original question as quoted by Cambie, section 1](https://arxiv.org/html/2508.18270v2#S1) · [Simpson, Lemma 2.3](https://doi.org/10.1016/0012-365x%2886%2990079-8)

## Statement

For $a=(a_1,\ldots,a_r)\in\mathbb Z^r$, write
```math
E(a)=\{x\in\mathbb Z:\ x\equiv a_i\pmod{n_i}\text{ for some }i\},
\qquad
d(a)=\lim_{N\to\infty}\frac{|E(a)\cap\{0,\ldots,N-1\}|}{N}.
```
Put $L=\mathrm{lcm}(n_1,\ldots,n_r)$ and $`X=\{0,\ldots,L-1\}`$. There are $T=\prod_i n_i$ residue tuples when each $a_i$ is reduced modulo $n_i$. Coordinates are labelled, so two choices at repeated moduli remain separate coordinates. Put $B=T+1$. For $S\subseteq X$ define
```math
e_i(S)=|\{x\bmod n_i:x\in S\}|,\qquad
A(S)=\prod_{i=1}^{r}\bigl(n_i-e_i(S)\bigr),\qquad
W=\sum_{S\subseteq X}(1-B)^{|S|}B^{L-|S|}A(S).
```

**Theorem.** Every $d(a)$ exists. The integer $W$ is positive, and both of the following values are attained.
```math
\max_a d(a)=\frac{\lfloor\log_B W\rfloor}{L},
\qquad
\min_a d(a)=\frac{|\{x\in X:n_i\mid x\text{ for some }i\}|}{L}.
```
Every common choice $a_i=t$ attains the minimum, for every integer $t$. For $0\le k\le L$, the digit of $W$ in position $k$ in base $B$ is the number of reduced tuples with $d(a)=k/L$. The units digit is in position zero. For an empty family, the conventions are $L=T=1$ and an empty product equals one.

## One period gives the natural density

Every $n_i$ divides $L$, so membership in $E(a)$ depends only on $x\bmod L$. Write $C(a)=|E(a)\cap X|$. For $N\ge1$ write $N=qL+s$, with $0\le s<L$. The $q$ full periods contribute exactly $qC(a)$ points. The final $s$ positions contribute some $R$ with $0\le R\le s$. Thus
```math
\left|\frac{|E(a)\cap\{0,\ldots,N-1\}|}{N}-\frac{C(a)}{L}\right|
 =\frac{|R-sC(a)/L|}{N}\le\frac{s}{N}<\frac{L}{N}.
```
Here $R$ and $sC(a)/L$ both lie in $[0,s]$. This proves $d(a)=C(a)/L$. Reducing any integer $a_i$ modulo $n_i$ preserves $E(a)$, so the finite space of $T$ reduced tuples realizes every density in the question.

## Maximum and counts at each density

Fix $S\subseteq X$. The class selected at coordinate $i$ misses every point in $S$ precisely when its residue avoids the $e_i(S)$ values represented there. This gives $n_i-e_i(S)$ choices. Residues at different coordinates can be chosen independently, even when two moduli have a common divisor. Hence $A(S)$ counts exactly the tuples for which **all** of $S$ is missed.

For each reduced tuple $a$, let $U(a)=X\setminus E(a)$ and $u=|U(a)|$, so $C(a)=L-u$. Replace $A(S)$ in the definition of $W$ by the count of tuples such that $S\subseteq U(a)$. Both sums are finite, so we may first fix $a$ and sum over its subsets of missed points. Its contribution is
```math
\begin{aligned}
\sum_{S\subseteq U(a)}(1-B)^{|S|}B^{L-|S|}
 &= B^{L-u}\sum_{j=0}^{u}\binom{u}{j}(1-B)^j B^{u-j} \\[2pt]
 &= B^{L-u}\bigl((1-B)+B\bigr)^u
  = B^{C(a)}.
\end{aligned}
```
The first equality groups subsets according to their cardinality. It also applies when $u=0$, in which case only the empty subset contributes.

Let $h_k$ count the tuples covering exactly $k$ positions. Summing the last identity over all $a$ yields
```math
W=\sum_a B^{C(a)}=\sum_{k=0}^L h_k B^k,
\qquad
\sum_{k=0}^L h_k=T=B-1.
```
There is at least one tuple, so $W>0$. Each $h_k$ lies between $0$ and $B-1$, so these coefficients are exactly the digits of $W$ in base $B$. In particular, $h_k=\lfloor W/B^k\rfloor\bmod B$, and an interior zero digit means that density is unattainable.

Let $m$ be the largest $k$ with $h_k>0$. A tuple attaining $m$ contributes $B^m$ to $W$, and each of the $T$ tuples contributes at most $B^m$. Consequently
```math
B^m\le W\le T B^m=(B-1)B^m\lt B^{m+1}.
```
Thus $\lfloor\log_B W\rfloor=m$, and the maximum density is $m/L$. This extraction can use integer comparisons throughout. Direct evaluation of the displayed formula for $W$ has $2^L$ subset terms. When the least common multiple is large it can cost more than enumerating all $T$ choices. The same calculation gives the exact count at every coverage level.

## Minimum and the common residue

We prove the inequality for **any** common period $M\ge1$. This lets us apply it to subfamilies during the proof. For a finite list $d_1,\ldots,d_j$ of divisors of $M$ and integer residues $b_i$, let $F_M(d,b)$ be the number of points in $\mathbb Z/M\mathbb Z$ covered by the classes $x\equiv b_i\pmod{d_i}$. We will prove $F_M(d,0)\le F_M(d,b)$ for every such list. Empty lists cover zero points. For $M=1$ the assertion follows since each available modulus is one.

**Prime-power period.** Suppose $M=p^e$ and the list is nonempty. Choose a smallest modulus $d_{\ast}$. The divisors of $p^e$ are ordered by divisibility, so $d_{\ast}$ divides every $d_i$. The union of the zero classes is exactly the class of multiples of $d_{\ast}$ and has $M/d_{\ast}$ elements. For arbitrary residues, the single selected class modulo $d_{\ast}$ also has $M/d_{\ast}$ elements. Its inclusion in the union proves the inequality.

**Product of coprime periods.** Write $M=uv$ with $u,v>1$ and $\gcd(u,v)=1$. Assume the inequality has been proved for all families of divisors of $u$ and of $v$. For every $i$ put $d_i'=\gcd(d_i,u)$ and $d_i''=\gcd(d_i,v)$. Each prime power in $d_i$ belongs in full to exactly one of $u,v$, since $d_i\mid uv$ and $u,v$ are coprime. Therefore $d_i=d_i'd_i''$ and $\gcd(d_i',d_i'')=1$.

Under the Chinese remainder bijection $\mathbb Z/M\mathbb Z\longrightarrow\mathbb Z/u\mathbb Z\times\mathbb Z/v\mathbb Z$, the class indexed by $i$ is the rectangle $P_i(b_i)\times Q_i(b_i)$, where
```math
P_i(t)=\{x\in\mathbb Z/u\mathbb Z:x\equiv t\pmod{d_i'}\},
\qquad
Q_i(t)=\{y\in\mathbb Z/v\mathbb Z:y\equiv t\pmod{d_i''}\}.
```
Indeed, congruence modulo $d_i$ is equivalent to those two congruences together. We compare the cardinalities of three unions.
```math
\begin{aligned}
H   &=\bigcup_i P_i(b_i)\times Q_i(b_i),\\[2pt]
H_1 &=\bigcup_i P_i(0)\times Q_i(b_i),\\[2pt]
H_0 &=\bigcup_i P_i(0)\times Q_i(0).
\end{aligned}
```

Fix a row $y\in\mathbb Z/v\mathbb Z$. The same indices $`I_y=\{i:y\in Q_i(b_i)\}`$ occur in that row of $H$ and $H_1$. Their row sections are respectively $\bigcup_{i\in I_y}P_i(b_i)$ and $\bigcup_{i\in I_y}P_i(0)$. The induction hypothesis for period $u$, applied to precisely this subfamily, bounds the size of the second section by that of the first. Summing over $y$ gives $|H_1|\le |H|$.

Now fix a column $x\in\mathbb Z/u\mathbb Z$. The indices occurring in that column of both $H_1$ and $H_0$ are $`J_x=\{i:x\in P_i(0)\}`$. The induction hypothesis for period $v$ gives
```math
\left|\bigcup_{i\in J_x}Q_i(0)\right|
 \le \left|\bigcup_{i\in J_x}Q_i(b_i)\right|.
```
Summing over $x$ yields $|H_0|\le |H_1|$. The Chinese remainder bijection identifies $|H_0|$ with $F_M(d,0)$ and $|H|$ with $F_M(d,b)$. This proves the desired inequality for $uv$. Any integer with at least two distinct prime factors splits into two smaller coprime factors by taking one full prime-power factor and its cofactor. Induction therefore covers every positive $M$.

Take $M=L$ and $d_i=n_i$. The all-zero tuple attains the lower bound. Translation by any integer $t$ is a bijection on $\mathbb Z/L\mathbb Z$ and sends its union to the union for the common choice $a_i=t$. This proves the minimum formula and the assertion about every common shift. Together with the maximum calculation and the density limit, this completes the theorem.

The minimum also has an arithmetic expression involving only least common multiples of subfamilies. For nonempty $`J\subseteq\{1,\ldots,r\}`$, the intersection of the zero classes indexed by $J$ has $L/\mathrm{lcm}_{i\in J}n_i$ elements in one period. Inclusion–exclusion followed by division by $L$ gives
```math
\min_a d(a)=
\sum_{\varnothing\ne J\subseteq\{1,\ldots,r\}}
 \frac{(-1)^{|J|+1}}{\mathrm{lcm}_{i\in J} n_i}.
```
For the empty list, the minimum and maximum are both zero and the single empty tuple gives $W=1$. If any modulus is one, every tuple covers all $L$ positions, and the counting identity gives $W=T B^L$.

## A worked example

Take the labelled moduli $(2,3,4,6)$. There are $144$ tuples and $L=12$. Fix the residues at $2$ and $3$. Their classes cover $6+4-2=8$ points. The four missed points have the opposite parity and occupy two residue classes modulo $6$, each with two representatives.

Of the four choices at modulus $4$, two have the parity already covered and add nothing. For either choice, the class modulo $6$ adds two points in two of its six choices and zero in the other four. Each of the other two choices at modulus $4$ meets the missed parity. Its three representatives run through all residues modulo $3$, so it fills one missed point in each of the two available classes modulo $6$. In this case the class modulo $6$ adds one point in two choices and zero in four. For each fixed pair of initial residues this gives $8$ completions covering $8$ points, $12$ covering $10$, and $4$ covering $11$.

There are six initial pairs, hence $W=48B^8+72B^{10}+24B^{11}$ with $B=145$. The minimum is $8/12=2/3$ and the maximum is $11/12$. The all-zero tuple attains the former. The tuple $(0,0,1,1)$ in the stated order attains the latter, missing only $11\bmod 12$.

## Formal correspondence and related work

The checked endpoint for integer representatives is `ResidueCoverage.jsp000237`. The table locates its principal steps and the companion digit theorem in the proof repository.

| Mathematical step | Lean declaration |
| --- | --- |
| Limit of initial-segment densities | [`natural_density`](Density.lean#L61) |
| Count tuples missing a set and interchange the two sums | [`count_avoiding`](Coverage.lean#L26), [`weighted_count`](Coverage.lean#L43) |
| Evaluate the signed sum and attain its top exponent | [`coverageCode_eq`](Coverage.lean#L66), [`maximum_attained`](Main.lean#L52) |
| Recover the number of tuples at each level | [`coverage_histogram`](Histogram.lean#L49) |
| Minimize over a period and handle common translates | [`zero_minimum`](Minimum.lean#L140), [`shared_shift`](Minimum.lean#L171) |
| Both extrema for arbitrary integer choices | [`jsp000237`](Prize.lean#L55) |

Ferudun gives a compatibility-graph formula for the maximum and counts the realizations of each graph. Those counts can also be grouped by coverage level. Onishi previously formalized the attained maximum and its natural-density limit in Lean. Schroeder studies maximum density and its computational complexity. The formula proved here counts by subsets of the period and recovers the entire distribution from one integer. [Ferudun, paper and method](https://eulersolve.org/papers/ep-278/) · [Onishi, pinned main theorem](https://github.com/yoshiyoyoyo44/erdos278/blob/66ff46ad30c302a0fcc19a2fb22d58a87eebf2cb/Erdos278/Main.lean) · [Schroeder, paper and companion](https://michaelschroeder.ai/research/Erdos278/companion)
