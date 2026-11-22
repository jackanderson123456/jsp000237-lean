"""Compare the period-subset formula with exhaustive residue choices on small examples."""
from collections import Counter
from itertools import combinations, product
from math import lcm, prod


def subset_formula(moduli):
    period = lcm(*moduli)
    base = 1 + prod(moduli)
    coefficient = [(1 - base) ** k * base ** (period - k) for k in range(period + 1)]
    code = 0
    for mask in range(1 << period):
        points = [x for x in range(period) if mask >> x & 1]
        avoid = prod(n - len({x % n for x in points}) for n in moduli)
        code += coefficient[len(points)] * avoid

    digits = Counter()
    for k in range(period + 1):
        code, count = divmod(code, base)
        if count:
            digits[k] = count
    assert code == 0
    return digits


def enumerate_residues(moduli):
    period = lcm(*moduli)
    digits = Counter()
    for residues in product(*(range(n) for n in moduli)):
        covered = sum(any(x % n == a for n, a in zip(moduli, residues))
                      for x in range(period))
        digits[covered] += 1
    return digits


if __name__ == "__main__":
    cases = {m for size in range(5) for m in combinations((1, 2, 3, 4, 6, 12), size)}
    cases.update([(4, 4), (2, 2, 3), (3, 3, 3), (5,), (2, 5)])
    for moduli in sorted(cases):
        histogram = subset_formula(moduli)
        assert histogram == enumerate_residues(moduli), moduli
        period = lcm(*moduli)
        zero_count = sum(any(x % n == 0 for n in moduli) for x in range(period))
        assert zero_count == min(histogram), moduli
        assert sum(histogram.values()) == prod(moduli), moduli
    print(f"{len(cases)} complete histograms agree.")
    sample = (2, 3, 4, 6)
    print(f"moduli={sample}, period={lcm(*sample)}, histogram={dict(sorted(subset_formula(sample).items()))}")

