import Minimum
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace ResidueCoverage
open Finset Filter
open scoped BigOperators Topology Classical

variable {I : Type*}

/-- Actual number of covered integers in the initial segment [0,N). -/
noncomputable def initialCount (N : ℕ) (s : Finset I) (d a : I → ℕ) : ℕ :=
  ∑ x ∈ range N, hitBit s d a x

theorem period_eq_initial (L : ℕ) (s : Finset I) (d a : I → ℕ) :
    periodCount L s d a = initialCount L s d a :=
  Fin.sum_univ_eq_sum_range _ _

private theorem initial_le (N : ℕ) (s : Finset I) (d a : I → ℕ) :
    initialCount N s d a ≤ N := by
  unfold initialCount
  calc
    _ ≤ ∑ _ ∈ range N, 1 := by
      apply sum_le_sum
      intro x _
      unfold hitBit
      split <;> omega
    _ = _ := by simp

private theorem shift_hit (L q x : ℕ) (s : Finset I) (d a : I → ℕ)
    (hd : ∀ i ∈ s, d i ∣ L) : hitBit s d a (q * L + x) = hitBit s d a x := by
  unfold hitBit
  congr 1
  apply propext
  have shift (i : I) (hi : i ∈ s) : q * L + x ≡ x [MOD d i] := by
    have h := (dvd_mul_of_dvd_right (hd i hi) q).modEq_zero_nat.add_right x
    simpa using h
  constructor
  · rintro ⟨i, hi, he⟩; exact ⟨i, hi, (shift i hi).symm.trans he⟩
  · rintro ⟨i, hi, he⟩; exact ⟨i, hi, (shift i hi).trans he⟩

private theorem blocks (L q r : ℕ) (s : Finset I) (d a : I → ℕ)
    (hd : ∀ i ∈ s, d i ∣ L) :
    initialCount (q * L + r) s d a = q * initialCount L s d a + initialCount r s d a := by
  have addBlock (k t : ℕ) : initialCount (k * L + t) s d a =
        initialCount (k * L) s d a + initialCount t s d a := by
    unfold initialCount
    rw [sum_range_add]
    simp only [shift_hit L k _ s d a hd]
  have full (k : ℕ) : initialCount (k * L) s d a = k * initialCount L s d a := by
    induction k with
    | zero => simp [initialCount]
    | succ k ih => rw [Nat.succ_mul, addBlock, ih, Nat.succ_mul]
  rw [addBlock, full]

/-- The finite-period fraction agrees with ordinary natural density. -/
theorem natural_density (L : ℕ) (hL : 0 < L) (s : Finset I) (d a : I → ℕ)
    (hd : ∀ i ∈ s, d i ∣ L) :
    Tendsto (fun N : ℕ => (initialCount N s d a : ℝ) / (N : ℝ))
      atTop (𝓝 ((periodCount L s d a : ℝ) / (L : ℝ))) := by
  rw [period_eq_initial, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt ((L : ℝ) / ε)
  refine ⟨n, fun N hN => ?_⟩
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have heN : (L : ℝ) < (N : ℝ) * ε := (div_lt_iff₀ hε).mp
    (hn.trans_le (by exact_mod_cast hN))
  have hNr : (0 : ℝ) < N := by
    by_contra! hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hε.le]
  let q := N / L
  let r := N % L
  have decomp : q * L + r = N := by
    simpa [q, r, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div N L
  have hr : r < L := Nat.mod_lt _ hL
  have hcount := blocks L q r s d a hd
  rw [decomp] at hcount
  let K := initialCount L s d a
  let R := initialCount r s d a
  have hK : (K : ℝ) ≤ L := by exact_mod_cast initial_le L s d a
  have hR : (R : ℝ) ≤ r := by exact_mod_cast initial_le r s d a
  have hrL : (r : ℝ) < L := by exact_mod_cast hr
  have hcountR : (initialCount N s d a : ℝ) = (q : ℝ)*K+R := by exact_mod_cast hcount
  have hdecomp : (q : ℝ) * L + r = N := by exact_mod_cast decomp
  rw [Real.dist_eq, div_sub_div _ _ hNr.ne' hLr.ne', abs_div, abs_of_pos (mul_pos hNr hLr)]
  apply (div_lt_iff₀ (mul_pos hNr hLr)).mpr
  change |(initialCount N s d a : ℝ)*L - (N : ℝ)*K| < _
  rw [hcountR]
  have hid : ((q : ℝ) * K + R) * L - (N : ℝ) * K = R * (L : ℝ) - r*K := by
    rw [← hdecomp]; ring
  rw [hid, abs_lt]
  have hrK : (r : ℝ)*K < (L : ℝ)*L := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _)) (mul_lt_mul_of_pos_right hrL hLr)
  have hRL : (R : ℝ)*L < (L : ℝ)*L := mul_lt_mul_of_pos_right (hR.trans_lt hrL) hLr
  have hεNL := mul_lt_mul_of_pos_right heN hLr
  constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg R : (0:ℝ) ≤ R) hLr.le,
    mul_nonneg (Nat.cast_nonneg r : (0:ℝ) ≤ r) (Nat.cast_nonneg K)]

end ResidueCoverage

