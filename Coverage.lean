import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-! Counting residue choices by the number of covered points in a period. -/
namespace ResidueCoverage

open Finset
open scoped BigOperators

variable {X I : Type*} [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
variable {V : I → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- A point is missed when every coordinate avoids its selected value. -/
def missed (R : ∀ i, X → V i) (a : ∀ i, V i) : Finset X :=
  univ.filter fun x => ∀ i, R i x ≠ a i

/-- Number of choices that avoid every point of a prescribed set. -/
def avoidCount (R : ∀ i, X → V i) (S : Finset X) : ℕ :=
  ∏ i, (Fintype.card (V i) - (S.image (R i)).card)

theorem count_avoiding (R : ∀ i, X → V i) (S : Finset X) :
    (univ.filter fun a => S ⊆ missed R a).card = avoidCount R S := by
  classical
  have h : (univ.filter fun a => S ⊆ missed R a) =
      Fintype.piFinset (fun i => (S.image (R i))ᶜ) := by
    ext a
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, mem_compl,
      mem_image, missed, subset_iff]
    constructor
    · intro ha i ⟨x, hx, he⟩
      exact ha hx i he
    · intro ha x hx i he
      exact ha i ⟨x, hx, he⟩
  rw [h, Fintype.card_piFinset]
  simp [avoidCount, Finset.card_compl]

/-- Finite double counting, with arbitrary integer weights on the test subsets. -/
theorem weighted_count (R : ∀ i, X → V i) (w : Finset X → ℤ) :
    (∑ S : Finset X, w S * (avoidCount R S : ℤ)) =
      ∑ a : (∀ i, V i), ∑ S ∈ (missed R a).powerset, w S := by
  classical
  calc
    _ = ∑ S : Finset X, ∑ a : (∀ i, V i), if S ⊆ missed R a then w S else 0 := by
      apply sum_congr rfl
      intro S _
      rw [← sum_filter, sum_const, nsmul_eq_mul, ← count_avoiding, mul_comm]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      rw [← sum_filter]
      congr 1
      ext S
      simp

/-- An integer computed from the moduli and their projections only. -/
def coverageCode (R : ∀ i, X → V i) (B : ℕ) : ℤ :=
  ∑ S : Finset X, ((1 - (B : ℤ)) ^ S.card * (B : ℤ) ^ (Fintype.card X - S.card))
    * (avoidCount R S : ℤ)

theorem coverageCode_eq (R : ∀ i, X → V i) (B : ℕ) :
    coverageCode R B = ∑ a : (∀ i, V i), (B : ℤ) ^ (Fintype.card X - (missed R a).card) := by
  classical
  unfold coverageCode
  rw [weighted_count]
  apply sum_congr rfl
  intro a _
  let U := missed R a
  have hU : U.card ≤ Fintype.card X := card_le_univ _
  change (∑ S ∈ U.powerset, (1 - (B : ℤ)) ^ S.card * (B : ℤ) ^ (Fintype.card X - S.card)) = _
  calc
    _ = (∑ S ∈ U.powerset, (1 - (B : ℤ)) ^ S.card * (B : ℤ) ^ (U.card - S.card)) *
        (B : ℤ) ^ (Fintype.card X - U.card) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro S hS
      have hs : S.card ≤ U.card := card_le_card (mem_powerset.mp hS)
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    _ = _ := by rw [sum_pow_mul_eq_add_pow]; simp [U]

/-- Integer logarithms recover an attained maximum when the base exceeds the population. -/
theorem log_sum_pow_max {A : Type*} [Fintype A] [Nonempty A] (f : A → ℕ)
    {B : ℕ} (hB : Fintype.card A < B) :
    (∃ a, f a = Nat.log B (∑ x, B ^ f x)) ∧
      ∀ a, f a ≤ Nat.log B (∑ x, B ^ f x) := by
  classical
  let values := univ.image f
  have hv : values.Nonempty := univ_nonempty.image f
  let m := values.max' hv
  obtain ⟨a, _, ha⟩ := mem_image.mp (values.max'_mem hv)
  have hall (x : A) : f x ≤ m := values.le_max' _ (mem_image_of_mem _ (mem_univ x))
  have bpos : 0 < B := lt_trans Fintype.card_pos hB
  have low : B ^ m ≤ ∑ x, B ^ f x := by
    change f a = m at ha
    rw [← ha]
    exact single_le_sum (fun x _ => Nat.zero_le (B ^ f x)) (mem_univ a)
  have upper : (∑ x, B ^ f x) < B ^ (m+1) := calc
    _ ≤ ∑ _ : A, B ^ m := sum_le_sum fun x _ => Nat.pow_le_pow_right bpos (hall x)
    _ = Fintype.card A * B ^ m := by simp
    _ < B * B ^ m := Nat.mul_lt_mul_of_pos_right hB (pow_pos bpos _)
    _ = _ := (pow_succ' B m).symm
  rw [Nat.log_eq_of_pow_le_of_lt_pow low upper]
  exact ⟨⟨a, ha⟩, hall⟩

/-- The returned count is attained, and every residue choice covers at most this many
points. The right-hand side has no search over choices. -/
theorem coverage_max (R : ∀ i, X → V i) [Nonempty (∀ i, V i)]
    (B : ℕ) (hB : Fintype.card (∀ i, V i) < B) :
    let M := Nat.log B (coverageCode R B).toNat
    (∃ a, Fintype.card X - (missed R a).card = M) ∧
      ∀ a, Fintype.card X - (missed R a).card ≤ M := by
  classical
  have h : coverageCode R B = ((∑ a : (∀ i, V i),
      B ^ (Fintype.card X - (missed R a).card) : ℕ) : ℤ) := by
    rw [coverageCode_eq]
    push_cast
    rfl
  simp only [h, Int.toNat_natCast]
  exact log_sum_pow_max _ hB

end ResidueCoverage


