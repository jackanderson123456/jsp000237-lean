import Coverage

namespace ResidueCoverage
open Finset
open scoped BigOperators Classical

/-- Every base digit, including interior zeros, counts the assignments at exactly
that exponent. This works for a composite radix as well as a prime one. -/
theorem digit_of_sum_powers {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℕ) (B k : ℕ) (hb : Fintype.card A < B) :
    ((∑ x, B ^ f x) / B ^ k) % B = (univ.filter fun x => f x = k).card := by
  classical
  let small := ∑ x : A, if f x < k then B ^ f x else 0
  let count := (univ.filter fun x : A => f x = k).card
  let high := ∑ x : A, if k < f x then B ^ (f x - (k+1)) else 0
  have hp : 0 < B := Fintype.card_pos.trans hb
  have hc : count < B := (card_le_univ _).trans_lt hb
  have hs : small < B ^ k := by
    cases k with
    | zero => simp [small]
    | succ t =>
      have h : small ≤ ∑ _ : A, B ^ t := by
        apply sum_le_sum
        intro x _
        split
        · exact Nat.pow_le_pow_right hp (by omega)
        · exact Nat.zero_le _
      calc
        _ ≤ _ := h
        _ = Fintype.card A * B ^ t := by simp
        _ < B * B ^ t := Nat.mul_lt_mul_of_pos_right hb (pow_pos hp _)
        _ = _ := (pow_succ' B t).symm
  have htotal : (∑ x, B ^ f x) = small + (count + high * B) * B ^ k := by
    have hc' : count = ∑ x : A, if f x = k then 1 else 0 := by simp [count]
    rw [hc', add_mul]
    unfold small high
    rw [sum_mul, sum_mul, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    rcases lt_trichotomy (f x) k with h | h | h
    · simp [h, h.ne, (not_lt_of_ge h.le)]
    · simp [h]
    · have he : f x - (k+1) + 1 + k = f x := by omega
      simp only [(not_lt_of_ge h.le), h.ne', if_false, h, if_true, zero_mul, zero_add]
      rw [← pow_succ, ← pow_add, he]
  rw [htotal, Nat.add_mul_div_right _ _ (pow_pos hp k), Nat.div_eq_of_lt hs, zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem coverage_histogram {X I : Type*} [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    {V : I → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [Nonempty (∀ i, V i)]
    (R : ∀ i, X → V i) (B k : ℕ) (hb : Fintype.card (∀ i, V i) < B) :
    ((coverageCode R B).toNat / B ^ k) % B =
      (univ.filter fun a => Fintype.card X - (missed R a).card = k).card := by
  have h : coverageCode R B = ((∑ a : (∀ i, V i),
      B ^ (Fintype.card X - (missed R a).card) : ℕ) : ℤ) := by
    rw [coverageCode_eq]
    push_cast
    rfl
  simp only [h, Int.toNat_natCast]
  exact digit_of_sum_powers _ B k hb

#print axioms coverage_histogram

end ResidueCoverage


