import Coverage
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.ModEq

namespace ResidueCoverage
open Finset
open scoped BigOperators Classical

variable {I : Type*}

def hits (s : Finset I) (d a : I → ℕ) (x : ℕ) : Prop :=
  ∃ i ∈ s, x ≡ a i [MOD d i]

noncomputable def hitBit (s : Finset I) (d a : I → ℕ) (x : ℕ) : ℕ := by
  classical exact if hits s d a x then 1 else 0

noncomputable def periodCount (L : ℕ) (s : Finset I) (d a : I → ℕ) : ℕ :=
  ∑ x : Fin L, hitBit s d a x.val

private theorem count_as_card (L : ℕ) (s : Finset I) (d a : I → ℕ) :
    periodCount L s d a =
      (univ.filter (fun x : Fin L => by classical exact hits s d a x.val)).card := by
  classical
  simp [periodCount, hitBit]

/-- In a prime-power period the divisors are linearly ordered by divisibility.
The largest zero class can be translated into the union for any other choice. -/
private theorem minimum_prime_power (p e : ℕ) (hp : Nat.Prime p) (s : Finset I)
    (d a : I → ℕ) (hd : ∀ i ∈ s, d i ∣ p ^ e) :
    periodCount (p ^ e) s d (fun _ => 0) ≤ periodCount (p ^ e) s d a := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨j, hj, hmin⟩ := exists_min_image s d hs
    have hL : 0 < p ^ e := pow_pos hp.pos _
    have hdiv (i : I) (hi : i ∈ s) : d j ∣ d i := by
      obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp (hd j hj)
      obtain ⟨l, _, hl⟩ := (Nat.dvd_prime_pow hp).mp (hd i hi)
      rcases le_total k l with h | h
      · rw [hk, hl]; exact pow_dvd_pow _ h
      · have rev : d i ∣ d j := by rw [hk, hl]; exact pow_dvd_pow _ h
        have hpos : 0 < d j := Nat.pos_of_dvd_of_pos (hd j hj) hL
        rw [le_antisymm (hmin i hi) (Nat.le_of_dvd hpos rev)]
    let f : Fin (p ^ e) → Fin (p ^ e) := fun x => ⟨(x.val + a j) % (p ^ e), Nat.mod_lt _ hL⟩
    rw [count_as_card, count_as_card]
    apply card_le_card_of_injOn f
    · intro x hx
      obtain ⟨i, hi, he⟩ := (mem_filter.mp hx).2
      apply mem_filter.mpr
      refine ⟨mem_univ _, j, hj, ?_⟩
      have hzero : x.val ≡ 0 [MOD d j] := he.of_dvd (hdiv i hi)
      have hShift : x.val + a j ≡ a j [MOD d j] := by simpa using hzero.add_right (a j)
      exact ((Nat.mod_modEq _ _).of_dvd (hd j hj)).trans hShift
    · intro x _ y _ h
      have hmod : x.val + a j ≡ y.val + a j [MOD p ^ e] := congrArg Fin.val h
      have he := Nat.ModEq.add_right_cancel' (a j) hmod
      apply Fin.ext
      simpa [Nat.ModEq, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] using he
  · have hempty : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp [hempty, periodCount, hitBit, hits]

private def crtPair (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hc : Nat.Coprime u v) :
    Fin (u * v) ≃ Fin u × Fin v where
  toFun x := (⟨x.val % u, Nat.mod_lt _ hu⟩, ⟨x.val % v, Nat.mod_lt _ hv⟩)
  invFun t := ⟨(Nat.chineseRemainder hc t.1.val t.2.val).val,
    Nat.chineseRemainder_lt_mul hc _ _ hu.ne' hv.ne'⟩
  left_inv x := by
    apply Fin.ext
    let z := Nat.chineseRemainder hc (x.val % u) (x.val % v)
    exact ((Nat.modEq_and_modEq_iff_modEq_mul hc).mp
      ⟨z.property.1.trans (Nat.mod_modEq _ _), z.property.2.trans (Nat.mod_modEq _ _)⟩
      ).eq_of_lt_of_lt (Nat.chineseRemainder_lt_mul hc _ _ hu.ne' hv.ne') x.isLt
  right_inv t := by
    let z := Nat.chineseRemainder hc t.1.val t.2.val
    have h₁ : z.val % u = t.1.val := Eq.trans z.property.1 (Nat.mod_eq_of_lt t.1.isLt)
    have h₂ : z.val % v = t.2.val := Eq.trans z.property.2 (Nat.mod_eq_of_lt t.2.isLt)
    exact Prod.ext (Fin.ext h₁) (Fin.ext h₂)

private noncomputable def rectangleBit (s : Finset I) (d₁ d₂ a₁ a₂ : I → ℕ)
    (x y : ℕ) : ℕ :=
  if ∃ i ∈ s, (x ≡ a₁ i [MOD d₁ i]) ∧ (y ≡ a₂ i [MOD d₂ i]) then 1 else 0

private theorem count_split (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hc : Nat.Coprime u v)
    (s : Finset I) (d a : I → ℕ) (hd : ∀ i ∈ s, d i ∣ u * v) :
    periodCount (u*v) s d a =
      ∑ x : Fin u, ∑ y : Fin v,
        rectangleBit s (fun i => (d i).gcd u) (fun i => (d i).gcd v) a a x.val y.val := by
  classical
  let term (z : Fin u × Fin v) := rectangleBit s (fun i => (d i).gcd u)
      (fun i => (d i).gcd v) a a z.1.val z.2.val
  change (∑ t : Fin (u*v), hitBit s d a t.val) = _
  calc
    _ = ∑ t : Fin (u*v), term (crtPair u v hu hv hc t) := by
      apply sum_congr rfl
      intro t _
      unfold term rectangleBit hitBit
      congr 1
      apply propext
      constructor
      · rintro ⟨i, hi, h⟩
        refine ⟨i, hi, ?_, ?_⟩
        · exact ((Nat.mod_modEq t.val u).of_dvd (Nat.gcd_dvd_right _ _)).trans
            (h.of_dvd (Nat.gcd_dvd_left _ _))
        · exact ((Nat.mod_modEq t.val v).of_dvd (Nat.gcd_dvd_right _ _)).trans
            (h.of_dvd (Nat.gcd_dvd_left _ _))
      · rintro ⟨i, hi, h₁, h₂⟩
        refine ⟨i, hi, ?_⟩
        have hprod := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hc).mpr (hd i hi)
        rw [← hprod]
        apply (Nat.modEq_and_modEq_iff_modEq_mul (hc.gcd_both (d i) (d i))).mp
        exact ⟨((Nat.mod_modEq t.val u).of_dvd (Nat.gcd_dvd_right _ _)).symm.trans h₁,
          ((Nat.mod_modEq t.val v).of_dvd (Nat.gcd_dvd_right _ _)).symm.trans h₂⟩
    _ = ∑ z, term z := (crtPair u v hu hv hc).sum_comp term
    _ = _ := Fintype.sum_prod_type _

private theorem rectangle_left (s : Finset I) (d₁ d₂ a₁ a₂ : I → ℕ) (x y : ℕ) :
    rectangleBit s d₁ d₂ a₁ a₂ x y =
      hitBit (s.filter fun i => y ≡ a₂ i [MOD d₂ i]) d₁ a₁ x := by
  classical
  unfold rectangleBit hitBit hits
  simp only [mem_filter]
  congr 1
  apply propext
  constructor
  · rintro ⟨i, hi, hx, hy⟩; exact ⟨i, ⟨hi, hy⟩, hx⟩
  · rintro ⟨i, ⟨hi, hy⟩, hx⟩; exact ⟨i, hi, hx, hy⟩

private theorem rectangle_right (s : Finset I) (d₁ d₂ a₁ a₂ : I → ℕ) (x y : ℕ) :
    rectangleBit s d₁ d₂ a₁ a₂ x y =
      hitBit (s.filter fun i => x ≡ a₁ i [MOD d₁ i]) d₂ a₂ y := by
  classical
  unfold rectangleBit hitBit hits
  simp only [mem_filter]
  congr 1
  apply propext
  constructor
  · rintro ⟨i, hi, hx, hy⟩; exact ⟨i, ⟨hi, hx⟩, hy⟩
  · rintro ⟨i, ⟨hi, hx⟩, hy⟩; exact ⟨i, hi, hx, hy⟩

/-- Rogers' minimum theorem for all finite families, in any common period. -/
theorem zero_minimum (L : ℕ) : ∀ (s : Finset I) (d a : I → ℕ),
    (∀ i ∈ s, d i ∣ L) → periodCount L s d (fun _ => 0) ≤ periodCount L s d a := by
  classical
  induction L using Nat.recOnPrimeCoprime with
  | h0 => intros; simp [periodCount]
  | hp p e hprime => exact minimum_prime_power p e hprime
  | h u v hu hv hc ihu ihv =>
    intro s d a hd
    let du (i : I) := (d i).gcd u
    let dv (i : I) := (d i).gcd v
    let z (_ : I) := 0
    rw [count_split u v (by omega) (by omega) hc _ _ _ hd,
        count_split u v (by omega) (by omega) hc _ _ _ hd]
    change (∑ x : Fin u, ∑ y : Fin v, rectangleBit s du dv z z x.val y.val) ≤
      ∑ x : Fin u, ∑ y : Fin v, rectangleBit s du dv a a x.val y.val
    calc
      _ ≤ ∑ x : Fin u, ∑ y : Fin v, rectangleBit s du dv z a x.val y.val := by
        apply sum_le_sum
        intro x _
        simp_rw [rectangle_right]
        apply ihv
        exact fun i _ => Nat.gcd_dvd_right _ _
      _ ≤ _ := by
        rw [sum_comm, sum_comm (s := (univ : Finset (Fin u)))]
        apply sum_le_sum
        intro y _
        simp_rw [rectangle_left]
        apply ihu
        exact fun i _ => Nat.gcd_dvd_right _ _

/-- Choosing the same integer shift in every congruence preserves the minimum. -/
theorem shared_shift (L : ℕ) (hL : 0 < L) (s : Finset I) (d : I → ℕ) (t : ℕ)
    (hd : ∀ i ∈ s, d i ∣ L) :
    periodCount L s d (fun _ => t) = periodCount L s d (fun _ => 0) := by
  classical
  let f (x : Fin L) : Fin L := ⟨(x.val + t) % L, Nat.mod_lt _ hL⟩
  have hf : Function.Injective f := by
    intro x y h
    have hm : x.val + t ≡ y.val + t [MOD L] := congrArg Fin.val h
    exact Fin.ext ((Nat.ModEq.add_right_cancel' t hm).eq_of_lt_of_lt x.isLt y.isLt)
  have comm (x : Fin L) : hitBit s d (fun _ => t) (f x).val = hitBit s d (fun _ => 0) x.val := by
    unfold hitBit
    congr 1
    apply propext
    have shift (i : I) (hi : i ∈ s) : (f x).val ≡ x.val + t [MOD d i] :=
      (Nat.mod_modEq _ _).of_dvd (hd i hi)
    constructor
    · rintro ⟨i, hi, he⟩
      refine ⟨i, hi, Nat.ModEq.add_right_cancel' t ?_⟩
      simpa using (shift i hi).symm.trans he
    · rintro ⟨i, hi, he⟩
      refine ⟨i, hi, (shift i hi).trans ?_⟩
      simpa using he.add_right t
  unfold periodCount
  calc
    _ = ∑ x : Fin L, hitBit s d (fun _ => t) (f x).val :=
      (hf.bijective_of_finite.sum_comp (fun x : Fin L => hitBit s d (fun _ => t) x.val)).symm
    _ = _ := sum_congr rfl fun x _ => comm x

end ResidueCoverage





