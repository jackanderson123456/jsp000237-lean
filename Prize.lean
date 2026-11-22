import Main
import Histogram
import Mathlib.Data.Int.ModEq

namespace ResidueCoverage
open Finset Filter
open scoped Classical Topology BigOperators

variable {r : ℕ}

/-- Count the integers from 0 through N−1 which satisfy at least one of the given congruences. -/
noncomputable def integerCount (N : ℕ) (d : Fin r → ℕ) (a : Fin r → ℤ) : ℕ :=
  ∑ x ∈ range N, if ∃ i, (x : ℤ) ≡ a i [ZMOD (d i : ℤ)] then 1 else 0

def integerDensities (d : Fin r → ℕ) : Set ℝ :=
  {z | ∃ a : Fin r → ℤ, Tendsto (fun N : ℕ => (integerCount N d a : ℝ) / N) atTop (𝓝 z)}

def representative (m : ℕ) (z : ℤ) : ℕ := (z % (m : ℤ)).toNat

private theorem repr_congr (m : ℕ) (hm : 0 < m) (z : ℤ) :
    (representative m z : ℤ) ≡ z [ZMOD (m : ℤ)] := by
  unfold representative
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))]
  exact Int.mod_modEq _ _

theorem integerCount_eq (N : ℕ) (d : Fin r → ℕ) (a : Fin r → ℤ)
    (b : Fin r → ℕ) (hb : ∀ i, (b i : ℤ) ≡ a i [ZMOD (d i : ℤ)]) :
    integerCount N d a = initialCount N univ d b := by
  unfold integerCount initialCount
  apply sum_congr rfl
  intro x _
  unfold hitBit hits
  congr 1
  apply propext
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, mem_univ _, Int.natCast_modEq_iff.mp (hi.trans (hb i).symm)⟩
  · rintro ⟨i, _, hi⟩
    exact ⟨i, (Int.natCast_modEq_iff.mpr hi).trans (hb i)⟩

theorem all_representatives (d : Fin r → ℕ) (h : ∀ i, 0 < d i) :
    integerDensities d = attainableDensities d := by
  ext z
  constructor
  · rintro ⟨a, ha⟩
    let b i := representative (d i) (a i)
    refine ⟨b, ?_⟩
    simpa only [fun N => integerCount_eq N d a b (fun i => repr_congr _ (h i) _)] using ha
  · rintro ⟨b, hb⟩
    refine ⟨fun i => (b i : ℤ), ?_⟩
    simpa only [fun N => integerCount_eq N d (fun i => (b i : ℤ)) b (fun _ => Int.ModEq.rfl)] using hb

/-- Both attained extrema, and the ordinary density of every system having a single
common integer residue. No distinctness or nonemptiness hypothesis is needed. -/
theorem jsp000237 (d : Fin r → ℕ) (h : ∀ i, 0 < d i) :
    let L := commonPeriod d
    let low := (periodCount L univ d (fun _ => 0) : ℝ) / L
    let high := (extremalNumerator d h : ℝ) / L
    IsGreatest (integerDensities d) high ∧ IsLeast (integerDensities d) low ∧
      ∀ t : ℤ, Tendsto (fun N : ℕ => (integerCount N d (fun _ => t) : ℝ) / N) atTop (𝓝 low) := by
  dsimp only
  rw [all_representatives d h]
  obtain ⟨hmax, hmin⟩ := extremal_densities d h
  refine ⟨hmax, hmin, fun t => ?_⟩
  let L := commonPeriod d
  have hL := period_positive d h
  let b := representative L t
  have hb (i : Fin r) : (b : ℤ) ≡ t [ZMOD (d i : ℤ)] :=
    (repr_congr L hL t).of_dvd (by exact_mod_cast divisor_of_period d i)
  have hd : ∀ i ∈ (univ : Finset (Fin r)), d i ∣ L := fun i _ => divisor_of_period d i
  have hlim := natural_density L hL univ d (fun _ => b) hd
  rw [shared_shift _ hL univ d b hd] at hlim
  simpa only [fun N => integerCount_eq N d (fun _ => t) (fun _ => b) hb] using hlim

#print axioms jsp000237
end ResidueCoverage

