import Density
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

/-! # Extremal densities of unions of residue classes -/
namespace ResidueCoverage

open Finset Filter
open scoped Classical Topology BigOperators

variable {r : ℕ}

def commonPeriod (d : Fin r → ℕ) : ℕ := univ.lcm d

theorem period_positive (d : Fin r → ℕ) (h : ∀ i, 0 < d i) : 0 < commonPeriod d := by
  apply Nat.pos_of_ne_zero
  intro hz
  obtain ⟨i, _, hi⟩ := (Finset.lcm_eq_zero_iff.mp hz)
  exact (h i).ne' hi

theorem divisor_of_period (d : Fin r → ℕ) (i : Fin r) : d i ∣ commonPeriod d :=
  dvd_lcm (mem_univ i)

def residueMap (d : Fin r → ℕ) (h : ∀ i, 0 < d i) (i : Fin r) (x : Fin (commonPeriod d)) :
    Fin (d i) := ⟨x.val % d i, Nat.mod_lt _ (h i)⟩

/-- A modulus-only formula. The base is one greater than the number of residue choices. -/
def extremalNumerator (d : Fin r → ℕ) (h : ∀ i, 0 < d i) : ℕ :=
  let B := (∏ i, d i) + 1
  Nat.log B (coverageCode (residueMap d h) B).toNat

private theorem count_eq_complement (d : Fin r → ℕ) (h : ∀ i, 0 < d i)
    (a : ∀ i, Fin (d i)) :
    periodCount (commonPeriod d) univ d (fun i => (a i).val) =
      commonPeriod d - (missed (residueMap d h) a).card := by
  classical
  have he : univ.filter (fun x : Fin (commonPeriod d) =>
      hits univ d (fun i => (a i).val) x.val) = (missed (residueMap d h) a)ᶜ := by
    ext x
    simp only [mem_filter, mem_univ, true_and, hits, missed, mem_compl, not_forall,
      not_not, Nat.ModEq, Fin.ext_iff, residueMap, Nat.mod_eq_of_lt (a _).isLt]

  unfold periodCount hitBit
  simp [sum_boole, he, card_compl]

private theorem normalize_count (d a : Fin r → ℕ) :
    periodCount (commonPeriod d) univ d (fun i => a i % d i) =
      periodCount (commonPeriod d) univ d a := by
  unfold periodCount hitBit hits
  simp [Nat.ModEq]

theorem maximum_attained (d : Fin r → ℕ) (h : ∀ i, 0 < d i) :
    (∃ a : Fin r → ℕ, periodCount (commonPeriod d) univ d a = extremalNumerator d h) ∧
    ∀ a : Fin r → ℕ, periodCount (commonPeriod d) univ d a ≤ extremalNumerator d h := by
  letI : Nonempty (∀ i, Fin (d i)) := ⟨fun i => ⟨0, h i⟩⟩
  have hb : Fintype.card (∀ i, Fin (d i)) < (∏ i, d i) + 1 := by simp
  obtain ⟨⟨a, ha⟩, hall⟩ := coverage_max (residueMap d h) _ hb
  constructor
  · exact ⟨fun i => (a i).val, (count_eq_complement d h a).trans (by simpa using ha)⟩
  · intro b
    let c (i : Fin r) : Fin (d i) := ⟨b i % d i, Nat.mod_lt _ (h i)⟩
    rw [← normalize_count d b]
    exact (count_eq_complement d h c).le.trans (by simpa using hall c)

/-- The set consists of ordinary limiting densities over all choices of one
residue per modulus. Natural representatives cover every integer residue class. -/
def attainableDensities (d : Fin r → ℕ) : Set ℝ :=
  {v | ∃ a : Fin r → ℕ, Tendsto (fun N : ℕ => (initialCount N univ d a : ℝ) / N) atTop (𝓝 v)}

theorem extremal_densities (d : Fin r → ℕ) (h : ∀ i, 0 < d i) :
    IsGreatest (attainableDensities d) ((extremalNumerator d h : ℝ) / commonPeriod d) ∧
    IsLeast (attainableDensities d) ((periodCount (commonPeriod d) univ d (fun _ => 0) : ℝ) /
      commonPeriod d) := by
  have hL := period_positive d h
  have hr : 0 ≤ (commonPeriod d : ℝ) := Nat.cast_nonneg _
  have dvdL : ∀ i ∈ (univ : Finset (Fin r)), d i ∣ commonPeriod d := fun i _ => divisor_of_period d i
  have lim (a : Fin r → ℕ) := natural_density (commonPeriod d) hL univ d a dvdL
  obtain ⟨⟨a, ha⟩, hall⟩ := maximum_attained d h
  constructor
  · refine ⟨⟨a, ha ▸ lim a⟩, ?_⟩
    rintro _ ⟨b, hb⟩
    rw [tendsto_nhds_unique hb (lim b)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hall b) hr
  · refine ⟨⟨fun _ => 0, lim _⟩, ?_⟩
    rintro _ ⟨b, hb⟩
    rw [tendsto_nhds_unique hb (lim b)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast zero_minimum _ univ d b dvdL) hr

#print axioms extremal_densities

end ResidueCoverage


