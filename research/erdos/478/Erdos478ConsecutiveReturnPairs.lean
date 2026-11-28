import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Consecutive pairs in an ordered finite fibre -/

namespace Erdos478.ReturnConcentration
open Finset
open scoped Classical
noncomputable section

/-- Increasing enumeration, extended constantly beyond the last point. -/
def point (s : Finset ℕ) (i : ℕ) : ℕ :=
  if h : 0 < s.card then
    s.orderEmbOfFin rfl ⟨min i (s.card-1), lt_of_le_of_lt (min_le_right ..) (by omega)⟩
  else 0

theorem point_mem {s : Finset ℕ} (hs : s.Nonempty) (i : ℕ) : point s i ∈ s := by
  simp only [point,dif_pos (card_pos.mpr hs)]
  apply orderEmbOfFin_mem

private theorem monotone_point (s : Finset ℕ) : Monotone (point s) := by
  intro i j le
  by_cases h : 0 < s.card
  · simp only [point,dif_pos h]
    apply (s.orderEmbOfFin rfl).monotone
    exact min_le_min_right _ le
  · simp [point,h]

private theorem strict_point {s : Finset ℕ} {i j : ℕ} (hij : i < j) (hj : j < s.card) :
    point s i < point s j := by
  have h : 0 < s.card := by omega
  simp only [point,dif_pos h]
  apply (s.orderEmbOfFin rfl).strictMono
  change min i (s.card-1) < min j (s.card-1)
  omega

/-- An edge joins each occurrence to its next occurrence in the same fibre. -/
def links (s : Finset ℕ) := (range (s.card-1)).image fun i => (point s i, point s (i+1))

def width (s : Finset ℕ) := point s (s.card-1) - point s 0

private theorem injective_pairs (s : Finset ℕ) :
    Set.InjOn (fun i => (point s i,point s (i+1))) (↑(range (s.card-1)) : Set ℕ) := by
  intro i hi j hj eq
  have h := congrArg Prod.fst eq
  change point s i = point s j at h
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  rcases lt_trichotomy i j with a | a | a
  · exact False.elim ((strict_point a (by omega : j<s.card)).ne h)
  · exact a
  · exact False.elim ((strict_point a (by omega : i<s.card)).ne h.symm)

theorem links_card (s : Finset ℕ) : (links s).card = s.card-1 :=
  (card_image_of_injOn (injective_pairs s)).trans (card_range _)

theorem links_sum (s : Finset ℕ) : ∑ e ∈ links s, (e.2-e.1) = width s := by
  rw [links,sum_image (injective_pairs s)]
  exact sum_range_tsub (monotone_point s) _

theorem links_mem {s : Finset ℕ} {e : ℕ × ℕ} (he : e ∈ links s) :
    e.1 ∈ s ∧ e.2 ∈ s ∧ e.1 < e.2 := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp he
  have b := mem_range.mp hi
  have hs := card_pos.mp (show 0<s.card by omega)
  exact ⟨point_mem hs _,point_mem hs _,strict_point (Nat.lt_succ_self _) (by omega)⟩

theorem width_le {s : Finset ℕ} {a b : ℕ} (hs : s ⊆ Icc a b) : width s ≤ b-a := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp [width]
  · have lo := (mem_Icc.mp (hs (point_mem hn 0))).1
    have hi := (mem_Icc.mp (hs (point_mem hn (s.card-1)))).2
    unfold width
    omega

#print axioms point
#print axioms point_mem
#print axioms links
#print axioms width
#print axioms links_card
#print axioms links_sum
#print axioms links_mem
#print axioms width_le

end
end Erdos478.ReturnConcentration
