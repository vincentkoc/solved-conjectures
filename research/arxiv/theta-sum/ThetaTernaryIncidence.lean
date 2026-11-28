import ThetaAlmostEqualPrimeTriples
import Mathlib.Algebra.Order.Chebyshev

/-! A second-moment bound for extracting vertex-disjoint prime triples. -/
namespace Arxiv.«2501.03234».ThetaTernaryIncidence
open Finset ThetaTernaryPacking ThetaTernaryDeletion
abbrev Triple := ℕ × ℕ × ℕ

def separated (D : Finset Triple) : Prop :=
  ∀ t∈D,∀ u∈D,t≠u → Disjoint (vertices t) (vertices u)

def incident (T : Finset Triple) (v : ℕ) := T.filter (fun t => v∈vertices t)
def moment (A : Finset ℕ) (n : ℕ) : ℕ := ∑ v∈A, (incident (triples A A A n) v).card^2

private theorem cover (T : Finset Triple) : ∃ D ⊆ T, separated D ∧
    ∀ t∈T,∃ v∈D.biUnion vertices,v∈vertices t := by
  classical
  let candidates := T.powerset.filter separated
  have h₀ : ∅∈candidates := by simp [candidates,separated]
  obtain ⟨D,hD,hmax⟩ := exists_max_image candidates card ⟨∅,h₀⟩
  obtain ⟨hsub,hsep⟩ := mem_filter.mp hD
  have hDT := mem_powerset.mp hsub
  refine ⟨D,hDT,hsep,?_⟩
  intro t ht
  by_contra! hmiss
  have hd : ∀ u∈D,Disjoint (vertices t) (vertices u) := by
    intro u hu
    exact disjoint_left.mpr (fun v hv hu' => hmiss v (mem_biUnion.mpr ⟨u,hu,hu'⟩) hv)
  have hnot : t∉D := by
    intro hh
    have h₁ : t.1∈vertices t := by simp [vertices]
    exact disjoint_left.mp (hd t hh) h₁ h₁
  have hi : insert t D∈candidates := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset ht hDT),?_⟩
    intro x hx y hy hne
    rcases mem_insert.mp hx with hxt|hxd
    · rcases mem_insert.mp hy with hyt|hyd
      · exact False.elim (hne (hxt.trans hyt.symm))
      · rw [hxt];exact hd y hyd
    · rcases mem_insert.mp hy with hyt|hyd
      · rw [hyt];exact (hd x hxd).symm
      · exact hsep x hxd y hyd hne
  have h := hmax _ hi
  simp [hnot] at h

/-- For an arbitrary subfamily T of the ordinary representations, the
denominator uses only ordinary incidences, even when T has theta restrictions. -/
theorem extraction (A : Finset ℕ) (n : ℕ) (T : Finset Triple)
    (hT : T ⊆ triples A A A n) :
    ∃ D ⊆ T,separated D ∧ T.card^2≤3*D.card*moment A n := by
  obtain ⟨D,hD,hsep,hcover⟩ := cover T
  let U := D.biUnion vertices
  let F := incident (triples A A A n)
  have hU : U⊆A := by
    intro v hv
    obtain ⟨t,ht,hv⟩ := mem_biUnion.mp hv
    obtain ⟨h₁,h₂,h₃,_⟩ := mem.mp (hT (hD ht))
    simp only [vertices,mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl;exact h₁;exact h₂;exact h₃
  have hsize : U.card≤D.card*3 := by
    apply card_biUnion_le_card_mul
    intro t _
    have h := card_insert_le t.1 ({t.2.1,t.2.2} : Finset ℕ)
    have hh := card_insert_le t.2.1 ({t.2.2} : Finset ℕ)
    simp only [card_singleton] at hh
    unfold vertices
    omega
  have hsub : T ⊆ U.biUnion F := by
    intro t ht
    obtain ⟨v,hv,htv⟩ := hcover t ht
    exact mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨hT ht,htv⟩⟩
  have hsum : T.card≤∑ v∈U,(F v).card := (card_le_card hsub).trans card_biUnion_le
  have hmoment : ∑ v∈U, (F v).card^2 ≤ moment A n :=
    sum_le_sum_of_subset_of_nonneg hU (by intros; positivity)
  refine ⟨D,hD,hsep,?_⟩
  calc T.card^2 ≤ (∑ v∈U,(F v).card)^2 := Nat.pow_le_pow_left hsum _
       _ ≤ U.card * ∑ v∈U,(F v).card^2 := sq_sum_le_card_mul_sum_sq
       _ ≤ (D.card*3)*moment A n := Nat.mul_le_mul hsize hmoment
       _ = _ := by ring

#print axioms extraction
end Arxiv.«2501.03234».ThetaTernaryIncidence
