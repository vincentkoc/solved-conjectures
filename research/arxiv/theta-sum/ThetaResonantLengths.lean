import ThetaResonantCount
import ThetaReciprocalResonance

/-! Distinct initial lengths forced by resonant dyadic levels. -/
namespace Arxiv.«2501.03234».ThetaResonantLengths
open Finset Real Filter ThetaResonanceScales ThetaResonantBlock ThetaResonantPrefix
open ThetaResonantCount ThetaReciprocalResonance
noncomputable section

def lengths (p : ℕ) [Fact p.Prime] (δ : ℝ) : Finset ℕ := by
  classical
  exact (range p).filter fun N => window p N δ ∧ ∃ a : ZMod p, a≠0 ∧ signal N a

def separated (E : Finset ℕ) : Prop := ∀ n m : ℕ, n ∈ E → m ∈ E → n < m → 2*n ≤ m

theorem select_lengths (F G : Finset ℕ)
    (h : ∀ i∈F, ∃ N∈G, 2^i ≤ N ∧ N ≤ 4*2^i) :
    ∃ E : Finset ℕ, E ⊆ G ∧ separated E ∧ F.card ≤ 3*E.card := by
  classical
  choose g hg hlo hhi using h
  let f (i : ℕ) := if hi : i∈F then g i hi else 0
  let fiber (r : ℕ) := F.filter (fun i => i%3=r)
  obtain ⟨r,hr,hmax⟩ := exists_max_image (range 3) (fun r => (fiber r).card)
    (show (range 3).Nonempty from ⟨0,by decide⟩)
  have hcost : F.card ≤ 3*(fiber r).card := calc
    _ = ∑ j∈range 3,(fiber j).card := card_eq_sum_card_fiberwise (f:=fun i : ℕ => i%3)
      (fun i _ => mem_range.mpr (Nat.mod_lt _ (by decide)))
    _ ≤ ∑ _j∈range 3,(fiber r).card := sum_le_sum (fun j hj => hmax j hj)
    _ = _ := by simp
  have hb (i : ℕ) (hi : i∈fiber r) : f i∈G ∧ 2^i ≤ f i ∧ f i≤4*2^i := by
    have hm := (mem_filter.mp hi).1
    simpa [f,hm] using (show g i hm∈G ∧ 2^i ≤ g i hm ∧ g i hm ≤ 4*2^i from ⟨hg i hm,hlo i hm,hhi i hm⟩)
  have hs (i j : ℕ) (hi : i∈fiber r) (hj : j∈fiber r) (hij : i<j) : 2*f i ≤ f j := by
    have hai := (mem_filter.mp hi).2
    have haj := (mem_filter.mp hj).2
    have hd : i+3≤j := by omega
    have hh := Nat.pow_le_pow_right (n:=2) (by decide) hd
    rw [pow_add] at hh
    norm_num at hh
    have := (hb i hi).2.2
    have := (hb j hj).2.1
    omega
  have hpos (i : ℕ) (hi : i∈fiber r) : 0 < f i := (by positivity : 0<(2:ℕ)^i).trans_le (hb i hi).2.1
  refine ⟨(fiber r).image f,?_,?_,?_⟩
  · intro n hn
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
    exact (hb i hi).1
  · intro n m hn hm hnm
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hm
    rcases lt_trichotomy i j with h|rfl|h
    · exact hs i j hi hj h
    · exact (lt_irrefl _ hnm).elim
    · have := hs j i hj hi h
      omega
  · rw [card_image_iff.mpr]
    · exact hcost
    · intro i hi j hj he
      rcases lt_trichotomy i j with h|h|h
      · have := hs i j hi hj h
        have := hpos i hi
        omega
      · exact h
      · have := hs j i hj hi h
        have := hpos j hj
        omega

theorem counted {δ : ℝ} (hδ : 0<δ) : ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
    letI : Fact p.Prime := ⟨hp⟩
    ∃ E : Finset ℕ, E ⊆ lengths p δ ∧ separated E ∧
      (levels p (lowerLevel p) (depth p)).card ≤ 3*E.card := by
  classical
  filter_upwards [scales,upper_scale hδ] with p H hupper
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨_,hs₀,_,_,_,_,hdepth,hroot⟩ := H
  apply select_lengths
  intro i hi
  obtain ⟨hi,hblock⟩ := mem_filter.mp hi
  obtain ⟨hs,ht⟩ := mem_Ico.mp hi
  obtain ⟨hJ,N,hlo,hhi,hn,a,ha,he⟩ := resonant_prefix (Nat.odd_iff.mp ho) (by omega) hblock
  obtain ⟨hlen,hv,hi⟩ := length_lower hs hs₀ hroot hlo
  exact ⟨N,mem_filter.mpr ⟨mem_range.mpr hn,⟨hlen,hupper i N ht hdepth hJ hhi,hn⟩,
    a,ha,strength hhi hi hv he⟩,hlo,hhi⟩

#print axioms select_lengths
#print axioms counted
end
end Arxiv.«2501.03234».ThetaResonantLengths
