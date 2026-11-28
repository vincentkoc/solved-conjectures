import Erdos722QuartetDeletion
import Erdos722QuartetMaster
import Erdos722QuartetSeeds

/-!
# Hanani's four-point block spectrum

Inflate a master pairwise balanced design by a factor of three and adjoin one
point. This gives every positive admissible order, hence the exact `r=2,k=4`
instance of the eventual statement in Erdős 722.
-/

namespace Erdos722.Quartet
open Finset Filter

private theorem seed {s : ℕ} (hs : Allowed s) : Has (· = 4) (3*s+1) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact Seeds.thirteen
  · exact Seeds.sixteen
  · exact Seeds.twenty_five
  · exact Seeds.twenty_eight
  · exact Seeds.thirty_seven

private theorem inflate {V : Type*} [Fintype V] (C : Cover V (AllPairs _) Allowed) :
    Has (· = 4) (3*Fintype.card V+1) :=
  inflate_uniform (by decide) C (fun _ => seed)

/-- The complete positive admissible residue classes for four-point blocks. -/
theorem hanani {n : ℕ} (hn : n%12=1 ∨ n%12=4) :
    ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 4 := by
  let r := (n-1)/3
  have h : QuartetOrders.admissible r := by dsimp [r,QuartetOrders.admissible]; omega
  have weaken {m : ℕ} (hm : Has (· = 4) m) : Has Allowed m :=
    hm.mono (by rintro k rfl; exact Or.inl rfl)
  let M := (master (weaken Seeds.thirteen) (weaken Seeds.twenty_eight) r h).some
  have hc := inflate M
  have hn' : 3*r+1 = n := by dsimp [r]; omega
  rw [Fintype.card_fin,hn'] at hc
  exact hc.some.design

private theorem residues_of_divisibility {n : ℕ} (hn : 1 ≤ n)
    (H : ∀ i < 2, (4-i).choose (2-i) ∣ (n-i).choose (2-i)) : n%12=1 ∨ n%12=4 := by
  have h0 : 6 ∣ n.choose 2 := by simpa [show Nat.choose 4 2=6 by decide] using H 0 (by decide)
  have h1 : 3 ∣ n-1 := by simpa using H 1 (by decide)
  rw [Nat.choose_two_right] at h0
  have h2 := n.even_mul_pred_self.two_dvd
  have hm : n*(n-1)%12=0 := by omega
  rw [Nat.mul_mod] at hm
  rcases (show n%12=1 ∨ n%12=4 ∨ n%12=7 ∨ n%12=10 by omega) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rw [h,show (n-1)%12=6 by omega] at hm
    contradiction
  · rw [h,show (n-1)%12=9 by omega] at hm
    contradiction

/-- The pinned Erdős 722 divisibility hypotheses suffice at every positive order
for `(r,k)=(2,4)`. -/
theorem four_of_divisibility {n : ℕ} (hn : 1 ≤ n)
    (H : ∀ i < 2, (4-i).choose (2-i) ∣ (n-i).choose (2-i)) :
    ∃ D : Finset (Finset (Fin n)), D.IsBlockDesign 2 4 :=
  hanani (residues_of_divisibility hn H)

/-- Count the `r`-subsets containing a fixed `i`-subset, first in the whole
vertex set and then inside each block that contains the fixed subset. -/
theorem design_divisibility {n r k : ℕ} {H : Finset (Finset (Fin n))}
    (hH : H.IsBlockDesign r k) {i : ℕ} (hin : i ≤ n) (hir : i ≤ r) :
    (k-i).choose (r-i) ∣ (n-i).choose (r-i) := by
  classical
  obtain ⟨A,_,hA⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using hin)
  let T := H.filter (A ⊆ ·)
  let P := fun B : Finset (Fin n) => (B.powersetCard r).filter (A ⊆ ·)
  have parts : T.biUnion P = P univ := by
    ext S
    simp only [T,P,mem_biUnion,mem_filter,mem_powersetCard,subset_univ,true_and]
    constructor
    · rintro ⟨_,_,⟨_,hs⟩,ha⟩
      exact ⟨hs,ha⟩
    · rintro ⟨hs,ha⟩
      obtain ⟨B,⟨hb,hsb⟩,_⟩ := hH.2 S hs
      exact ⟨B,⟨hb,ha.trans hsb⟩,⟨hsb,hs⟩,ha⟩
  have disjoint : (T : Set (Finset (Fin n))).PairwiseDisjoint P := by
    intro B hB D hD hne
    apply Finset.disjoint_left.mpr
    intro S hsb hsd
    have hb := mem_powersetCard.mp (mem_filter.mp hsb).1
    have hd := mem_powersetCard.mp (mem_filter.mp hsd).1
    exact hne ((hH.2 S hb.2).unique ⟨(mem_filter.mp hB).1,hb.1⟩ ⟨(mem_filter.mp hD).1,hd.1⟩)
  have counts (B : Finset (Fin n)) (ha : A ⊆ B) :
      (P B).card = (B.card-i).choose (r-i) := by
    simpa [P,hA] using card_filter_powersetCard_subset A B r ha (hA ▸ hir)
  have total := congrArg Finset.card parts
  rw [card_biUnion disjoint,counts univ (subset_univ A),card_univ,Fintype.card_fin] at total
  refine ⟨T.card,?_⟩
  rw [← total]
  calc
    _ = ∑ _B ∈ T, (k-i).choose (r-i) := by
      apply sum_congr rfl
      intro B hb
      rw [counts B (mem_filter.mp hb).2,hH.1 B (mem_filter.mp hb).1]
    _ = _ := by simp [Nat.mul_comm]

/-- Existence at a positive order is equivalent to Hanani's two residue classes. -/
theorem hanani_iff {n : ℕ} (hn : 1 ≤ n) :
    (∃ D : Finset (Finset (Fin n)), D.IsBlockDesign 2 4) ↔ n%12=1 ∨ n%12=4 :=
  ⟨fun ⟨_,hD⟩ => residues_of_divisibility hn (fun i hi => design_divisibility hD (by omega) hi.le),
    hanani⟩

theorem eventually_four : ∀ᶠ n : ℕ in atTop,
    (∀ i < 2, (4-i).choose (2-i) ∣ (n-i).choose (2-i)) →
      ∃ D : Finset (Finset (Fin n)), D.IsBlockDesign 2 4 :=
  eventually_atTop.mpr ⟨1,fun _ hn => four_of_divisibility hn⟩

#print axioms hanani
#print axioms design_divisibility
#print axioms hanani_iff
#print axioms four_of_divisibility
#print axioms eventually_four

end Erdos722.Quartet
