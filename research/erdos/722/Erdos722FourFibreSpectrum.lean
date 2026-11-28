import Erdos722FourFibreLabelled

/-! # The exact labelled rank distribution of the normalized split family -/

namespace Erdos722.FourPoint
open QuadSwitch Finset Equiv
noncomputable section
open scoped Classical
local instance : Fintype Colour := fintypePerm

def splitSystems (d : ℕ) := (univ : Finset (EdgeWord d)).image (splitFamily d)

/-- The stratum with binary nullity `d+1+k`, restricted to this family. -/
def splitStratum (d k : ℕ) :=
  (splitSystems d).filter fun D => (binaryIncidence D).rank+(d+1)+k=4*2^d

theorem splitSystems_card (d : ℕ) : (splitSystems d).card=6^numberEdges d := by
  rw [splitSystems,card_image_of_injective _ (splitFamily_injective d),card_univ,Fintype.card_fun,
    cubeEdge_card,show Fintype.card Colour=6 by decide +kernel]

theorem rank_tests (d : ℕ) (w : EdgeWord d) :
    let r := (binaryIncidence (splitFamily d w)).rank+(d+1)
    (r=4*2^d ↔ w∈noDirectionWords (CubeEdge d)) ∧
    (r+1=4*2^d ↔ w∈oneDirectionWords (CubeEdge d)) ∧
    (r+2=4*2^d ↔ w=(fun _ => 1)) := by
  dsimp only
  rw [mem_noDirectionWords,mem_oneDirectionWords,survivors_card]
  have arithmetic (r n : ℕ) (p q : Prop) [Decidable p] [Decidable q]
      (hr : r+(if p then 2 else if q then 1 else 0)=n) :
      (r=n ↔ (if p then 3 else if q then 1 else 0)=0) ∧
      (r+1=n ↔ (if p then 3 else if q then 1 else 0)=1) ∧ (r+2=n ↔ p) := by
    by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq] at hr ⊢ <;> omega
  exact arithmetic _ _ _ _ (splitFamily_rank d w)

private theorem countStratum (d k : ℕ) (S : Finset (EdgeWord d))
    (h : ∀ w, (binaryIncidence (splitFamily d w)).rank+(d+1)+k=4*2^d ↔ w∈S) :
    (splitStratum d k).card=S.card := by
  rw [splitStratum,splitSystems,filter_image,card_image_of_injective _ (splitFamily_injective d)]
  congr 1
  ext w
  simp [h]

theorem splitStratum_top (d : ℕ) :
    (splitStratum d 0).card=6^numberEdges d-(1+3*(2^numberEdges d-1)) := by
  rw [countStratum d 0 (noDirectionWords _) (fun w => by simpa using (rank_tests d w).1),
    noDirectionWords_card,cubeEdge_card]

theorem splitStratum_middle (d : ℕ) : (splitStratum d 1).card=3*(2^numberEdges d-1) := by
  rw [countStratum d 1 (oneDirectionWords _) (fun w => (rank_tests d w).2.1),
    oneDirectionWords_card,cubeEdge_card]

theorem splitStratum_minimum (d : ℕ) : (splitStratum d 2).card=1 := by
  rw [countStratum d 2 {fun _ => 1} (fun w => by simpa using (rank_tests d w).2.2),card_singleton]

theorem splitStratum_exhaustive (d : ℕ) {D} (h : D∈splitSystems d) :
    D∈splitStratum d 0 ∨ D∈splitStratum d 1 ∨ D∈splitStratum d 2 := by
  obtain ⟨w,_,rfl⟩ := mem_image.mp h
  simp only [splitStratum,mem_filter,h,true_and,add_zero]
  have hr := splitFamily_rank d w
  split_ifs at hr <;> omega

/-- The first nontrivial split family. These are actual labelled block sets. -/
theorem order_sixteen :
    (splitSystems 2).card=216 ∧ (splitStratum 2 0).card=194 ∧
    (splitStratum 2 1).card=21 ∧ (splitStratum 2 2).card=1 := by
  rw [splitSystems_card,splitStratum_top,splitStratum_middle,splitStratum_minimum]
  decide +kernel

end

#print axioms splitSystems
#print axioms splitStratum
#print axioms splitSystems_card
#print axioms rank_tests
#print axioms splitStratum_top
#print axioms splitStratum_middle
#print axioms splitStratum_minimum
#print axioms splitStratum_exhaustive
#print axioms order_sixteen
end Erdos722.FourPoint
