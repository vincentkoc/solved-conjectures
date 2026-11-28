import Erdos722RigidCubeWord
import Erdos722SplitFourAutomorphismGroup
import Mathlib.GroupTheory.Coset.Card

/-! # Sharp minimum automorphism group for the four-point matching family -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Finset Equiv
noncomputable section
attribute [local instance] cubeOrder cubeDec

private theorem cube_size (d : ℕ) (hd : 2≤d) : 3≤Fintype.card (Cube d) := by
  have bound : 2^2≤2^d := Nat.pow_le_pow_right (by decide) hd
  simpa [Cube] using (show 3≤2^d by omega)

private theorem cube_shifts (d : ℕ) : Nat.card (shifts (cubeRule d))=4*(2^d)^2 := by
  rw [shifts_card,cube_checks_card,pow_succ]; ring

private theorem word_hyp (d : ℕ) {w : EdgeWord d} (hw : w∈noDirectionWords (CubeEdge d)) :
    FibreHypotheses (cubeRule d) (edgeMatching 0 w) :=
  ⟨cube_separates d,⟨0,edge_normalized 0 w⟩,(noFix_edge_iff 0 w).mpr hw⟩

/-- Full automorphisms of the labelled host system at the top rank of the family. -/
def labelledFourAut (d : ℕ) (hd : 2≤d) {w : EdgeWord d} (hw : w∈noDirectionWords (CubeEdge d)) :
    FrameProduct (cubeRule d) (edgeMatching 0 w) ≃* automorphisms (splitFamily d w) :=
  (fullFourAut _ _ (word_hyp d hw) (cube_size d hd)).trans (automorphismRelabel (fourLabels d) _)

/-- The same translations act for every split word, even when other
automorphisms fail to preserve the chosen four-point fibres. -/
theorem four_divisibility (d : ℕ) (w : EdgeWord d) :
    4*(2^d)^2 ∣ Nat.card (automorphisms (splitFamily d w)) := by
  let Q := cubeRule d
  let M := edgeMatching 0 w
  let f : Multiplicative (shifts Q) →* automorphisms (fourRule Q M).blocks :=
    (evaluateFrame Q M).comp SemidirectProduct.inl
  have h : Function.Injective f := (evaluateFrame_injective Q M 0).comp SemidirectProduct.inl_injective
  let e := automorphismRelabel (fourLabels d) (fourRule Q M).blocks
  have bound := Subgroup.card_dvd_of_injective (e.toMonoidHom.comp f) (e.injective.comp h)
  rw [← cube_shifts]
  exact bound

private theorem rigid_frames (d : ℕ) (hd : 2≤d) :
    Subsingleton (baseFrames (cubeRule d) (edgeMatching 0 (rigidWord d hd))) := by
  rw [rigidWord_matching]
  exact ⟨fun g h => (path_frame_trivial _ _ g).trans (path_frame_trivial _ _ h).symm⟩

/-- Every automorphism of this explicit word is an affine fibre translation. -/
def rigidAut (d : ℕ) (hd : 2≤d) :
    Multiplicative (shifts (cubeRule d)) ≃* automorphisms (splitFamily d (rigidWord d hd)) := by
  letI := rigid_frames d hd
  apply MulEquiv.trans _ (labelledFourAut d hd (rigidWord_top d hd))
  apply MulEquiv.ofBijective SemidirectProduct.inl
  refine ⟨SemidirectProduct.inl_injective,fun g => ⟨g.left,?_⟩⟩
  exact SemidirectProduct.ext rfl (Subsingleton.elim _ _)

theorem rigid_group_law (d : ℕ) (hd : 2≤d)
    (a b : automorphisms (splitFamily d (rigidWord d hd))) : a*b=b*a ∧ a*a=1 := by
  obtain ⟨x,rfl⟩ := (rigidAut d hd).surjective a
  obtain ⟨y,rfl⟩ := (rigidAut d hd).surjective b
  constructor
  · rw [← map_mul,← map_mul,mul_comm x y]
  · have xx : x*x=1 := by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext (funext fun i => fibre_double (x.toAdd.val i))
    rw [← map_mul,xx,map_one]

/-- The canonical block predicate, the binary matrix rank, and the order
of the entire point automorphism group for the explicit infinite family. -/
theorem rigid_family (d : ℕ) (hd : 2≤d) :
    (splitFamily d (rigidWord d hd)).IsBlockDesign 3 4 ∧
    (binaryIncidence (splitFamily d (rigidWord d hd))).rank+(d+1)=4*2^d ∧
    Nat.card (automorphisms (splitFamily d (rigidWord d hd)))=4*(2^d)^2 :=
  ⟨splitFamily_design ..,(rank_tests ..).1.mpr (rigidWord_top d hd),
    (Nat.card_congr (rigidAut d hd).toEquiv).symm.trans (cube_shifts d)⟩

private theorem mem_split {d : ℕ} (D : Finset (Finset (Fin (4*2^d)))) :
    D∈splitSystems d ↔ ∃ w : EdgeWord d, splitFamily d w=D := by
  unfold splitSystems
  simp only [Finset.mem_image,Finset.mem_univ,true_and]

/-- The minimum is over all systems of the split family, including all three ranks. -/
theorem least_four_aut (d : ℕ) (hd : 2≤d) :
    IsLeast {k : ℕ | ∃ D∈splitSystems d, Nat.card (automorphisms D)=k} (4*(2^d)^2) := by
  constructor
  · let v := rigidWord d hd
    exact ⟨splitFamily d v,(mem_split _).mpr ⟨v,rfl⟩,(rigid_family d hd).2.2⟩
  · rintro k ⟨D,hD,rfl⟩
    obtain ⟨w,rfl⟩ := (mem_split D).mp hD
    exact Nat.le_of_dvd (Nat.card_pos (α:=automorphisms (splitFamily d w))) (four_divisibility d w)

#print axioms labelledFourAut
#print axioms four_divisibility
#print axioms rigidAut
#print axioms rigid_group_law
#print axioms rigid_family
#print axioms least_four_aut
end
end Erdos722.FourPoint
