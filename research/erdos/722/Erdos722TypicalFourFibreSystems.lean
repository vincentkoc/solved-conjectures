import Erdos722ExceptionalMatchingWords

/-! # Typical matching words give actual quadruple systems with minimum automorphism group -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Finset Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

theorem carries_star {I J : Type*} {M : Matching I} {N : Matching J} {b : I ≃ J} {s : Colour}
    (frame : Frame M N b s) {o : I} (h : Normalized M o) : Normalized N (b o) := by
  intro j
  have e := frame o (b.symm j)
  rw [h,mul_one,b.apply_symm_apply] at e
  apply mul_right_cancel (b:=s)
  simpa only [one_mul] using e.symm

theorem typical_top {d : ℕ} {w : EdgeWord d} (hw : Typical d w) : w∈noDirectionWords (CubeEdge d) := by
  apply (mem_noDirectionWords w).mpr
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨s,ne,frame⟩ := fixed_direction_frame 0 w i ((mem_survivors w i).mp hi)
  have mem : (1 : Perm (Cube d))∈rootedBases d := (mem_rootedBases ..).mpr ⟨rfl,fun _ _ _ => rfl⟩
  exact ne (hw.2 1 mem s frame).2

theorem typical_frames {d : ℕ} {w : EdgeWord d} (hw : Typical d w) :
    Subsingleton (baseFrames (cubeRule d) (edgeMatching 0 w)) := by
  have id (g : baseFrames (cubeRule d) (edgeMatching 0 w)) : g=1 := by
    obtain ⟨base,frame⟩ := g.prop
    have root := hw.1 _ (carries_star frame (edge_normalized 0 w))
    have mem := (mem_rootedBases d g.val.1).mpr ⟨root,base⟩
    obtain ⟨hb,hs⟩ := hw.2 _ mem _ frame
    exact Subtype.ext (Prod.ext hb hs)
  exact ⟨fun a b => (id a).trans (id b).symm⟩

def typicalAut {d : ℕ} (hd : 2≤d) {w : EdgeWord d} (hw : Typical d w) :
    Multiplicative (shifts (cubeRule d)) ≃* automorphisms (splitFamily d w) := by
  letI := typical_frames hw
  apply MulEquiv.trans _ (labelledFourAut d hd (typical_top hw))
  apply MulEquiv.ofBijective SemidirectProduct.inl
  refine ⟨SemidirectProduct.inl_injective,fun g => ⟨g.left,?_⟩⟩
  exact SemidirectProduct.ext rfl (Subsingleton.elim _ _)

/-- The point group, binary incidence rank, and pinned block-design predicate
of every typical word. -/
theorem typical_design {d : ℕ} (hd : 2≤d) {w : EdgeWord d} (hw : Typical d w) :
    (splitFamily d w).IsBlockDesign 3 4 ∧
    (binaryIncidence (splitFamily d w)).rank+(d+1)=4*2^d ∧
    Nat.card (automorphisms (splitFamily d w))=4*(2^d)^2 := by
  refine ⟨splitFamily_design ..,(rank_tests ..).1.mpr (typical_top hw),?_⟩
  rw [← Nat.card_congr (typicalAut hd hw).toEquiv]
  change Nat.card (shifts (cubeRule d))=_
  rw [shifts_card,cube_checks_card,pow_succ]
  ring

#print axioms carries_star
#print axioms typical_top
#print axioms typical_frames
#print axioms typicalAut
#print axioms typical_design
end
end Erdos722.FourPoint
