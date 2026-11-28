import Erdos722TwistedClassCount

/-! # Explicit ranks, point groups and class counts for rigid transversal sums -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Finset
noncomputable section
attribute [local instance] cubeOrder cubeDec

theorem path_word_frames (d : ℕ) (hd : 2≤d) :
    Subsingleton (baseFrames (cubeRule d) (edgeMatching 0 (rigidWord d hd))) := by
  rw [rigidWord_matching]
  exact ⟨fun g h => (path_frame_trivial _ _ g).trans (path_frame_trivial _ _ h).symm⟩

/-- For each fixed dimension this counts distinct unlabelled designs of the
explicit path-matching family. Every offset has the stated rank and full group. -/
theorem rigid_offset_family (d : ℕ) (hd : 2≤d) :
    (twistClasses d (rigidWord d hd)).card=4^(blockNumber (2^d)+d+1-2^d) ∧
    ∀ u : CubeOffsets d, let D := twistedFamily d (rigidWord d hd) u
      D.IsBlockDesign 3 4 ∧ (binaryIncidence D).rank+(d+1)=4*2^d ∧
      Nat.card (automorphisms D)=4*(2^d)^2 ∧
      ∀ a b : automorphisms D, a*b=b*a ∧ a*a=1 := by
  let hw := rigidWord_top d hd
  let rigid := path_word_frames d hd
  refine ⟨twist_class_count hd hw rigid,fun u => ?_⟩
  obtain ⟨design,rank⟩ := twist_rank hw u
  let e := twistAut hd hw rigid u
  refine ⟨design,rank,?_,?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    change Nat.card (shifts (cubeRule d))=_
    rw [shifts_card,cube_checks_card,pow_succ]
    ring
  · intro a b
    obtain ⟨x,rfl⟩ := e.surjective a
    obtain ⟨y,rfl⟩ := e.surjective b
    refine ⟨by rw [← map_mul,← map_mul,mul_comm x y],?_⟩
    have xx : x*x=1 := by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext (funext fun i => fibre_double (x.toAdd.val i))
    rw [← map_mul,xx,map_one]

theorem rigid_sixteen_one : (twistClasses 2 (rigidWord 2 (by decide))).card=1 := by
  rw [(rigid_offset_family 2 (by decide)).1]
  decide

theorem rigid_thirtytwo_million : (twistClasses 3 (rigidWord 3 (by decide))).card=1048576 := by
  rw [(rigid_offset_family 3 (by decide)).1]
  decide

#print axioms path_word_frames
#print axioms rigid_offset_family
#print axioms rigid_sixteen_one
#print axioms rigid_thirtytwo_million
end
end Erdos722.FourPoint
