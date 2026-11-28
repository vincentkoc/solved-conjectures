import Erdos722RigidTwistTranslations
import Erdos722RankClassQuotient
import Erdos722SharpFourFibreAutomorphisms

/-! # Binary cube families with independent transversal sums -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Finset Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

abbrev CubeOffsets (d : ℕ) := BlockOffsets (cubeRule d)

def twistedFamily (d : ℕ) (w : EdgeWord d) (u : CubeOffsets d) :=
  labelledBlocks d (twistedRule (cubeRule d) (edgeMatching 0 w) u)

theorem twistedFamily_injective (d : ℕ) (w : EdgeWord d) : Function.Injective (twistedFamily d w) := by
  intro u v eq
  have blocks := (fourLabels d).finsetCongr.finsetCongr.injective eq
  apply offset_injective (cubeRule d)
  funext i j k
  have h := congrArg Prod.snd (completion_determined _ _ blocks (i,0) (j,0) (k,0))
  exact add_left_cancel (a:=fourth (edgeMatching 0 w) i j k 0 0 0) h

theorem cube_offsets_card (d : ℕ) : Nat.card (CubeOffsets d)=4^blockNumber (2^d) := by
  rw [Nat.card_eq_fintype_card]
  simp only [CubeOffsets,BlockOffsets,Fintype.card_fun,Fintype.card_coe,base_block_count (cubeRule d).isBlockDesign]
  simp [blockNumber,Fibre]

theorem twist_labelled_count (d : ℕ) (w : EdgeWord d) :
    (univ.image (twistedFamily d w)).card=4^blockNumber (2^d) := by
  rw [card_image_of_injective _ (twistedFamily_injective d w),card_univ,← Nat.card_eq_fintype_card,cube_offsets_card]

theorem twist_rank {d : ℕ} {w : EdgeWord d} (hw : w∈noDirectionWords (CubeEdge d)) (u : CubeOffsets d) :
    (twistedFamily d w u).IsBlockDesign 3 4 ∧
      (binaryIncidence (twistedFamily d w u)).rank+(d+1)=4*2^d :=
  arbitrary_filling_rank d hw _ (twisted_compatible ..)

private theorem wordHyp {d : ℕ} {w : EdgeWord d} (hw : w∈noDirectionWords (CubeEdge d)) :
    FibreHypotheses (cubeRule d) (edgeMatching 0 w) :=
  ⟨cube_separates d,⟨0,edge_normalized 0 w⟩,(noFix_edge_iff ..).mpr hw⟩

private theorem cubeSize {d : ℕ} (hd : 2≤d) : 3≤Fintype.card (Cube d) := by
  have bound : 2^2≤2^d := Nat.pow_le_pow_right (by decide) hd
  simpa [Cube] using (show 3≤2^d by omega)

theorem twist_class_iff {d : ℕ} (hd : 2≤d) {w : EdgeWord d} (hw : w∈noDirectionWords (CubeEdge d))
    (rigid : Subsingleton (baseFrames (cubeRule d) (edgeMatching 0 w))) (u v : CubeOffsets d) :
    classOf (twistedFamily d w u)=classOf (twistedFamily d w v) ↔
      ∃ t : Cube d → Fibre, v=u+blockGradient (cubeRule d) t := by
  rw [class_eq_iff,twistedFamily,twistedFamily,labelledBlocks,labelledBlocks,relabel_iso_iff]
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨t,h,_⟩ := (rigid_twist_iso (wordHyp hw) (cubeSize hd) rigid u v e).mp he
    exact ⟨t,h⟩
  · rintro ⟨t,h⟩
    exact ⟨_,(rigid_twist_iso (wordHyp hw) (cubeSize hd) rigid u v _).mpr ⟨t,h,rfl⟩⟩

/-- Actual automorphisms, including permutations which were not presumed to respect fibres. -/
def twistAut {d : ℕ} (hd : 2≤d) {w : EdgeWord d} (hw : w∈noDirectionWords (CubeEdge d))
    (rigid : Subsingleton (baseFrames (cubeRule d) (edgeMatching 0 w))) (u : CubeOffsets d) :
    Multiplicative (shifts (cubeRule d)) ≃* automorphisms (twistedFamily d w u) := by
  refine MulEquiv.trans ?_ (automorphismRelabel (fourLabels d) _)
  rw [twisted_aut_eq (wordHyp hw) (cubeSize hd) rigid]
  refine MulEquiv.trans ?_ (fullFourAut _ _ (wordHyp hw) (cubeSize hd))
  apply MulEquiv.ofBijective SemidirectProduct.inl
  exact ⟨SemidirectProduct.inl_injective,fun g => ⟨g.left,SemidirectProduct.ext rfl (rigid.elim _ _)⟩⟩

#print axioms CubeOffsets
#print axioms twistedFamily
#print axioms twistedFamily_injective
#print axioms cube_offsets_card
#print axioms twist_labelled_count
#print axioms twist_rank
#print axioms twist_class_iff
#print axioms twistAut
end
end Erdos722.FourPoint
