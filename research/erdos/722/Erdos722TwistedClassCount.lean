import Erdos722TwistedCubeFamilies

/-! # Exact number of unrestricted isomorphism classes for fixed rigid matchings -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Finset Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

def twistClasses (d : ℕ) (w : EdgeWord d) := univ.image (fun u => classOf (twistedFamily d w u))

private theorem quotient_class {d : ℕ} (hd : 2≤d) {w : EdgeWord d} (hw : w∈noDirectionWords (CubeEdge d))
    (rigid : Subsingleton (baseFrames (cubeRule d) (edgeMatching 0 w))) (u v : CubeOffsets d) :
    classOf (twistedFamily d w u)=classOf (twistedFamily d w v) ↔
    (u : CubeOffsets d ⧸ (blockGradient (cubeRule d)).range)=v := by
  rw [twist_class_iff hd hw rigid,QuotientAddGroup.eq,AddMonoidHom.mem_range]
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,by abel⟩
  · rintro ⟨t,h⟩
    exact ⟨t,by rw [h]; abel⟩

/-- The quotient by arbitrary point isomorphism on this family is exactly
the quotient of the two-coordinate block words by the incidence range. -/
def twistClassEquiv {d : ℕ} (hd : 2≤d) {w : EdgeWord d} (hw : w∈noDirectionWords (CubeEdge d))
    (rigid : Subsingleton (baseFrames (cubeRule d) (edgeMatching 0 w))) :
    (CubeOffsets d ⧸ (blockGradient (cubeRule d)).range) ≃ twistClasses d w := by
  let f (q : CubeOffsets d ⧸ (blockGradient (cubeRule d)).range) : twistClasses d w :=
    ⟨classOf (twistedFamily d w q.out),mem_image.mpr ⟨_,mem_univ _,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    have eq := (quotient_class hd hw rigid p.out q.out).mp (congrArg Subtype.val h)
    exact p.out_eq.symm.trans (eq.trans q.out_eq)
  · rintro ⟨C,hC⟩
    obtain ⟨u,_,rfl⟩ := mem_image.mp hC
    exact ⟨u,Subtype.ext ((quotient_class hd hw rigid _ u).mpr (Quotient.out_eq _))⟩

theorem twist_class_count {d : ℕ} (hd : 2≤d) {w : EdgeWord d} (hw : w∈noDirectionWords (CubeEdge d))
    (rigid : Subsingleton (baseFrames (cubeRule d) (edgeMatching 0 w))) :
    (twistClasses d w).card=4^(blockNumber (2^d)+d+1-2^d) := by
  let G := blockGradient (cubeRule d)
  have A := G.range.card_eq_card_quotient_mul_card_addSubgroup
  have D := G.ker.card_eq_card_quotient_mul_card_addSubgroup
  rw [Nat.card_congr (twistClassEquiv hd hw rigid),Nat.card_eq_fintype_card (α:=twistClasses d w),
    Fintype.card_coe,cube_offsets_card] at A
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange G).toEquiv] at D
  have domain : Nat.card (Cube d → Fibre)=4^(2^d) := by simp [Nat.card_eq_fintype_card,Fibre,Cube]
  have ker : Nat.card G.ker=4^(d+1) := by
    rw [show G.ker=shifts (cubeRule d) from gradient_kernel _,shifts_card,cube_checks_card]
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  rw [domain,ker] at D
  have h : (twistClasses d w).card * 4^(2^d)=4^(blockNumber (2^d)+d+1) := by
    rw [D,← mul_assoc,← A,← pow_add]
    congr 1
  have pos : 0<(twistClasses d w).card := card_pos.mpr ⟨_,mem_image.mpr ⟨0,mem_univ _,rfl⟩⟩
  have le : 2^d≤blockNumber (2^d)+d+1 := (Nat.pow_le_pow_iff_right (by decide : 1<4)).mp
    ((Nat.le_mul_of_pos_left _ pos).trans h.le)
  apply Nat.eq_of_mul_eq_mul_right (by positivity : 0<4^(2^d))
  rw [h,← pow_add,Nat.sub_add_cancel le]

#print axioms twistClasses
#print axioms twistClassEquiv
#print axioms twist_class_count
end
end Erdos722.FourPoint
