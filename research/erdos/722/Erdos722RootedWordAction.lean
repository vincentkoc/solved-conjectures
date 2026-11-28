import Erdos722TypicalFourFibreSystems

/-! # The rooted linear and colour action on normalized matching words -/

namespace Erdos722.FourPoint
open Finset Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

abbrev RootFrames (d : ℕ) := (Cube d ≃ₗ[ZMod 2] Cube d) × Colour

theorem linear_rooted {d : ℕ} (L : Cube d ≃ₗ[ZMod 2] Cube d) : L.toEquiv∈rootedBases d :=
  (mem_rootedBases ..).mpr ⟨L.map_zero,fun x y z => by simp⟩

theorem rooted_linear {d : ℕ} {b : Perm (Cube d)} (hb : b∈rootedBases d) :
    ∃ L : Cube d ≃ₗ[ZMod 2] Cube d,L.toEquiv=b := by
  obtain ⟨h0,h3⟩ := (mem_rootedBases ..).mp hb
  let f : Cube d →+ Cube d :=
    { toFun := b
      map_zero' := h0
      map_add' := fun x y => by simpa only [add_zero,h0] using h3 x y 0 }
  exact ⟨LinearEquiv.ofBijective (f.toZModLinearMap 2) b.bijective,Equiv.ext fun _ => rfl⟩

theorem root_frames_card (d : ℕ) : Nat.card (RootFrames d)≤6*(2^d)^d := by
  let f (L : Cube d ≃ₗ[ZMod 2] Cube d) : rootedBases d := ⟨L.toEquiv,linear_rooted L⟩
  have inj : Function.Injective f := fun _ _ h => LinearEquiv.ext fun x =>
    DFunLike.congr_fun (congrArg Subtype.val h) x
  have h := Nat.card_le_card_of_injective f inj
  rw [Nat.card_eq_finsetCard] at h
  have c : Nat.card Colour=6 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [Nat.card_prod,c,mul_comm]
  exact Nat.mul_le_mul_left _ (h.trans (rooted_bases_card d))

private def changeCoords {I : Type*} (M : Matching I) (b : Perm I) (s : Colour) : Matching I where
  transport i j := s*M.transport (b.symm i) (b.symm j)*s⁻¹
  diagonal i := by simp [M.diagonal]
  reverse i j := by rw [M.reverse (b.symm i) (b.symm j)]; simp [mul_assoc]

private theorem reconstruct {I : Type*} [LinearOrder I] [Fintype I] {o : I} (M : Matching I)
    (h : Normalized M o) (i j : I) :
    (edgeMatching o (fun e => M.transport e.val.1 e.val.2)).transport i j=M.transport i j := by
  dsimp only [edgeMatching]
  unfold edgeMove
  split
  · rfl
  split
  · exact (M.reverse j i).symm
  · rename_i hn
    by_cases hi : i=o
    · subst i; exact (h j).symm
    by_cases hj : j=o
    · subst j; rw [M.reverse o i,h i,inv_one]
    by_cases eq : i=j
    · subst j; exact (M.diagonal i).symm
    rcases lt_or_gt_of_ne eq with lt|gt
    · exact False.elim (by apply ‹(i,j)∉edges o›; exact (mem_edges ..).mpr ⟨⟨hi,hj⟩,lt⟩)
    · exact False.elim (hn ((mem_edges ..).mpr ⟨⟨hj,hi⟩,gt⟩))

def recode {d : ℕ} (g : RootFrames d) (w : EdgeWord d) : EdgeWord d :=
  let N := changeCoords (edgeMatching 0 w) g.1.toEquiv g.2
  fun e => N.transport e.val.1 e.val.2

theorem recode_transport {d : ℕ} (g : RootFrames d) (w : EdgeWord d) (i j : Cube d) :
    (edgeMatching 0 (recode g w)).transport i j =
      g.2*(edgeMatching 0 w).transport (g.1.symm i) (g.1.symm j)*g.2⁻¹ := by
  apply reconstruct (changeCoords _ _ _) _ i j
  intro x
  change g.2*(edgeMatching 0 w).transport (g.1.symm 0) (g.1.symm x)*g.2⁻¹=1
  rw [map_zero,edge_normalized 0 w (g.1.symm x),mul_one,mul_inv_cancel]

theorem frame_iff_recode {d : ℕ} (g : RootFrames d) (w v : EdgeWord d) :
    Frame (edgeMatching 0 w) (edgeMatching 0 v) g.1.toEquiv g.2 ↔ recode g w=v := by
  constructor
  · intro h
    funext e
    have q := h (g.1.symm e.val.1) (g.1.symm e.val.2)
    change g.2*_=(edgeMatching 0 v).transport (g.1 (g.1.symm _)) (g.1 (g.1.symm _))*g.2 at q
    simp only [LinearEquiv.apply_symm_apply,edge_forward] at q
    exact (congrArg (·*g.2⁻¹) q).trans (mul_inv_cancel_right ..)
  · rintro rfl i j
    rw [recode_transport]
    change _=g.2*(edgeMatching 0 w).transport (g.1.symm (g.1 i)) (g.1.symm (g.1 j))*g.2⁻¹*g.2
    simp

instance rootedWordAction (d : ℕ) : MulAction (RootFrames d) (EdgeWord d) where
  smul := recode
  one_smul w := (frame_iff_recode 1 w w).mp (fun i j => by simp)
  mul_smul g h w := by
    change recode (g*h) w=recode g (recode h w)
    apply (frame_iff_recode (g*h) w _).mp
    have fh := (frame_iff_recode h w _).mpr rfl
    have fg := (frame_iff_recode g (recode h w) _).mpr rfl
    intro i j
    change (g.2*h.2)*_=(edgeMatching 0 _).transport (g.1 (h.1 i)) (g.1 (h.1 j))*(g.2*h.2)
    rw [mul_assoc,fh,← mul_assoc,fg,mul_assoc]
    rfl

#print axioms RootFrames
#print axioms linear_rooted
#print axioms rooted_linear
#print axioms root_frames_card
#print axioms recode
#print axioms recode_transport
#print axioms frame_iff_recode
#print axioms rootedWordAction
end
end Erdos722.FourPoint
