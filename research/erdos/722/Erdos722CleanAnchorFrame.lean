import Erdos722BlockwiseFibreCoordinates
import Erdos722FourFibreFrame

/-! # Detecting a common linear part at a point with ordinary transversals -/

namespace Erdos722.FourPoint
open QuadCompletion Finset Equiv
noncomputable section
variable {I J : Type*} [DecidableEq I] [Fintype I]

/-- All distinct-base triples through this point have ordinary addition, with a free constant. -/
def PlainThrough (P : Rule (I × Fibre)) (o : I) : Prop :=
  ∀ i k, i≠o → i≠k → o≠k → ∃ c : Fibre, ∀ x y z,
    (P.complete (i,x) (o,y) (k,z)).2=x+y+z+c

theorem plain_of_chart (Q : Rule I) (M : Matching I) (u : BlockOffsets Q)
    (D : BlockCoordinates Q) (o : I) (idAt : ∀ S : Finset I, o∈S →
      blockChart Q D S=fun _ => Equiv.refl Fibre) :
    PlainThrough (blockwiseRule Q M (twistedRule Q M u) (twisted_compatible ..) D) o := by
  intro i k io ik ok
  let B : Q.blocks := ⟨_,completed_block Q io ik ok⟩
  have ch : blockChart Q D (baseQuad Q i o k)=D B := dif_pos (completed_block Q io ik ok)
  have id : D B=fun _ => Equiv.refl Fibre := ch.symm.trans (idAt _ (by simp [baseQuad]))
  refine ⟨u B,fun x y z => ?_⟩
  have eq := blockwise_transversal Q M u D io ik ok x y z
  change D B _ _=D B _ x+D B _ y+D B _ z+u B at eq
  rw [id] at eq
  exact eq

theorem frame_at_plain_point {Q : Rule I} {R : Rule J} {M : Matching I} {N : Matching J}
    {P : Rule (I × Fibre)} {T : Rule (J × Fibre)} (src : Compatible Q M P) (dst : Compatible R N T)
    {b : I ≃ J} {f : I → Perm Fibre} (o : I) (size : 3≤Fintype.card I)
    (srcPlain : PlainThrough P o) (dstPlain : PlainThrough T (b o))
    (law : ∀ i j k x y z, f (Q.complete i j k) (P.complete (i,x) (j,y) (k,z)).2=
      (T.complete (b i,f i x) (b j,f j y) (b k,f k z)).2) :
    ∃ s : Colour, Frame M N b s ∧ ∀ i x, f i x=move s x+f i 0 := by
  obtain ⟨s,hs⟩ := affine_fibre (f o)
  have lin (i : I) (x : Fibre) : f i x=move s x+f i 0 := by
    by_cases io : i=o
    · simpa only [io] using hs x
    have less : ({i,o}:Finset I).card<(univ : Finset I).card := by rw [card_pair io,card_univ]; omega
    obtain ⟨k,_,out⟩ := exists_mem_notMem_of_card_lt_card less
    simp only [mem_insert,mem_singleton,not_or] at out
    have ik := Ne.symm out.1
    have ok := Ne.symm out.2
    obtain ⟨a,first⟩ := srcPlain i k io ik ok
    obtain ⟨c,second⟩ := dstPlain (b i) (b k) (b.injective.ne io) (b.injective.ne ik) (b.injective.ne ok)
    have h₁ := law i o k x 0 0
    have h₂ := law i o k 0 x 0
    simp only [first,second,add_zero,zero_add] at h₁ h₂
    exact add_right_cancel (calc
      f i x+f o 0 = f i 0+f o x := add_right_cancel (add_right_cancel (h₁.symm.trans h₂))
      _ = (move s x+f i 0)+f o 0 := by rw [hs x]; ac_rfl)
  refine ⟨s,?_,lin⟩
  intro i j
  apply move_faithful
  intro x
  have eq := law i i j 0 x 0
  rw [src.pair,dst.pair,Q.repeated] at eq
  simp only [zero_add] at eq
  rw [lin j (move (M.transport i j) x),lin i x] at eq
  rw [(show ∀ u z : Fibre, u+(z+u)=z by decide +kernel) (f i 0) (move s x),add_comm (f j 0)] at eq
  simpa only [move_product] using add_right_cancel eq

#print axioms PlainThrough
#print axioms plain_of_chart
#print axioms frame_at_plain_point
end
end Erdos722.FourPoint
