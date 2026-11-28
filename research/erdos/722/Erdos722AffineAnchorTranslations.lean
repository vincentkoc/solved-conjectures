import Erdos722FourFibreGroups
import Erdos722FourFibreCube

/-! # Recovering a binary affine translation from the triples at one point -/

namespace Erdos722.FourPoint
open Finset QuadCompletion
open scoped Classical
noncomputable section

/-- All triples through one base point determine the affine law on the entire cube. -/
theorem offset_of_anchor {d : ℕ} (o : Cube d) (t : Cube d → Fibre)
    (at_o : ∀ i j, t (i+j+o)=t i+t j+t o) : Offset (cubeRule d) t := by
  intro i j k
  change t (i+j+k)=_
  have oo : o+o=0 := by funext a; exact CharTwo.add_self_eq_zero _
  have coord : (i+j+o)+k+o=i+j+k := by
    calc
      _ = (i+j+k)+(o+o) := by ac_rfl
      _ = _ := by rw [oo,add_zero]
  rw [← coord,at_o,at_o]
  calc
    _ = (t i+t j+t k)+(t o+t o) := by ac_rfl
    _ = _ := by rw [fibre_double,add_zero]

def affineBasisMarks (d : ℕ) : Finset (Cube d) :=
  insert 0 (univ.image fun i => Pi.basisFun (ZMod 2) (Fin d) i)

theorem affineBasisMarks_bound (d : ℕ) : (affineBasisMarks d).card≤d+1 := by
  let basis := Pi.basisFun (ZMod 2) (Fin d)
  exact (card_insert_le 0 (univ.image fun i => basis i)).trans
    (Nat.add_le_add_right (card_image_le.trans (by simp)) _)

/-- An affine fibre translation that vanishes on the marked affine basis vanishes everywhere. -/
theorem offset_zero_on_basis {d : ℕ} {t : Cube d → Fibre} (law : Offset (cubeRule d) t)
    (vanish : ∀ q∈affineBasisMarks d, t q=0) : t=0 := by
  let B := Pi.basisFun (ZMod 2) (Fin d)
  have t0 := vanish 0 (mem_insert_self ..)
  let add : Cube d →+ Fibre :=
    { toFun := t, map_zero' := t0, map_add' := fun x y => by
        simpa only [cubeRule,add_zero,t0] using law x y 0 }
  have eq : add.toZModLinearMap 2=0 := by
    apply B.ext
    intro i
    exact vanish (B i) (mem_insert_of_mem (mem_image_of_mem _ (mem_univ i)))
  exact funext fun x => DFunLike.congr_fun eq x

theorem sparse_basis_size {d : ℕ} (hd : 6≤d) : 8*(d+1)<2^d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [pow_succ]; omega

#print axioms offset_of_anchor
#print axioms affineBasisMarks
#print axioms affineBasisMarks_bound
#print axioms offset_zero_on_basis
#print axioms sparse_basis_size
end
end Erdos722.FourPoint
