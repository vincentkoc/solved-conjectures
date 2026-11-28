import Erdos478WindowPairIncidence
import Erdos478CoprimeRootMoments

/-! # Boundary terms in the exact root count of a translated factorial collision -/

namespace Erdos478.WindowAverage
open Polynomial Finset LocalSpacing
open scoped Classical
noncomputable section

/-- The only residues unavailable as starts are zero and the last H residues.
For fixed offsets their characteristic-zero evaluations bound every bad prime. -/
def boundaryBound (H s k : ℕ) :=
  (range (H+1)).sup fun t => ((translatedGap ℤ s k).eval (-(t:ℤ))).natAbs

private theorem boundary_not_root {p H s k t : ℕ} (hk : 2≤k) (ht : t≤H)
    (large : boundaryBound H s k<p) :
    ¬(translatedGap (ZMod p) s k).IsRoot (-(t:ZMod p)) := by
  let f := translatedGap ℤ s k
  let z := -(t:ℤ)
  have nonzero : f.eval z≠0 := by
    intro h
    have root : f.IsRoot z := h
    have mapped := root.map (f:=Int.castRingHom ℚ)
    rw [show f=translatedGap ℤ s k from rfl,map_translated] at mapped
    apply (translated_irreducible s (by omega : 0<k)).not_isRoot_of_natDegree_ne_one _ mapped
    rw [(translated_degree ℚ s (by omega : 0<k)).natDegree_eq]
    omega
  intro bad
  have value : ((f.eval z:ℤ):ZMod p)=0 := by
    change Int.castRingHom (ZMod p) (f.eval z)=0
    rw [← eval₂_at_apply,← eval_map]
    simpa [f,z,map_translated,IsRoot] using bad
  have dv := Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp value)
  simp only [Int.natAbs_natCast] at dv
  have small : (f.eval z).natAbs≤boundaryBound H s k :=
    le_sup (f:=fun t : ℕ => ((translatedGap ℤ s k).eval (-(t:ℤ))).natAbs) (mem_range.mpr (by omega : t<H+1))
  exact (small.trans_lt large).not_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr nonzero) dv)

private theorem valid_of_root {p H s k : ℕ} [Fact p.Prime] (hk : 2≤k)
    (large : boundaryBound H s k<p) {x : ZMod p} (root : (translatedGap (ZMod p) s k).IsRoot x) :
    x.val∈starts p H := by
  rw [mem_starts]
  have val := x.val_lt
  constructor
  · by_contra! lo
    have z : x=0 := by rw [← ZMod.natCast_zmod_val x,show x.val=0 by omega,Nat.cast_zero]
    rw [z] at root
    exact boundary_not_root hk (Nat.zero_le H) large (by simpa using root)
  · by_contra! hi
    let t := p-x.val
    have th : t≤H := by dsimp [t]; omega
    have eq : x.val+t=p := by dsimp [t]; omega
    have add : x+(t:ZMod p)=0 := by rw [← ZMod.natCast_zmod_val x,← Nat.cast_add,eq,ZMod.natCast_self]
    have bad : (translatedGap (ZMod p) s k).IsRoot (-(t:ZMod p)) := by rwa [← eq_neg_of_add_eq_zero_left add]
    exact boundary_not_root hk th large bad

private theorem equal_of_root {p H r s a : ℕ} (rs : r<s) (inside : a∈starts p H)
    (root : (translatedGap (ZMod p) s (s-r)).IsRoot (a:ZMod p)) :
    a∈equalStarts p H r s := by
  have one : ((a+s).descFactorial (s-r):ZMod p)=1 := by
    simpa only [IsRoot.def,translatedGap,taylor_eval,← Nat.cast_add,eval_sub,eval_one,sub_eq_zero,
      descPochhammer_eval_eq_descFactorial] using root
  have nat := Nat.factorial_mul_descFactorial (by omega : s-r≤a+s)
  rw [show a+s-(s-r)=a+r by omega] at nat
  have prod := congrArg (fun j : ℕ => (j:ZMod p)) nat
  simp only [Nat.cast_mul,one,mul_one] at prod
  exact mem_filter.mpr ⟨inside,(ZMod.natCast_eq_natCast_iff' _ _ _).mp prod⟩

/-- Beyond the explicit boundary cutoff every modular root is a unique
positive starting index with the prescribed colliding positions. -/
theorem equalStarts_exact {p H r s : ℕ} (hp : p.Prime) (gap : r+2≤s) (sH : s≤H)
    (large : boundaryBound H s (s-r)<p) :
    (equalStarts p H r s).card=Nat.card (RootPairs.solutions (translatedGap ℤ s (s-r)) (ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  let f := translatedGap ℤ s (s-r)
  have iff (x : ZMod p) : f.eval₂ (Int.castRingHom (ZMod p)) x=0 ↔ (translatedGap (ZMod p) s (s-r)).IsRoot x := by
    rw [← map_translated,IsRoot.def,eval_map]
  let e : RootPairs.solutions f (ZMod p) ≃ equalStarts p H r s := {
    toFun := fun x =>
      let h := (iff x.val).mp x.prop
      let good := valid_of_root (by omega : 2≤s-r) large h
      ⟨x.val.val,equal_of_root (by omega) good (by simpa only [ZMod.natCast_zmod_val] using h)⟩
    invFun := fun a =>
      have valid := mem_starts.mp (mem_filter.mp a.prop).1
      have h := collision_root hp (Nat.le_add_right a.val r) (show a.val+r<a.val+s by omega)
        (show a.val+s<p by omega) (mem_filter.mp a.prop).2
      ⟨(a.val:ZMod p),(iff _).mpr (by simpa only [Nat.add_sub_cancel_left,Nat.add_sub_add_left] using h)⟩
    left_inv := fun x => Subtype.ext (ZMod.natCast_zmod_val x.val)
    right_inv := fun a => Subtype.ext (ZMod.val_natCast_of_lt (by have v := mem_starts.mp (mem_filter.mp a.prop).1; omega)) }
  exact (Nat.card_eq_finsetCard _).symm.trans (Nat.card_congr e.symm)

#print axioms boundaryBound
#print axioms equalStarts_exact
end
end Erdos478.WindowAverage
