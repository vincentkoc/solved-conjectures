import Green51FourSpaceMasks
import Green51FourSpaceCover
import Green51SmallDimensions

/-! # Weights, shortening, and binary parity checks -/
open Finset Green50Downsets Green50Sharp
open scoped Classical
namespace Green51FourSpace
local notation "F" => ZMod 2

/-- A binary code of length sixteen and dimension six has a nonzero word below weight eight. -/
theorem below_eight (C:Submodule F (Cube 16)) (dim:6≤Module.finrank F C) :
    ∃ w∈C,w≠0 ∧ (supp w).card<8 := by
  classical
  by_contra! high
  let coord := (LinearMap.proj (R:=F) (φ:=fun _:Fin 16=>F) (0:Fin 16)).comp C.subtype
  let S := coord.ker
  have deleted (x:S) : x.val.val 0=0 := x.property
  let cut : S →ₗ[F] Cube 15 :=
    { toFun := fun x i => x.val.val i.succ
      map_add' := by intro a b; rfl
      map_smul' := by intro a b; rfl }
  have inj : Function.Injective cut := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => congrFun he j) i
    exact (deleted x).trans (deleted y).symm
  have wt (x:S) : (supp (cut x)).card=(supp x.val.val).card := by
    simp only [supp,card_filter,Fin.sum_univ_succ,deleted,ne_eq,not_true_eq_false,ite_false,zero_add]
    rfl
  have dist (v:cut.range) (hv:v≠0) : 8≤(supp v.val).card := by
    obtain ⟨x,hx⟩ := v.property
    rw [←hx,wt]
    apply high _ x.val.property
    intro hz
    apply hv
    apply Subtype.ext
    change v.val=0
    rw [←hx]
    exact (congrArg cut (show x=0 by exact Subtype.ext (Subtype.ext hz))).trans cut.map_zero
  have p := Green51SmallDimensions.linear_plotkin cut.range dist
  rw [cut.finrank_range_of_inj inj] at p
  have rk := coord.finrank_range_add_finrank_ker
  have atmost := Submodule.finrank_le coord.range
  have : Module.finrank F F=1 := by simp
  rw [this] at atmost
  have ds : 5≤Module.finrank F S := by dsimp only [S];omega
  have pow := Nat.pow_le_pow_right (by decide : 0<2) ds
  change 32 ≤ 2^Module.finrank F S at pow
  omega

/-- A scalar parity check is the dot product with its values on the coordinate basis. -/
theorem check_dot {n:ℕ} (L:Cube n →ₗ[F] F) (w:Cube n) :
    L w = ∑ i:Fin n, w i*L (Pi.single i 1) := by
  conv_lhs => rw [←Finset.univ_sum_single w,map_sum]
  apply sum_congr rfl
  intro i _
  rcases (show ∀ b:F,b=0 ∨ b=1 from by decide) (w i) with h|h <;> simp [h]

theorem byte_weight (b:ℕ) (small:b<256) :
    Certificate.byteWeight b=(univ.filter (fun i:Fin 8=>b.testBit i.val=true)).card := by
  have ht : ∀ b:Fin 256,Certificate.byteWeight b.val=(univ.filter (fun i:Fin 8=>b.val.testBit i.val=true)).card := by decide +kernel
  exact ht ⟨b,small⟩

/-- Natural-number masks implement the scalar dot product over the binary field. -/
theorem orthogonal_check (L:Cube 8 →ₗ[F] F) (u:Nat) (small:u<256) :
    Certificate.orthogonal u (encode (fun i:Fin 8=>L (Pi.single i 1)))=true ↔ L (decode 8 u)=0 := by
  let r:=encode (fun i:Fin 8=>L (Pi.single i 1))
  change (Certificate.byteWeight (u &&& r)%2 == 0)=true ↔ _
  have bit (i:Fin 8) : (if r.testBit i.val then 1 else 0 : F)=L (Pi.single i 1) :=
    congrFun (decode_encode (fun i:Fin 8=>L (Pi.single i 1))) i
  have dot : L (decode 8 u) = ((univ.filter (fun i:Fin 8=>(u &&& r).testBit i.val=true)).card : F) := by
    rw [check_dot,Finset.card_eq_sum_ones]
    push_cast
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    rw [←bit,Nat.testBit_and]
    cases hu:u.testBit i.val <;> cases hr:r.testBit i.val <;> simp [decode,hu]
  rw [dot,ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero,byte_weight _ (lt_of_le_of_lt Nat.and_le_left small)]
  simp
end Green51FourSpace
#print axioms Green51FourSpace.below_eight
#print axioms Green51FourSpace.orthogonal_check
