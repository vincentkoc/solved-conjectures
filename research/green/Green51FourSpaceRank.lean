import Green51FourSpaceCoordinates
import Green51FourSpaceResidual

/-! # The rank bound after fixing one six-site relation -/
open Finset Green50Downsets Green50Sharp
open scoped Classical
namespace Green51FourSpace
local notation "F" => ZMod 2

theorem normalized_rank {C:Submodule F (Cube 16)} (hc:validCode C) {s:Cube 16}
    (hs:s∈C) (shape:supp s=positions 63) : Module.finrank F C≤5 := by
  classical
  have es : s=decode 16 63 := by
    funext i
    have h : (s i≠0) ↔ (63:Nat).testBit i.val=true := by
      simpa [supp,positions] using (show i∈supp s ↔ i∈positions 63 from shape ▸ Iff.rfl)
    rcases (by decide : ∀b:F,b=0∨b=1) (s i) with e|e <;> cases hb:(63:Nat).testBit i.val <;> simp_all [decode]
  have hi0 : high s=0 := by
    rw [es]
    exact (by decide +kernel : high (decode 16 63)=0)
  have lo63 : encode (low s)=63 := by
    rw [es,show low (decode 16 63)=decode 8 63 by decide +kernel,encode_decode (by decide)]
  let c := ((LinearMap.proj (R:=F) (φ:=fun _:Fin 8=>F) (5:Fin 8)).comp low).comp C.subtype
  let S := c.ker
  let toC := C.subtype.comp S.subtype
  let H := high.comp toC
  have ok (x:S) : Certificate.allowed (encode (H x)) (encode (low (toC x)))=true := by
    let w:=toC x
    have mem:w∈C := x.val.property
    have zero:(low w) 5=0 := x.property
    have off:(encode (low w)).testBit 5=false := Bool.eq_false_iff.mpr fun yes=>(bit_test _ (5:Fin 8)).mp yes zero
    have both:=code_admissible hc (w+s) (C.add_mem mem hs)
    rw [map_add,hi0,add_zero,map_add,encode_add,lo63] at both
    change (!((encode (low w)).testBit 5) && Certificate.admissible (encode (high w)) (encode (low w)) &&
      Certificate.admissible (encode (high w)) (encode (low w) ^^^ 63))=true
    rw [off,code_admissible hc w mem,both]
    rfl
  have kernel_zero (x:S) (hhigh:H x=0) : x=0 := by
    have valid:=ok x
    rw [hhigh,encode_zero] at valid
    have eql:=Certificate.zero_low_offset (encode_lt (low (toC x))) valid
    have eqh:=congrArg encode hhigh
    rw [encode_zero] at eqh
    have total : encode (toC x)=0 := by
      rw [←split_encode, eql]
      change 256*encode (H x)+0=0
      simp [eqh]
    apply Subtype.ext
    apply Subtype.ext
    change toC x=0
    rw [←decode_encode (toC x),total,decode_zero]
  have H_inj : Function.Injective H := by
    intro x y hxy
    have zero : x+y=0 := kernel_zero _ ((H.map_add x y).trans (by rw [hxy,ZModModule.add_self]))
    exact add_right_cancel (zero.trans (ZModModule.add_self y).symm)
  let e := LinearEquiv.ofInjective H H_inj
  let L := low.comp (toC.comp e.symm.toLinearMap)
  have allowed (y:H.range) : Certificate.allowed (encode y.val) (encode (L y))=true := by
    have v:=ok (e.symm y)
    have he:H (e.symm y)=y.val := congrArg Subtype.val (e.apply_symm_apply y)
    rw [he] at v
    exact v
  have rankH := no_linear_offsets H.range L allowed
  rw [H.finrank_range_of_inj H_inj] at rankH
  have rk:=c.finrank_range_add_finrank_ker
  have one:=Submodule.finrank_le c.range
  have dF:Module.finrank F F=1 := by simp
  rw [dF] at one
  change Module.finrank F c.ker≤4 at rankH
  omega
end Green51FourSpace
#print axioms Green51FourSpace.normalized_rank
