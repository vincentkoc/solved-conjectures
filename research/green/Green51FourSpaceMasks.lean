import Green51FourSpaceProjection

/-! # Finite binary masks and field-valued coordinates -/

open Finset Green50Downsets
open scoped Classical
namespace Green51FourSpace
local notation "F" => ZMod 2

/-- A low-order-first binary mask, interpreted as a vector over the two-element field. -/
def decode (n m:Nat) : Cube n := fun i => if m.testBit i then 1 else 0

theorem decode_xor (n a b:Nat) : decode n (a ^^^ b)=decode n a+decode n b := by
  funext i
  change (if (a ^^^ b).testBit i then 1 else 0 : F)=_+_
  rw [Nat.testBit_xor]
  cases ha:a.testBit i <;> cases hb:b.testBit i <;> simp [decode,ha,hb,ZModModule.add_self]

theorem decode_inj (n:Nat) : Function.Injective (fun i:Fin (2^n) => decode n i.val) := by
  intro a b eq
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj:j<n
  · have h := congrFun eq ⟨j,hj⟩
    change (if a.val.testBit j then 1 else 0 : F)=(if b.val.testBit j then 1 else 0) at h
    cases e:a.val.testBit j <;> cases e':b.val.testBit j <;> simp_all
  · have le := Nat.pow_le_pow_right (by decide : 0<2) (le_of_not_gt hj)
    rw [Nat.testBit_eq_false_of_lt (a.isLt.trans_le le),Nat.testBit_eq_false_of_lt (b.isLt.trans_le le)]

noncomputable def maskEquiv (n:Nat) : Fin (2^n) ≃ Cube n :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr ⟨decode_inj n,by simp [Cube]⟩)

noncomputable def encode {n:Nat} (w:Cube n) : Nat := ((maskEquiv n).symm w).val

theorem encode_lt {n:Nat} (w:Cube n) : encode w<2^n := ((maskEquiv n).symm w).isLt

@[simp] theorem decode_encode {n:Nat} (w:Cube n) : decode n (encode w)=w := (maskEquiv n).apply_symm_apply _

theorem encode_decode {n m:Nat} (h:m<2^n) : encode (decode n m)=m :=
  congrArg Fin.val ((maskEquiv n).symm_apply_apply ⟨m,h⟩)

theorem encode_add {n:Nat} (x y:Cube n) : encode (x+y)=encode x ^^^ encode y := by
  rw [←encode_decode (Nat.xor_lt_two_pow (encode_lt x) (encode_lt y)),decode_xor,decode_encode,decode_encode]

theorem decode_zero (n:Nat) : decode n 0=0 := by funext i;simp [decode]

@[simp] theorem encode_zero (n:Nat) : encode (0:Cube n)=0 := by
  rw [←decode_zero n];exact encode_decode (by positivity)
end Green51FourSpace
#print axioms Green51FourSpace.encode_add
