import Green51FourSpaceParity

/-! # Reading the two halves of a sixteen-coordinate code -/
open Finset Green50Downsets Green50Sharp
namespace Green51FourSpace
local notation "F" => ZMod 2

def positions (p:Nat) : Finset (Fin 16) := univ.filter fun i=>p.testBit i.val=true

/-- The weight and affine-hyperplane conditions on a sixteen-coordinate binary code. -/
def validCode (C:Submodule F (Cube 16)) : Prop := ∀ w∈C,
  2∣(supp w).card ∧ (supp w).card≠2 ∧ (supp w).card≠4 ∧
  ((supp w).card=6 → ∃ p∈Certificate.planes,supp w⊆positions p)


theorem bit_test {n:Nat} (w:Cube n) (i:Fin n) :
    (encode w).testBit i.val=true ↔ w i≠0 := by
  have h := congrFun (decode_encode w) i
  change (if (encode w).testBit i.val then 1 else 0 : F)=w i at h
  cases hb:(encode w).testBit i.val <;> simp_all [←h]

theorem positions_encode (w:Cube 16) : positions (encode w)=supp w := by
  ext i
  simp [positions,supp,bit_test]

def low : Cube 16 →ₗ[F] Cube 8 :=
  { toFun := fun w i => w (Fin.castAdd 8 i)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
def high : Cube 16 →ₗ[F] Cube 8 :=
  { toFun := fun w i => w (Fin.natAdd 8 i)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

theorem split_encode (w:Cube 16) : 256*encode (high w)+encode (low w)=encode w := by
  let m := encode w
  have lo : decode 8 (m%256)=low w := by
    funext i
    have h := congrFun (decode_encode w) (Fin.castAdd 8 i)
    change (if (m % 2^8).testBit i.val then 1 else 0 : F)=_
    rw [Nat.testBit_mod_two_pow,decide_eq_true i.isLt,Bool.true_and]
    exact h
  have hi : decode 8 (m/256)=high w := by
    funext i
    have h:=congrFun (decode_encode w) (Fin.natAdd 8 i)
    change (if (m/2^8).testBit i.val then 1 else 0 : F)=_
    rw [Nat.testBit_div_two_pow,Nat.add_comm]
    exact h
  have hm : m<65536 := encode_lt _
  rw [←lo,←hi,encode_decode (by change m/256<256;omega),encode_decode (by change m%256<256;omega)]
  exact Nat.div_add_mod m 256

theorem split_weight (w:Cube 16) :
    Certificate.byteWeight (encode (high w))+Certificate.byteWeight (encode (low w))=(supp w).card := by
  have wt (v:Cube 8) : Certificate.byteWeight (encode v)=(supp v).card := by
    rw [byte_weight _ (encode_lt v)]
    simp [bit_test,supp]
  rw [wt,wt,add_comm]
  simp only [supp,card_filter]
  exact (Fin.sum_univ_add (a:=8) (b:=8) (fun i=> if w i≠0 then 1 else 0)).symm

theorem contained_bits (w:Cube 16) (p:Nat) (sub:supp w⊆positions p) :
    encode w &&& p=encode w := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  cases e:(encode w).testBit j with
  | false => rfl
  | true =>
    have hj : j<16 := by
      by_contra! le
      have small := (encode_lt w).trans_le (Nat.pow_le_pow_right (by decide : 0<2) le)
      simp_all [Nat.testBit_eq_false_of_lt small]
    have mem : (⟨j,hj⟩:Fin 16)∈supp w := by
      simpa [supp] using (bit_test w ⟨j,hj⟩).mp e
    exact (mem_filter.mp (sub mem)).2

theorem code_admissible {C:Submodule F (Cube 16)} (hc:validCode C) (w:Cube 16) (hw:w∈C) :
    Certificate.admissible (encode (high w)) (encode (low w))=true := by
  obtain ⟨par,two,four,flat⟩:=hc w hw
  unfold Certificate.admissible
  rw [split_encode,split_weight]
  by_cases zero:w=0
  · simp [zero]
  have pos : 0<(supp w).card := by
    by_contra! none
    have emp := card_eq_zero.mp (by omega : (supp w).card=0)
    apply zero
    funext i
    by_contra! bad
    have mem : i∈supp w := by simpa [supp] using bad
    simp [emp] at mem
  apply Bool.or_eq_true_iff.mpr <| Or.inr <| Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr (Nat.dvd_iff_mod_eq_zero.mp par),?_⟩
  by_cases big:8≤(supp w).card
  · simp [big]
  · have six:(supp w).card=6 := by omega
    obtain ⟨p,hp,sub⟩:=flat six
    apply Bool.or_eq_true_iff.mpr <| Or.inr <| Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr six,?_⟩
    exact List.any_eq_true.mpr ⟨p,hp,beq_iff_eq.mpr (contained_bits _ _ sub)⟩
end Green51FourSpace
#print axioms Green51FourSpace.code_admissible
