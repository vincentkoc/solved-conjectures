import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin

/-! # Translating a 1024-bit set under coordinate xor -/

namespace Green51BitTranslations

def low (j:ℕ) := (2^1024-1)/(2^(2^j)+1)
def high (j:ℕ) := low j <<< (2^j)
def flip (j m:ℕ) := ((m <<< (2^j)) &&& high j) ||| ((m >>> (2^j)) &&& low j)

private def Address (j i:ℕ) := if i.testBit j then
  (high j).testBit i=true ∧ (low j).testBit i=false ∧ 2^j≤i ∧ i-2^j=i ^^^ 2^j
  else (high j).testBit i=false ∧ (low j).testBit i=true ∧ 2^j+i=i ^^^ 2^j
private instance (j i:ℕ) : Decidable (Address j i) := by unfold Address; infer_instance

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem addresses (j:Fin 10) : ∀i:Fin 1024, Address j.val i.val := by
  fin_cases j <;> decide +kernel

theorem flip_bit (j:Fin 10) (m:ℕ) (i:Fin 1024) :
    (flip j.val m).testBit i.val=m.testBit (i.val ^^^ 2^j.val) := by
  have data := addresses j i
  unfold Address at data
  simp only [flip,Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  split at data
  · obtain ⟨a,b,c,d⟩ := data
    simp [a,b,c,d]
  · obtain ⟨a,b,c⟩ := data
    simp [a,b,c]

def shift (v m:ℕ) : ℕ → ℕ
  | 0 => m
  | k+1 => let a:=shift v m k; if v.testBit k then flip k a else a

private def offset (v:ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => if v.testBit k then (2^k) ^^^ offset v k else offset v k

private theorem effect (v m:ℕ) {k:ℕ} (hk:k≤10) (i:Fin 1024) :
    (shift v m k).testBit i.val=m.testBit (i.val ^^^ offset v k) := by
  induction k generalizing i with
  | zero => simp [shift,offset]
  | succ k ih =>
    have kb : k<10 := by omega
    have bound : 2^k<2^10 := Nat.pow_lt_pow_right (by decide) kb
    have h := Nat.xor_lt_two_pow (show i.val<2^10 from i.isLt) bound
    by_cases on : v.testBit k=true
    · simp only [shift,offset,on,if_true]
      rw [show (flip k (shift v m k)).testBit i.val=(shift v m k).testBit (i.val ^^^ 2^k) from
        flip_bit ⟨k,kb⟩ _ i,←Nat.xor_assoc]
      exact ih (by omega) ⟨_,h⟩
    · simpa only [shift,offset,on,Bool.false_eq_true,if_false] using ih (by omega) i

set_option maxRecDepth 5000 in
private theorem offset_ten : ∀ v:Fin 1024,offset v.val 10=v.val := by decide +kernel

theorem shift_bit (v i:Fin 1024) (m:ℕ) :
    (shift v.val m 10).testBit i.val=m.testBit (i.val ^^^ v.val) := by
  simpa only [offset_ten v] using effect v.val m (k:=10) le_rfl i

end Green51BitTranslations
#print axioms Green51BitTranslations.flip_bit
#print axioms Green51BitTranslations.shift_bit
