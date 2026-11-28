import Erdos478ReflectedParityValues
import Erdos478InverseParity
import ThetaOddInverseCount

/-! # Products from one even and one odd factorial index -/

namespace Erdos478.ParityProducts
open Finset
open Arxiv.«2501.03234» ThetaFourier ThetaOddInverseCount ThetaReciprocalCutoff
open scoped Classical
noncomputable section
variable {p : ℕ} [Fact p.Prime]

private theorem peel (i : ℕ) (hi : 0 < i) :
    (i.factorial : ZMod p)=(i:ZMod p)*((i-1).factorial : ZMod p) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  rw [Nat.factorial_succ,Nat.cast_mul]
  rfl

theorem even_in_mixed (hp : p%2=1) {x : ZMod p} (nz : x≠0) (he : x.val%2=0) : x∈mixedProducts p := by
  let i := x.val
  have lt : i<p := x.val_lt
  have pos : 0 < i := ZMod.val_pos.mpr nz
  have ee : (i.factorial : ZMod p)∈parityValues p 0 := mem_parity.mpr ⟨i,lt,he,rfl⟩
  have odd : (((i-1).factorial : ℕ):ZMod p)∈parityValues p 1 := mem_parity.mpr ⟨i-1,by omega,by dsimp [i]; omega,rfl⟩
  have oo : (((i-1).factorial : ZMod p))⁻¹∈parityValues p 1 := by simpa using reflected_value hp odd
  refine mem_mixed.mpr ⟨_,ee,_,oo,?_⟩
  rw [peel i pos,mul_inv_cancel_right₀ (no_zero odd),ZMod.natCast_zmod_val]

theorem inverse_odd_in_mixed (hp : p%2=1) {x : ZMod p} (ho : x.val%2=1) : x⁻¹∈mixedProducts p := by
  have nz : x≠0 := by rintro rfl; simp at ho
  let i := x.val
  have lt : i<p := x.val_lt
  have pos : 0 < i := ZMod.val_pos.mpr nz
  have odd : (i.factorial : ZMod p)∈parityValues p 1 := mem_parity.mpr ⟨i,lt,ho,rfl⟩
  have even : (((i-1).factorial : ℕ):ZMod p)∈parityValues p 0 := mem_parity.mpr ⟨i-1,by omega,by dsimp [i]; omega,rfl⟩
  have oo : ((i.factorial : ZMod p))⁻¹∈parityValues p 1 := by simpa using reflected_value hp odd
  refine mem_mixed.mpr ⟨_,even,_,oo,?_⟩
  rw [peel i pos,mul_inv_rev,← mul_assoc,mul_inv_cancel₀ (no_zero even),one_mul,ZMod.natCast_zmod_val]

theorem mixed_contains_inverse_count (hp : p%2=1) :
    p/2+inverseCount p≤(mixedProducts p).card := by
  let V := (odds p).image Neg.neg
  let J := (odds p).filter (fun x => x⁻¹∈odds p)
  have parity {x : ZMod p} (hx : x∈odds p) : x.val%2=1 := (mem_filter.mp hx).2
  have even {x : ZMod p} (hx : x∈V) : x≠0 ∧ x.val%2=0 := by
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    have h := parity hy
    have nz : y≠0 := by rintro rfl; simp at h
    have : NeZero y := ⟨nz⟩
    have vl := y.val_lt
    exact ⟨neg_ne_zero.mpr nz,by rw [ZMod.val_neg_of_ne_zero]; omega⟩
  have dis : Disjoint V J := by
    apply disjoint_left.mpr
    intro x hx hj
    have a := (even hx).2
    have b := parity (mem_filter.mp hj).1
    omega
  have inc : V∪J⊆mixedProducts p := by
    intro x hx
    rcases mem_union.mp hx with v|j
    · exact even_in_mixed hp (even v).1 (even v).2
    · simpa only [inv_inv] using inverse_odd_in_mixed hp (parity (mem_filter.mp j).2)
  have eq : V.card=p/2 := (card_image_of_injective _ neg_injective).trans (card_odds hp)
  have low := card_le_card inc
  rwa [card_union_of_disjoint dis,eq] at low

theorem mixed_pointwise (hp : p%2=1) : 4*p ≤ 6*(mixedProducts p).card+2 := by
  have H := InverseParity.six_mul_card_odd_inverse (p:=p) hp
  have same : ((odds p).filter (fun a => a⁻¹∈odds p))=
      univ.filter (fun x : ZMod p => x.val%2=1 ∧ x⁻¹.val%2=1) := by ext; simp [odds]
  change p+1≤6*_ at H
  rw [← same] at H
  have low := mixed_contains_inverse_count hp
  unfold inverseCount at low
  omega

/-- An unconditional finite bound with the checked elementary Kloosterman error. -/
theorem mixed_discrepancy (hp : p%2=1) :
    3*((p:ℝ)-1)≤4*((mixedProducts p).card:ℝ)+2*discrepancy p := by
  have inv := (abs_le.mp (inverse_discrepancy hp)).1
  have low : ((p/2:ℕ):ℝ)+inverseCount p≤(mixedProducts p).card := by exact_mod_cast mixed_contains_inverse_count hp
  have eq : 2*((p/2:ℕ):ℝ)+1=p := by exact_mod_cast (show 2*(p/2)+1=p by omega)
  linarith

#print axioms even_in_mixed
#print axioms inverse_odd_in_mixed
#print axioms mixed_contains_inverse_count
#print axioms mixed_pointwise
#print axioms mixed_discrepancy
end
end Erdos478.ParityProducts
