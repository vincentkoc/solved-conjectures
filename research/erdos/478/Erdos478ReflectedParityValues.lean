import Erdos478MixedProductOverlap
import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Factorial.BigOperators

/-! # Wilson reflection on even-indexed and odd-indexed factorial values -/

namespace Erdos478.ParityProducts
open Finset
open scoped Classical
noncomputable section

/-- The even set includes 0!, which equals the eligible factorial 1!.
The union therefore gives precisely the host value set. -/
def parityValues (p b : ℕ) := ((range p).filter (fun i => i%2=b)).image (fun i => (i.factorial : ZMod p))
def allValues (p : ℕ) := parityValues p 0 ∪ parityValues p 1
def mixedProducts (p : ℕ) := mixedImage (·*·) (parityValues p 0) (parityValues p 1)

theorem mem_parity {p b : ℕ} {x : ZMod p} : x∈parityValues p b ↔
    ∃ i<p,i%2=b ∧ (i.factorial : ZMod p)=x := by
  simp only [parityValues,mem_image,mem_filter,mem_range]
  exact ⟨fun ⟨i,⟨hi,hb⟩,eq⟩ => ⟨i,hi,hb,eq⟩,fun ⟨i,hi,hb,eq⟩ => ⟨i,⟨hi,hb⟩,eq⟩⟩

theorem mem_mixed {p : ℕ} {x : ZMod p} : x∈mixedProducts p ↔
    ∃ a∈parityValues p 0,∃ b∈parityValues p 1,a*b=x := by
  simp only [mixedProducts,mixedImage,mem_image,Prod.exists,mem_product]
  grind

variable {p : ℕ} [Fact p.Prime]

theorem allValues_host : (allValues p).image ZMod.val=(Ico 1 p).image (fun i => i.factorial%p) := by
  have hp := (Fact.out : p.Prime).two_le
  have all : allValues p=(Ico 1 p).image (fun i => (i.factorial : ZMod p)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,eq⟩ : ∃ i<p,(i.factorial : ZMod p)=x := by
        rcases mem_union.mp hx with he|ho <;> obtain ⟨i,hi,_,eq⟩ := mem_parity.mp ‹_› <;> exact ⟨i,hi,eq⟩
      cases i with
      | zero => exact mem_image.mpr ⟨1,mem_Ico.mpr ⟨by decide,by omega⟩,eq⟩
      | succ i => exact mem_image.mpr ⟨_,mem_Ico.mpr ⟨by omega,hi⟩,eq⟩
    · intro hx
      obtain ⟨i,hi,eq⟩ := mem_image.mp hx
      have ml := (mem_Ico.mp hi).2
      obtain he|ho : i%2=0 ∨ i%2=1 := by omega
      · exact mem_union_left _ (mem_parity.mpr ⟨i,ml,he,eq⟩)
      · exact mem_union_right _ (mem_parity.mpr ⟨i,ml,ho,eq⟩)
  rw [all,image_image]
  simp only [Function.comp_def,ZMod.val_natCast]

theorem host_card : (allValues p).card=((Ico 1 p).image (fun i => i.factorial%p)).card := by
  rw [← allValues_host,card_image_of_injective _ (ZMod.val_injective p)]

/-- Pair the top i factors of Wilson's product with their negatives at the bottom. -/
theorem reflected_factorials (i : ℕ) (hi : i<p) :
    (i.factorial : ZMod p)*((p-1-i).factorial : ZMod p)=(-1:ZMod p)^(i+1) := by
  have hp := (Fact.out : p.Prime).two_le
  have desc : ((p-1).descFactorial i : ZMod p)=(-1:ZMod p)^i*(i.factorial : ZMod p) := by
    rw [Nat.descFactorial_eq_prod_range,Nat.factorial_eq_prod_range_add_one,Nat.cast_prod,Nat.cast_prod]
    simp only [Nat.cast_add,Nat.cast_one]
    calc
      _ = ∏ j∈range i,(-1:ZMod p)*((j:ZMod p)+1) := by
        apply prod_congr rfl
        intro j hj
        have lt := mem_range.mp hj
        rw [Nat.cast_sub (by omega : j≤p-1),Nat.cast_sub (by omega : 1≤p),ZMod.natCast_self,Nat.cast_one]
        ring
      _ = _ := by rw [prod_mul_distrib,prod_const,card_range]
  have fac := congrArg (fun n : ℕ => (n:ZMod p)) (Nat.factorial_mul_descFactorial (n:=p-1) (k:=i) (by omega))
  simp only [Nat.cast_mul,desc,ZMod.wilsons_lemma] at fac
  rcases Nat.even_or_odd i with he|ho
  · rw [pow_succ,he.neg_one_pow,one_mul]
    rw [he.neg_one_pow,one_mul] at fac
    exact (mul_comm ..).trans fac
  · rw [pow_succ,ho.neg_one_pow,neg_mul_neg,one_mul]
    rw [ho.neg_one_pow,neg_one_mul,mul_neg,neg_inj] at fac
    exact (mul_comm ..).trans fac

theorem no_zero {b : ℕ} {x : ZMod p} (h : x∈parityValues p b) : x≠0 := by
  obtain ⟨i,hi,_,rfl⟩ := mem_parity.mp h
  intro hz
  have r := reflected_factorials i hi
  rw [hz,zero_mul] at r
  exact (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) r.symm

/-- Wilson reflection keeps parity at odd primes. For odd factorials it
gives the inverse; for even factorials it gives the negative inverse. -/
theorem reflected_value {b : ℕ} (hp : p%2=1) {x : ZMod p} (hx : x∈parityValues p b) :
    (if b=0 then -x⁻¹ else x⁻¹)∈parityValues p b := by
  have nz := no_zero hx
  obtain ⟨i,hi,hb,rfl⟩ := mem_parity.mp hx
  refine mem_parity.mpr ⟨p-1-i,by omega,by omega,?_⟩
  have r := reflected_factorials i hi
  by_cases he : b=0
  · rw [if_pos he]
    have parity : Even i := Nat.even_iff.mpr (by omega)
    apply mul_left_cancel₀ nz
    rw [r,pow_succ,parity.neg_one_pow,one_mul,mul_neg,mul_inv_cancel₀ nz]
  · rw [if_neg he]
    have parity : Odd i := Nat.odd_iff.mpr (by omega)
    apply mul_left_cancel₀ nz
    rw [r,pow_succ,parity.neg_one_pow,neg_mul_neg,one_mul,mul_inv_cancel₀ nz]

#print axioms parityValues
#print axioms allValues
#print axioms mixedProducts
#print axioms mem_parity
#print axioms mem_mixed
#print axioms allValues_host
#print axioms host_card
#print axioms reflected_factorials
#print axioms no_zero
#print axioms reflected_value
end
end Erdos478.ParityProducts
