import Green51MissingLabel
/-! # Doubly even subcodes on seventeen positions -/
open Finset Green50Downsets Green50Sharp
open scoped Classical Pointwise
namespace Green51ResidualPacking
local notation "F" => ZMod 2
private theorem large_unique (C:Submodule F (Cube 17))
    (dist:∀x:C,x≠0 → 8≤(supp x.val).card) {x y:C}
    (hx:(supp x.val).card=16) (hy:(supp y.val).card=16) : x=y := by
  have sub:supp (x+y).val⊆(supp x.val)ᶜ∪(supp y.val)ᶜ := by
    intro i hi
    by_contra h
    have ix:i∈supp x.val := by simpa using (notMem_union.mp h).1
    have iy:i∈supp y.val := by simpa using (notMem_union.mp h).2
    have one : ∀a:F,a≠0 → a=1:=by decide
    have ex:=one _ (mem_filter.mp ix).2
    have ey:=one _ (mem_filter.mp iy).2
    have bad:= (mem_filter.mp hi).2
    change x.val i+y.val i≠0 at bad
    exact bad (by rw [ex,ey];decide)
  have small:= (card_le_card sub).trans (card_union_le ..)
  rw [card_compl,card_compl,Fintype.card_fin,hx,hy] at small
  have eq:x+y=0:=by by_contra h;have d:=dist _ h;omega
  exact add_right_cancel (eq.trans (ZModModule.add_self y).symm)

theorem seventeen (C:Submodule F (Cube 17))
    (dist:∀x:C,x≠0 → 8≤(supp x.val).card)
    (four:∀x:C,4∣(supp x.val).card) :
    Module.finrank F C ≤ 5 := by
  classical
  let s (x:C) : ℤ:=17-2*(supp x.val).card
  let H:=(univ:Finset C).filter (fun x=>(supp x.val).card=16)
  have hc:H.card≤1:=card_le_one.mpr fun a ha b hb=>large_unique C dist
    (mem_filter.mp ha).2 (mem_filter.mp hb).2
  have identity (x:C) : s x^2+6*s x-7=(if x=0 then 384 else 0)+
      (if (supp x.val).card=16 then 128 else 0) := by
    by_cases zero:x=0
    · simp [zero,s,supp]
    have hi:(supp x.val).card≤17:=(supp x.val).card_le_univ.trans_eq (Fintype.card_fin _)
    have lo:=dist x zero
    have mult:=four x
    simp only [s,if_neg zero,zero_add]
    generalize hw:(supp x.val).card=w at *
    have cases:w=8 ∨ w=12 ∨ w=16:=by omega
    rcases cases with rfl|rfl|rfl <;> decide
  have total:=sum_congr (s₁:=(univ:Finset C)) rfl (fun x _=>identity x)
  have heavy : (∑x:C, if (supp x.val).card=16 then (128:ℤ) else 0)=(H.card:ℤ)*128 := by
    simp [H,sum_ite]
  rw [sum_add_distrib,heavy] at total
  simp only [sum_ite_eq',mem_univ,if_true] at total
  simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,sum_const,card_univ,nsmul_eq_mul] at total
  have second:=Green51Hadamard.weight_second_moment C
  change 17*(Fintype.card C:ℤ)≤∑x:C,(s x)^2 at second
  have first:=Green51Hadamard.weight_first_moment C
  change 0≤∑x:C,s x at first
  have hc' : (H.card:ℤ)≤1:=by exact_mod_cast hc
  have upper:(Fintype.card C:ℤ)<64:=by linarith
  by_contra! rank
  have bound:2^6≤2^Module.finrank F C := Nat.pow_le_pow_right (by decide) rank
  have eq:=Module.card_eq_pow_finrank (K:=F) (V:=C)
  rw [ZMod.card] at eq
  rw [←eq] at bound
  omega
end Green51ResidualPacking

#print axioms Green51ResidualPacking.seventeen
