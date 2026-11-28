import Erdos478SexticResolvent
import Mathlib.Data.Finset.Card

/-!
# Root counts for the sixth factorial gap over a field

Roots in the coordinate `s=2*x-5` occur in opposite pairs. Once two
different pairs are present the third pair is supplied by `17/(s*t)`.
-/

namespace Erdos478.SexticGap
open Polynomial Finset
noncomputable section
open scoped Classical

private theorem remaining_root {K : Type*} [Field K] {u v : K}
    (hu : (cub K).toPoly.eval u=0) (hv : (cub K).toPoly.eval v=0) (hne : u≠v) :
    ∃ w : K, u*v*w=17^2 ∧
      (∀ z : K, (cub K).toPoly.eval z=0 ↔ z=u ∨ z=v ∨ z=w) ∧
      ((u-v)*(u-w)*(v-w))^2=64^2*1957 := by
  rw [cub_eval] at hu hv
  let w := 35-u-v
  have hs : (u-v)*(u^2+u*v+v^2-35*(u+v)+259)=0 := by linear_combination hu-hv
  have h := (mul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr hne)
  have h₁ : u+v+w=35 := by dsimp [w]; ring
  have h₂ : u*v+u*w+v*w=259 := by dsimp [w]; linear_combination -h
  have h₃ : u*v*w=17^2 := by dsimp [w]; linear_combination hu-u*h
  refine ⟨w,h₃,?_,?_⟩
  · intro z
    rw [cub_eval,show z^3-35*z^2+259*z-289=(z-u)*(z-v)*(z-w) by
      linear_combination z^2*h₁-z*h₂+h₃]
    simp [sub_eq_zero,or_assoc]
  · calc
      _ = (Cubic.mk 1 (-(u+v+w)) (u*v+u*w+v*w) (-(u*v*w))).discr := by
        simp only [Cubic.discr]; ring
      _ = _ := by rw [h₁,h₂,h₃]; norm_num [Cubic.discr]

private def pair {K : Type*} [Field K] (x : K) : Finset K := {x,-x}

private theorem mem_pair {K : Type*} [Field K] {x y : K} : x∈pair y ↔ x^2=y^2 := by
  simp [pair,sq_eq_sq_iff_eq_or_eq_neg]

private theorem card_pair {K : Type*} [Field K] {x : K} (h₂ : (2:K)≠0) (hx : x≠0) :
    (pair x).card=2 := by
  have hn : x≠ -x := by
    intro h
    exact (mul_ne_zero h₂ hx) (by linear_combination h)
  simp [pair,hn]

private theorem disjoint_pair {K : Type*} [Field K] {x y : K} (h : x^2≠y^2) :
    Disjoint (pair x) (pair y) :=
  disjoint_left.mpr fun _ hx hy => h ((mem_pair.mp hx).symm.trans (mem_pair.mp hy))

/-- This finite-set formulation counts distinct roots in arbitrary characteristic
away from the primes dividing twice seventeen and the cubic discriminant. -/
theorem coordinate_counts {K : Type*} [Field K] (S : Finset K)
    (hS : ∀ x : K, x∈S ↔ (cub K).toPoly.eval (x^2)=0)
    (h₂ : (2:K)≠0) (h₁₇ : (17:K)≠0) (hdisc : (1957:K)≠0) :
    S.card=0 ∨ S.card=2 ∨ S.card=6 := by
  classical
  by_cases h₀ : S=∅
  · exact Or.inl (by simp [h₀])
  obtain ⟨a,ha⟩ := nonempty_iff_ne_empty.mpr h₀
  have nozero {x : K} (hx : x∈S) : x≠0 := by
    rintro rfl
    have he := (hS _).mp hx
    have h289 : (289:K)=17^2 := by norm_num
    simp only [cub_eval,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),mul_zero,
      sub_zero,add_zero,zero_sub,neg_eq_zero] at he
    exact pow_ne_zero 2 h₁₇ (h289 ▸ he)
  by_cases hall : ∀ b∈S, b^2=a^2
  · right; left
    have he : S=pair a := by
      ext b
      rw [mem_pair]
      exact ⟨hall b,fun hb => (hS b).mpr (hb ▸ (hS a).mp ha)⟩
    rw [he,card_pair h₂ (nozero ha)]
  push Not at hall
  obtain ⟨b,hb,hba⟩ := hall
  obtain ⟨w,hprod,hclass,hdis⟩ := remaining_root ((hS a).mp ha) ((hS b).mp hb) (Ne.symm hba)
  let c := 17/(a*b)
  have hc : c^2=w := by
    rw [show c=17/(a*b) from rfl,div_pow,div_eq_iff (pow_ne_zero 2 (mul_ne_zero (nozero ha) (nozero hb))),mul_pow]
    linear_combination -hprod
  have h64 : (64:K)≠0 := by
    rw [show (64:K)=2^6 by norm_num]
    exact pow_ne_zero _ h₂
  have hnd : (a^2-b^2)*(a^2-w)*(b^2-w)≠0 := by
    intro h
    rw [h,zero_pow (by decide : 2≠0)] at hdis
    exact mul_ne_zero (pow_ne_zero _ h64) hdisc hdis.symm
  have hac : a^2≠c^2 := by
    rw [hc]; intro h; apply hnd; rw [h,sub_self,mul_zero,zero_mul]
  have hbc : b^2≠c^2 := by
    rw [hc]; intro h; apply hnd; rw [h,sub_self,mul_zero]
  have hfin : S=pair a ∪ pair b ∪ pair c := by
    ext x
    rw [hS,hclass,mem_union,mem_union,mem_pair,mem_pair,mem_pair,hc,or_assoc]
  right; right
  rw [hfin,card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨disjoint_pair hac,disjoint_pair hbc⟩),
    card_union_of_disjoint (disjoint_pair (Ne.symm hba)),card_pair h₂ (nozero ha),
    card_pair h₂ (nozero hb),card_pair h₂ (div_ne_zero h₁₇ (mul_ne_zero (nozero ha) (nozero hb)))]

#print axioms coordinate_counts
end
end Erdos478.SexticGap
