import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Tactic

/-!
# Real roots of factorial gap polynomials

For n ≥ 5 the product of n consecutive linear factors has absolute
value greater than one at every half-integer. Between two neighboring
half-integers straddling a factor the signs are opposite. Each resulting
open interval therefore contains a root of the product minus one.
-/

namespace Erdos478.GapReality
open Polynomial Set Finset
noncomputable section

private theorem five_eval (x : ℝ) : (descPochhammer ℝ 5).eval x =
    x*(x-1)*(x-2)*(x-3)*(x-4) := by
  norm_num [descPochhammer_succ_eval,descPochhammer]
  ring

private theorem five_half (t : ℤ) : 1 < |(descPochhammer ℝ 5).eval ((t:ℝ)+1/2)| := by
  rw [five_eval]
  by_cases lo : t≤ -2
  · have h : (t:ℝ)≤ -2 := by exact_mod_cast lo
    simp only [abs_mul]
    repeat' apply one_lt_mul_of_lt_of_le
    all_goals first | apply lt_abs.mpr; right; linarith | apply le_abs.mpr; right; linarith
  by_cases hi : 5≤t
  · have h : (5:ℝ)≤t := by exact_mod_cast hi
    simp only [abs_mul]
    repeat' apply one_lt_mul_of_lt_of_le
    all_goals first | apply lt_abs.mpr; left; linarith | apply le_abs.mpr; left; linarith
  have h₁ : -1≤t := by omega
  have h₂ : t≤4 := by omega
  interval_cases t <;> norm_num

private theorem left_eval (n : ℕ) (x : ℝ) : (descPochhammer ℝ (n+1)).eval x =
    x*(descPochhammer ℝ n).eval (x-1) := by
  rw [descPochhammer_succ_left]
  simp

theorem half_integer_magnitude {n : ℕ} (hn : 5≤n) (t : ℤ) :
    1 < |(descPochhammer ℝ n).eval ((t:ℝ)+1/2)| := by
  induction n, hn using Nat.le_induction generalizing t with
  | base => exact five_half t
  | succ n hn ih =>
    let x : ℝ := (t:ℝ)+1/2
    have hn' : (5:ℝ)≤n := by exact_mod_cast hn
    by_cases h : 1≤|x-n|
    · rw [descPochhammer_succ_eval,abs_mul]
      exact one_lt_mul_of_lt_of_le (ih t) h
    · have hx : 1≤|x| := le_abs.mpr (Or.inl (by
        have := abs_lt.mp (lt_of_not_ge h)
        linarith))
      rw [left_eval,abs_mul]
      apply one_lt_mul_of_le_of_lt hx
      simpa only [Int.cast_sub,Int.cast_one,show (t:ℝ)-1+1/2=t+1/2-1 by ring] using ih (t-1)

/-- One real root in each of the n unit intervals centered at the old
zeros 0,1,…,n−1. The half-integer endpoints are excluded. -/
theorem root_in_cell {n : ℕ} (hn : 5≤n) (j : Fin n) :
    ∃ r : ℝ, (j.val:ℝ)-1/2<r ∧ r<(j.val:ℝ)+1/2 ∧
      (descPochhammer ℝ n).eval r=1 := by
  let x : ℝ := j.val-1/2
  let y : ℝ := j.val+1/2
  let P := descPochhammer ℝ n
  have hL : 1 < |P.eval x| := by
    have hl := half_integer_magnitude hn ((j.val:ℤ)-1)
    simpa only [P,x,Int.cast_sub,Int.cast_natCast,Int.cast_one,
      show (j.val:ℝ)-1+1/2=j.val-1/2 by ring] using hl
  have hR : 1 < |P.eval y| := by simpa [P,y] using half_integer_magnitude hn (j.val:ℤ)
  have hxy : y-1=x := by dsimp [x,y]; ring
  have rel : P.eval y*(y-n)=y*P.eval x := by
    rw [← descPochhammer_succ_eval,left_eval,hxy]
  have hpos : 0<y := by dsimp [y]; positivity
  have hneg : y-n<0 := by
    have hn' : (j.val:ℝ)+1≤n := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    dsimp [y]
    linarith
  have ha : x≤y := by dsimp [x,y]; linarith
  have cross : 1∈Ioo (P.eval x) (P.eval y) ∨ 1∈Ioo (P.eval y) (P.eval x) := by
    rcases lt_abs.mp hL with h₁|h₁ <;> rcases lt_abs.mp hR with h₂|h₂
    · have := mul_neg_of_pos_of_neg (by linarith : 0<P.eval y) hneg
      have := mul_pos hpos (by linarith : 0<P.eval x)
      linarith
    · exact Or.inr ⟨by linarith,h₁⟩
    · exact Or.inl ⟨by linarith,h₂⟩
    · have := mul_pos_of_neg_of_neg (by linarith : P.eval y<0) hneg
      have := mul_neg_of_pos_of_neg hpos (by linarith : P.eval x<0)
      linarith
  have hc := P.continuous.continuousOn (s:=Icc x y)
  have H := cross.elim (fun h => intermediate_value_Ioo ha hc h) (fun h => intermediate_value_Ioo' ha hc h)
  obtain ⟨r,hr,he⟩ := H
  exact ⟨r,hr.1,hr.2,he⟩

/-- All n roots are real. The proof counts the disjoint open cells,
so the split polynomial also has n distinct roots. -/
theorem splits_real_gap {n : ℕ} (hn : 5≤n) :
    (descPochhammer ℝ n-1).Splits ∧ (descPochhammer ℝ n-1).roots.toFinset.card=n := by
  classical
  let P := descPochhammer ℝ n-1
  have H : (descPochhammer ℝ n).IsMonicOfDegree n :=
    ⟨descPochhammer_natDegree ℝ n,monic_descPochhammer ℝ n⟩
  have hP : P.IsMonicOfDegree n := by
    simpa only [P,sub_eq_add_neg] using H.add_right (q:=-(1:ℝ[X])) (by simpa using (show 0<n by omega))
  choose r hr using root_in_cell hn
  have inc : StrictMono r := by
    intro i j hij
    have ij : (i.val:ℝ)+1≤j.val := by exact_mod_cast (show i.val+1≤j.val from hij)
    linarith [(hr i).2.1,(hr j).1]
  have sub : Finset.univ.image r⊆P.roots.toFinset := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := mem_image.mp hx
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hP.monic.ne_zero).mpr
    simp [P,IsRoot,(hr j).2.2]
  have hle := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inc.injective,Finset.card_univ,Fintype.card_fin] at hle
  have h₁ := Multiset.toFinset_card_le P.roots
  have h₂ := card_roots' P
  rw [hP.natDegree_eq] at h₂
  exact ⟨splits_iff_card_roots.mpr (by change P.roots.card=P.natDegree; rw [hP.natDegree_eq]; omega),
    by change P.roots.toFinset.card=n; omega⟩

#print axioms splits_real_gap
#print axioms half_integer_magnitude
#print axioms root_in_cell
end
end Erdos478.GapReality
