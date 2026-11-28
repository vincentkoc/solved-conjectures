import research.arxiv.«2211.10788».LucasFibonacciIndexForms

/-! Reductions of the upper Hosoya index forms at the ramified prime and the prime of the initial norm. -/

namespace Arxiv.«2211.10788»

private theorem upper_mod_eleven (r : ℕ) : (lucasFibonacciSum r : ZMod 11) = 4^r := by
  induction r using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more r h₀ h₁ =>
    rw [lucas_fibonacci_sum_recurrence,Nat.cast_add,h₀,h₁,pow_succ,pow_succ]
    have h : (4:ZMod 11)^2=4+1 := by decide
    linear_combination -(4^r : ZMod 11)*h

/-- The norm-eleven prime leaves just one linear factor of multiplicity d. -/
theorem upperIndexForm_mod_eleven (x y : ZMod 11) (r d : ℕ) :
    upperIndexForm x y d r = 4^r*(x+4*y)^d := by
  induction d generalizing r with
  | zero => simp [upperIndexForm,upper_mod_eleven]
  | succ d ih => rw [upperIndexForm,ih,ih,pow_succ (4:ZMod 11),pow_succ]; ring

private theorem upper_difference_five (r : ℕ) :
    (lucasFibonacciSum (r+1) : ZMod 5) = 3*lucasFibonacciSum r + 3^r := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show r+1+1=r+2 by omega,lucas_fibonacci_sum_recurrence,Nat.cast_add,ih,pow_succ]
    have h : (3:ZMod 5)^2=3+1 := by decide
    have h' : (3:ZMod 5)+3=1 := by decide
    linear_combination -(lucasFibonacciSum r : ZMod 5)*h - (3^r : ZMod 5)*h'

/-- At five, the form of degree d+1 is a dth power of one line times a linear form. -/
theorem upperIndexForm_mod_five (x y : ZMod 5) (r d : ℕ) :
    upperIndexForm x y (d+1) r = (x+3*y)^d*
      ((lucasFibonacciSum r : ZMod 5)*(x+3*y)+(d+1:ℕ)*3^r*y) := by
  induction d generalizing r with
  | zero =>
    rw [upperIndexForm,upperIndexForm,upperIndexForm,upper_difference_five]
    push_cast
    ring
  | succ d ih =>
    rw [upperIndexForm, ih, ih,upper_difference_five,pow_succ (3:ZMod 5),pow_succ (x+3*y)]
    push_cast
    ring

#print axioms upperIndexForm_mod_eleven
#print axioms upperIndexForm_mod_five

/-- The affine chart and its point at infinity. -/
def upperIndexChart {p : ℕ} : Option (ZMod p) → ZMod p × ZMod p
  | none => (1,0)
  | some x => (x,1)

/-- Number of roots in the affine chart (x,1) together with the point (1,0). -/
def upperProjectiveRootCount (p r d : ℕ) [NeZero p] : ℕ :=
  (Finset.univ.filter fun z : Option (ZMod p) =>
    upperIndexForm (upperIndexChart z).1 (upperIndexChart z).2 d r=0).card

/-- Exactly one projective root modulo eleven at every positive degree. -/
theorem upperProjectiveRootCount_eleven (r d : ℕ) (hd : 0<d) :
    upperProjectiveRootCount 11 r d = 1 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h : (4:ZMod 11)^r ≠ 0 := pow_ne_zero _ (by decide)
  unfold upperProjectiveRootCount
  simp only [upperIndexForm_mod_eleven,mul_eq_zero,h,false_or,pow_eq_zero_iff hd.ne']
  decide

/-- At the ramified prime the root count can rise to all six projective points. -/
theorem upperProjectiveRootCount_five (r d : ℕ) :
    upperProjectiveRootCount 5 r (d+1) =
      if d=0 then 1 else if 5 ∣ d+1 then (if 5 ∣ lucasFibonacciSum r then 6 else 1) else 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let u : ZMod 5 := lucasFibonacciSum r
  let c : ZMod 5 := (d+1:ℕ)*3^r
  have hc : c=0 ↔ 5 ∣ d+1 := by
    simp only [c,mul_eq_zero,pow_ne_zero r (by decide : (3:ZMod 5)≠0),or_false]
    exact ZMod.natCast_eq_zero_iff ..
  have hu : u=0 ↔ 5 ∣ lucasFibonacciSum r := ZMod.natCast_eq_zero_iff ..
  unfold upperProjectiveRootCount
  simp only [upperIndexForm_mod_five]
  change (Finset.univ.filter fun z : Option (ZMod 5) =>
    ((upperIndexChart z).1+3*(upperIndexChart z).2)^d*(u*((upperIndexChart z).1+3*(upperIndexChart z).2)+c*(upperIndexChart z).2)=0).card=_
  simp only [←hc,←hu]
  by_cases hd : d=0
  · simp only [hd,pow_zero,one_mul]
    have count (u c : ZMod 5) (hn : c≠0) :
        (Finset.univ.filter fun z : Option (ZMod 5) =>
          u*((upperIndexChart z).1+3*(upperIndexChart z).2)+c*(upperIndexChart z).2=0).card=1 := by revert u c; decide
    exact count u c (hc.not.mpr (by simp [hd]))
  · simp only [if_neg hd,mul_eq_zero,pow_eq_zero_iff hd]
    have count (u c : ZMod 5) :
        (Finset.univ.filter fun z : Option (ZMod 5) =>
          (upperIndexChart z).1+3*(upperIndexChart z).2=0 ∨ u*((upperIndexChart z).1+3*(upperIndexChart z).2)+c*(upperIndexChart z).2=0).card=
          if c=0 then (if u=0 then 6 else 1) else 2 := by revert u c; decide
    exact count u c

#print axioms upperProjectiveRootCount_eleven
#print axioms upperProjectiveRootCount_five

end Arxiv.«2211.10788»
