import Mathlib.Tactic

/-! A finite certificate for centered color counts in the candidate of order 238. -/

namespace Green33GraphHistogram

/-- The p-entries are the seven ordered convolution counts. The b-entries
are the necessary contributions from nonzero rows when the total color is zero. -/
def excluded (a b c d e f g : ℕ) : Bool :=
  let p0 := a*a + 2*(b*g+c*f+d*e)
  let p1 := e*e + 2*(a*b+c*g+d*f)
  let p2 := b*b + 2*(a*c+d*g+e*f)
  let p3 := f*f + 2*(a*d+b*c+e*g)
  let p4 := c*c + 2*(a*e+b*d+f*g)
  let p5 := g*g + 2*(a*f+b*e+c*d)
  let p6 := d*d + 2*(a*g+b*f+c*e)
  let b0 := 32+2*a+a
  let b1 := 32+2*g+e
  let b2 := 32+2*f+b
  let b3 := 32+2*e+f
  let b4 := 32+2*d+c
  let b5 := 32+2*c+g
  let b6 := 32+2*b+d
  decide (3 < (b0-p0)+(b1-p1)+(b2-p2)+(b3-p3)+(b4-p4)+(b5-p5)+(b6-p6) ∨
    p0+3 < b0+14 ∧ p1+3 < b1+14 ∧ p2+3 < b2+14 ∧ p3+3 < b3+14 ∧ p4+3 < b4+14 ∧ p5+3 < b5+14 ∧ p6+3 < b6+14)

private def allUpTo (ok : ℕ → Bool) : ℕ → Bool
  | 0 => ok 0
  | n+1 => ok (n+1) && allUpTo ok n

private lemma from_all {ok : ℕ → Bool} {n k : ℕ} (h : allUpTo ok n=true) (hk : k≤n) :
    ok k=true := by
  induction n with
  | zero => simpa [allUpTo,Nat.eq_zero_of_le_zero hk] using h
  | succ n ih =>
    rw [allUpTo,Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le hk with rfl | hk
    · exact h.1
    · exact ih h.2 (by omega)

private def slice (a : ℕ) : Bool :=
  allUpTo (fun b =>
    allUpTo (fun c =>
      allUpTo (fun d =>
        allUpTo (fun e =>
          allUpTo (fun f => excluded a b c d e f (17-(a+b+c+d+e+f)))
            (17-(a+b+c+d+e))) (17-(a+b+c+d))) (17-(a+b+c))) (17-(a+b))) (17-a)

set_option maxHeartbeats 0 in
private theorem checked (a : Fin 18) : slice a=true := by
  fin_cases a <;> decide +kernel

/-- All seven-part nonnegative compositions of 17 are excluded. -/
theorem impossible (a b c d e f g : ℕ) (h : a+b+c+d+e+f+g=17) :
    excluded a b c d e f g=true := by
  have h₀ := checked ⟨a,by omega⟩
  change slice a=true at h₀
  obtain h₁ := from_all (k := b) h₀ (by omega)
  obtain h₂ := from_all (k := c) h₁ (by omega)
  obtain h₃ := from_all (k := d) h₂ (by omega)
  obtain h₄ := from_all (k := e) h₃ (by omega)
  obtain h₅ := from_all (k := f) h₄ (by omega)
  simpa only [show 17-(a+b+c+d+e+f)=g by omega] using h₅

#print axioms impossible

end Green33GraphHistogram
