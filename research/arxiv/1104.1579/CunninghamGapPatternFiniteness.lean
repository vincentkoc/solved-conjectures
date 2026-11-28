import CunninghamSquareGapComparison

/-! Finiteness of exceptional degrees with a bounded number of witness coefficients. -/

namespace CunninghamChain.GapLift
open Polynomial Finset

def samePair {ι : Type*} (n : ℕ) (x : ι → ℕ) (i j k l : ι ⊕ Fin 4) : Bool :=
  decide (positions n x i+(n+2-positions n x j)=positions n x k+(n+2-positions n x l))

/-- A degree permitting a witness with t slots which passes the reflected-product
test but is divisible by the endpoint in neither orientation. -/
def exceptional (b : ℚ) (t n : ℕ) : Prop :=
  ∃ (x : Fin t → ℕ) (a : Fin t → ℚ), (∀ i, x i ≤ n+2) ∧
    assemble (positions n x) (witness a)*assemble (fun i => n+2-positions n x i) (witness a) =
    assemble (positions n x) (endpoint (b^2))*assemble (fun i => n+2-positions n x i) (endpoint (b^2)) ∧
    ¬ ((1+tailPoly (b^2) n) ∣ assemble (positions n x) (witness a) ∨
      (1+tailPoly (b^2) n) ∣ assemble (fun i => n+2-positions n x i) (witness a))

/-- Two different exceptional degrees cannot give the same equality pattern
on pairs of indices. Coefficient values do not enter the pattern. -/
theorem exceptional_finite {b : ℚ} (hb : 1 < b) (t : ℕ) :
    {n | exceptional b t n}.Finite := by
  classical
  by_contra bad
  let E := {n : ℕ | exceptional b t n}
  have inf : E.Infinite := bad
  let : Infinite E := inf.to_subtype
  choose x a bounded eq miss using (fun i : E => i.property)
  let pattern (i : E) := samePair i.val (x i)
  obtain ⟨i,j,ne,match'⟩ := Finite.exists_ne_map_eq_of_infinite pattern
  have exclude (v w : E) (lt : v.val < w.val) (he : pattern v=pattern w) : False := by
    apply miss v
    apply square_comparison hb lt (x v) (x w) (bounded v) (bounded w) _ (a v) (eq v)
    intro i j k l h
    have rel := congrFun (congrFun (congrFun (congrFun he i) j) k) l
    change decide (_ = _) = decide (_ = _) at rel
    exact of_decide_eq_true ((congrArg id rel).symm.trans (decide_eq_true h))
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => ne (Subtype.ext e)) with lt|lt
  · exact exclude i j lt match'
  · exact exclude j i lt match'.symm

theorem bounded_exceptional_finite {b : ℚ} (hb : 1 < b) (W : ℕ) :
    {n | ∃ t ≤ W, exceptional b t n}.Finite := by
  apply ((Set.finite_Iic W).biUnion (fun t _ => exceptional_finite hb t)).subset
  rintro n ⟨t,ht,h⟩
  exact Set.mem_iUnion₂.mpr ⟨t,ht,h⟩

#print axioms exceptional_finite
#print axioms bounded_exceptional_finite

end CunninghamChain.GapLift
