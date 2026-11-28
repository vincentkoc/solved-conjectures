import Erdos478TetrahedralEdgeAction
import Erdos478TetrahedralSexticMean

/-! # Relative independence of the sixth factorial gap and the four lower root actions -/

namespace Erdos478.TetrahedralGap
open Polynomial Equiv Finset MulAction FirstCollision BinaryGap LowGapAction FrobeniusCounts
open RelativeGap QuinticLaw SplittingDensity
open scoped Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

omit [IsGalois ℚ K] in
theorem sixth_count_descends (sp : ((rationalGap 6).map (algebraMap ℚ K)).Splits) (g h : Aut K)
    (same : vertexAction K g=vertexAction K h) : fixedGap K 6 g=fixedGap K 6 h := by
  have acts := (vertex_eq_iff_edge K sp g h).mp same
  have eq : fixedBy (GapRoots K 6) g=fixedBy (GapRoots K 6) h := by
    ext x
    simp only [mem_fixedBy]
    have same_x : g • x=h • x := congrArg (fun π : Perm (GapRoots K 6) => π x) acts
    rw [same_x]
  unfold fixedGap fixedCount
  rw [eq]

/-- Every real-valued observable of the number of sixth-gap endpoints
factors independently of every observable of all the lower root permutations. -/
theorem sixth_independent (split : ∀ k, 2≤k → k≤6 → ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (W : Aut K → ℝ) (v : ℕ → ℝ) (stable : ∀ (n : LowerKernel K (short 5)) g, W (n.val*g)=W g) :
    uniform (Aut K) (fun g => W g*v (fixedGap K 6 g))=sexticMean v*uniform (Aut K) W := by
  classical
  have sp := split 6 (by decide) (by decide)
  have onto := vertex_surjective K (quartic_splits_of_sextic K sp)
  let V (π : Perm (Vertex K)) := v (fixedGap K 6 (onto π).choose)
  have lv (g : Aut K) : V (vertexAction K g)=v (fixedGap K 6 g) :=
    congrArg v (sixth_count_descends K sp _ g (onto (vertexAction K g)).choose_spec)
  have eq := quotient_independent _ (vertexAction K) (vertex_relative_surjective K split) W V stable
  have m := quotient_mean _ onto V
  simp_rw [lv] at eq m
  rw [← m,sextic_mean K sp v] at eq
  exact eq

def fiveLaw (a b c d e : ℕ → Bool) : ℝ := fourLaw a b c d*sexticMean (fun j => if e j then 1 else 0)

theorem joint_sextic_law (split : ∀ k, 2≤k → k≤6 → ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (a b c d e : ℕ → Bool) :
    uniform (Aut K) (fun g => if a (fixedGap K 2 g) && b (fixedGap K 3 g) && c (fixedGap K 4 g) &&
      d (fixedGap K 5 g) && e (fixedGap K 6 g) then 1 else 0)=fiveLaw a b c d e := by
  let W (g : Aut K) : ℝ := if a (fixedGap K 2 g) && b (fixedGap K 3 g) && c (fixedGap K 4 g) &&
    d (fixedGap K 5 g) then 1 else 0
  let v (j : ℕ) : ℝ := if e j then 1 else 0
  have stable (n : LowerKernel K (short 5)) (g : Aut K) : W (n.val*g)=W g := by
    simp only [W,stable_count K n g (show 2∈short 5 by decide),stable_count K n g (show 3∈short 5 by decide),
      stable_count K n g (show 4∈short 5 by decide),stable_count K n g (show 5∈short 5 by decide)]
  have eq := sixth_independent K split W v stable
  have prod (g : Aut K) : W g*v (fixedGap K 6 g) = if a (fixedGap K 2 g) && b (fixedGap K 3 g) &&
      c (fixedGap K 4 g) && d (fixedGap K 5 g) && e (fixedGap K 6 g) then 1 else 0 := by
    simp only [W,v,Bool.and_eq_true]
    split_ifs <;> simp_all
  simp_rw [prod] at eq
  rw [show uniform (Aut K) W=_ from joint_quintic_law K (fun k lo hi => split k lo (by omega)) a b c d] at eq
  exact eq.trans (mul_comm ..)

#print axioms sixth_count_descends
#print axioms sixth_independent
#print axioms fiveLaw
#print axioms joint_sextic_law
end
end Erdos478.TetrahedralGap
