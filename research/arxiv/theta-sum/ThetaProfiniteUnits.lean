import ThetaNaturalPrimeMeans
import Mathlib.Topology.Instances.ZMod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Group.SubmonoidClosure

/-! Haar measure on the inverse limit of the factorial unit groups. -/
namespace Arxiv.«2501.03234».ThetaProfiniteUnits
open MeasureTheory MeasureTheory.Measure Filter TopologicalSpace Set
open scoped Topology
noncomputable section

abbrev U (n : ℕ) := (ZMod n.factorial)ˣ
local instance (n : ℕ) : NeZero n.factorial := ⟨(Nat.factorial_pos _).ne'⟩

def restrict {m n : ℕ} (h : m ≤ n) : U n →* U m :=
  ZMod.unitsMap (Nat.factorial_dvd_factorial h)

private lemma restrict_trans {a b c : ℕ} (hab : a≤b) (hbc : b≤c) (u : U c) :
    restrict hab (restrict hbc u) = restrict (hab.trans hbc) u :=
  DFunLike.congr_fun (ZMod.unitsMap_comp _ _) u

def compatible : Subgroup ((n : ℕ) → U n) where
  carrier := {x | ∀ n, restrict (Nat.le_succ n) (x (n+1)) = x n}
  one_mem' n := map_one _
  mul_mem' := by
    intro x y hx hy n
    exact (map_mul _ _ _).trans (congrArg₂ (·*·) (hx n) (hy n))
  inv_mem' := by
    intro x hx n
    exact (map_inv _ _).trans (congrArg Inv.inv (hx n))

/-- The profinite unit group, using the cofinal moduli n!. -/
abbrev G := ↥compatible

private theorem closed_compatible : IsClosed (compatible : Set ((n : ℕ) → U n)) := by
  change IsClosed {x : (n : ℕ) → U n | ∀ n, restrict (Nat.le_succ n) (x (n+1)) = x n}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro n
  apply isClosed_eq _ (continuous_apply n)
  exact (continuous_of_discreteTopology : Continuous (restrict (Nat.le_succ n))).comp (continuous_apply _)

instance : CompactSpace G := isCompact_iff_compactSpace.mp closed_compatible.isCompact
instance : MeasurableSpace G := borel G
instance : BorelSpace G := ⟨rfl⟩

def projection (n : ℕ) : G →* U n where
  toFun x := x.val n
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_projection (n : ℕ) : Continuous (projection n) :=
  (continuous_apply n).comp continuous_subtype_val

theorem projection_restrict (x : G) {i j : ℕ} (h : i ≤ j) :
    restrict h (projection j x) = projection i x := by
  induction j, h using Nat.le_induction with
  | base => simp [restrict]
  | succ j hij ih =>
    rw [← restrict_trans hij (Nat.le_succ j),show restrict (Nat.le_succ j) (projection (j+1) x) =
      projection j x from x.property j,ih]

private def extend (n : ℕ) (u : U n) : (k : ℕ) → U k
  | 0 => restrict (Nat.zero_le n) u
  | k+1 => if h : k+1≤n then restrict h u
           else (ZMod.unitsMap_surjective (Nat.factorial_dvd_factorial (Nat.le_succ k))
             (extend n u k)).choose

private theorem extend_le (n : ℕ) (u : U n) {k : ℕ} (hk : k≤n) :
    extend n u k = restrict hk u := by
  cases k with
  | zero => rfl
  | succ k => simp [extend,hk]

theorem projection_surjective (n : ℕ) : Function.Surjective (projection n) := by
  intro u
  have hx : extend n u ∈ compatible := by
    intro k
    by_cases h : k+1≤n
    · rw [extend_le n u h,extend_le n u ((Nat.le_succ k).trans h),restrict_trans]
    · rw [extend, dif_neg h]
      exact (ZMod.unitsMap_surjective (Nat.factorial_dvd_factorial (Nat.le_succ k)) (extend n u k)).choose_spec
  refine ⟨⟨_,hx⟩,?_⟩
  change extend n u n = u
  rw [extend_le n u le_rfl]
  simp [restrict]

def haar : Measure G :=
  haarMeasure (⟨⟨univ,isCompact_univ⟩, by simp⟩ : PositiveCompacts G)

instance : IsProbabilityMeasure haar := ⟨haarMeasure_self⟩
instance : IsMulLeftInvariant haar := by unfold haar; infer_instance

open Finset ThetaConditionalRows ThetaPeriodMeans

/-- A function of one factorial residue lifted to the profinite unit group. -/
def cylinder (n : ℕ) (f : ℕ → ℝ) (x : G) : ℝ := f ((projection n x : ZMod n.factorial).val)

theorem continuous_cylinder (n : ℕ) (f : ℕ → ℝ) : Continuous (cylinder n f) :=
  (continuous_of_discreteTopology : Continuous (fun u : U n => f (u:ZMod n.factorial).val)).comp
    (continuous_projection n)

/-- Normalized Haar measure gives the uniform mean on every factorial unit group. -/
theorem integral_cylinder (n : ℕ) (f : ℕ → ℝ) :
    (∫ x, cylinder n f x ∂haar) = unitMean n.factorial f := by
  let F (v : U n) := f (v:ZMod n.factorial).val
  have hc (v : U n) : Continuous (fun x : G => F (v*projection n x)) :=
    (continuous_of_discreteTopology : Continuous (fun u : U n => F (v*u))).comp (continuous_projection n)
  have hi (v : U n) : (∫ x, F (v*projection n x) ∂haar) = ∫ x, cylinder n f x ∂haar := by
    obtain ⟨y,rfl⟩ := projection_surjective n v
    simp only [← map_mul]
    exact integral_mul_left_eq_self (cylinder n f) y
  have hs (x : G) : (∑ v : U n, F (v*projection n x)) = ∑ v : U n,F v :=
    Fintype.sum_bijective (fun v : U n => v*projection n x) (Equiv.mulRight _).bijective _ _ (fun _ => rfl)
  have H := integral_finsetSum (μ:=haar) univ (f:=fun v (x : G) => F (v*projection n x))
    (fun v _ => (hc v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  simp only [hs,hi,integral_const, probReal_univ,one_smul,
    sum_const,card_univ,nsmul_eq_mul,ZMod.card_units_eq_totient] at H
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.factorial_pos _)).ne')).mpr
  simpa only [F,mul_comm] using H.symm

theorem cylinder_lift {i j : ℕ} (h : i≤j) {f : ℕ → ℝ} (hf : OnMod i.factorial f) (x : G) :
    cylinder i f x = cylinder j f x := by
  unfold cylinder
  rw [← projection_restrict x h]
  have hv : ((restrict h (projection j x):ZMod i.factorial).val) =
      (projection j x:ZMod j.factorial).val%i.factorial := by
    rw [restrict,ZMod.unitsMap_val,← ZMod.natCast_zmod_val (projection j x:ZMod j.factorial),
      ZMod.cast_natCast (Nat.factorial_dvd_factorial h),ZMod.val_natCast,ZMod.natCast_zmod_val]
  rw [hv,hf]

#print axioms projection_surjective
#print axioms integral_cylinder
#print axioms cylinder_lift

end
end Arxiv.«2501.03234».ThetaProfiniteUnits
