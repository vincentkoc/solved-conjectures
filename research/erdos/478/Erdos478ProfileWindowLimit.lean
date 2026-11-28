import Erdos478WitnessDensityDichotomy
import Erdos478ShortFreeWindows

/-! # Long factorial collisions conditional on any earlier endpoint-count event -/

namespace Erdos478.LocalWitness
open Polynomial Finset Filter Topology BinaryGap FrobeniusCounts GapSieve GapDensity
open SplittingDensity FrobeniusBands BandWeights FirstCollision
open scoped Classical
noncomputable section

def profileWindow (X : ℕ) (b : Finset ℕ) (P : (b → ℕ) → Prop) (s : Finset Nat.Primes) (θ : ℝ) :=
  fraction X (fun p => realizes b P p ∧ θ≤((GapSieve.hits s p).card:ℝ) ∧
    ((Ico 1 p).image (fun i => i.factorial%p)).card+(GapSieve.hits s p).card≤p-1) /
    fraction X (realizes b P)

/-- The lower tail inequality retains its full strength after restriction to
any positive-mass event on the endpoint counts of smaller lengths. -/
theorem profile_limit (pit : DegreeOnePrimeIdealTheorem) (b : Finset ℕ) (hb : ∀ k∈b, 2≤k)
    (P : (b → ℕ) → Prop) (pos : 0<density b P) (s : Finset Nat.Primes)
    (below : ∀ k∈b, ∀ i∈s, k < i.val) (good : ∀ i∈s, broad i.val ∧ 3 < i.val) (θ : ℝ) :
    ∃ e : ℝ, Tendsto (fun X => profileWindow X b P s θ) atTop (𝓝 e) ∧
      ∀ z : ℝ, 0<z → z≤1 → 1-Real.exp (s.card*Real.log ((1+z)/2)-θ*Real.log z)≤e := by
  let T := combined b s
  let K := FieldOf T
  let : Normal ℚ K := SplittingField.instNormal _
  have hT (k) (hk : k∈T) : 2≤k := by
    rcases mem_union.mp hk with h|h
    · exact hb k h
    · obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact i.prop.two_le
  let Z (a : T → ℕ) := P (fun i => a ⟨i.val,mem_union_left _ i.prop⟩)
  let E (a : T → ℕ) := Z a ∧ θ≤((observed b s a).card:ℝ)
  let W (a : b → ℕ) : ℝ := if P a then 1 else 0
  have mass : density b P=density T Z := density_congr pit hb hT P Z (fun _ _ => Iff.rfl)
  refine ⟨density T E/density b P,?_,?_⟩
  · obtain ⟨B,hB⟩ := GapSieve.hits_le_deficit s
    have lim := density_limit pit T hT E (fun p => realizes b P p ∧ θ≤((GapSieve.hits s p).card:ℝ) ∧
      ((Ico 1 p).image (fun i => i.factorial%p)).card+(GapSieve.hits s p).card≤p-1) B (by
      intro p hp hpr
      have h := hB p hp hpr
      unfold MeanDeficit.deficit at h
      have cert : ((Ico 1 p).image (fun i => i.factorial%p)).card+(GapSieve.hits s p).card≤p-1 := by omega
      simp only [E,Z,realizes,cert,and_true]
      rw [observed_endpoints b s p])
    exact lim.div (density_limit pit b hb P (realizes b P) 0 (fun _ _ _ => Iff.rfl)) pos.ne'
  · intro z hz hz'
    apply (le_div_iff₀ pos).mpr
    rw [mass]
    have res := weighted_threshold K b (fun k hk => (by decide : 0<2).trans_le (hb k hk)) s below good
      (fun k hk => gap_splits (fun k h => (by decide : 0<2).trans_le (hT k h)) hk) W
      (fun a => by dsimp [W]; split_ifs <;> norm_num) θ hz hz'
    apply res.trans_eq
    apply congrArg (uniform (Aut K))
    funext g
    let a (i : T) := fixedGap K i.val g
    change (if θ≤((ConditionalGaps.hits K s g).card:ℝ) then (if Z a then (1:ℝ) else 0) else 0)=
      (@ite ℝ (Z a ∧ θ≤((observed b s a).card:ℝ)) (Classical.propDecidable _) 1 0)
    have eq : observed b s a=ConditionalGaps.hits K s g := observed_fixed K b s g
    rw [eq]
    by_cases hit : θ≤((ConditionalGaps.hits K s g).card:ℝ) <;> simp [hit]

#print axioms profileWindow
#print axioms profile_limit
end
end Erdos478.LocalWitness
