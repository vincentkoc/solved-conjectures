import Erdos478LeastPrimeCollision
import Erdos478ConditionalHitThreshold
import Erdos478TiltedHitWindows

/-! # Long collision windows within the primes having no short collision -/

namespace Erdos478.FirstCollision
open Polynomial Finset Filter Topology BinaryGap FrobeniusCounts GapSieve GapDensity
open SplittingDensity FrobeniusBands BandWeights
open scoped Classical
noncomputable section

def observed (b : Finset ℕ) (s : Finset Nat.Primes) (a : combined b s → ℕ) :=
  (s.attach.filter (fun i => 0<a ⟨i.val.val,mem_union_right b (mem_image_of_mem _ i.prop)⟩)).map
    (Function.Embedding.subtype _)

theorem observed_endpoints (b : Finset ℕ) (s : Finset Nat.Primes) (p : ℕ) :
    observed b s (fun i => (endpoints i.val p).card)=GapSieve.hits s p := by
  ext i
  simp [observed,GapSieve.hits,ConditionalGaps.hasGap_iff,and_comm]

theorem observed_fixed (K : Type*) [Field K] [Algebra ℚ K] (b : Finset ℕ) (s : Finset Nat.Primes) (g : Aut K) :
    observed b s (fun i => fixedGap K i.val g)=ConditionalGaps.hits K s g := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
    exact mem_filter.mpr ⟨j.prop,(mem_filter.mp hj).2⟩
  · intro hi
    obtain ⟨hs,hpos⟩ := mem_filter.mp hi
    exact mem_map.mpr ⟨⟨i,hs⟩,mem_filter.mpr ⟨mem_attach _ _,hpos⟩,rfl⟩

/-- Fraction of the short-collision-free primes that meet a prescribed count
of longer lengths. The image-loss certificate uses the canonical factorial interval. -/
def relativeWindow (X J : ℕ) (s : Finset Nat.Primes) (θ : ℝ) :=
  fraction X (fun p => NoShort p J ∧ θ≤((GapSieve.hits s p).card:ℝ) ∧
    ((Ico 1 p).image (fun i => i.factorial%p)).card+(GapSieve.hits s p).card≤p-1) /
    fraction X (fun p => NoShort p J)

theorem relative_window_limit (pit : DegreeOnePrimeIdealTheorem) (J : ℕ) (s : Finset Nat.Primes)
    (hi : ∀ i∈s, J < i.val ∧ broad i.val ∧ 3 < i.val) (θ : ℝ) :
    ∃ e : ℝ, Tendsto (fun X => relativeWindow X J s θ) atTop (𝓝 e) ∧
      ∀ z : ℝ, 0<z → z≤1 → 1-Real.exp (s.card*Real.log ((1+z)/2)-θ*Real.log z)≤e := by
  let b := short J
  let T := combined b s
  let K := FieldOf T
  let : Normal ℚ K := SplittingField.instNormal _
  have hT (k) (hk : k∈T) : 2≤k := by
    rcases mem_union.mp hk with h|h
    · exact (mem_Icc.mp h).1
    · obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact i.prop.two_le
  let Z (a : T → ℕ) := zeroCounts (s:=b) (fun i => a ⟨i.val,mem_union_left _ i.prop⟩)
  let E (a : T → ℕ) := Z a ∧ θ≤((observed b s a).card:ℝ)
  let W (a : b → ℕ) : ℝ := if zeroCounts a then 1 else 0
  have mass : survival J=density T Z := density_congr pit (fun _ hk => (mem_Icc.mp hk).1) hT
    zeroCounts Z (fun _ _ => Iff.rfl)
  refine ⟨density T E/survival J,?_,?_⟩
  · obtain ⟨B,hB⟩ := GapSieve.hits_le_deficit s
    have lim := density_limit pit T hT E (fun p => NoShort p J ∧ θ≤((GapSieve.hits s p).card:ℝ) ∧
      ((Ico 1 p).image (fun i => i.factorial%p)).card+(GapSieve.hits s p).card≤p-1) B (by
      intro p hp hpr
      have h := hB p hp hpr
      unfold MeanDeficit.deficit at h
      have cert : ((Ico 1 p).image (fun i => i.factorial%p)).card+(GapSieve.hits s p).card≤p-1 := by omega
      simp only [E,Z,cert,and_true,noShort_iff hpr]
      rw [observed_endpoints b s p])
    exact lim.div (survival_limit pit J) (survival_pos J).ne'
  · intro z hz hz'
    apply (le_div_iff₀ (survival_pos J)).mpr
    rw [mass]
    have res := weighted_threshold K b (fun k hk => (by decide : 0<2).trans_le (mem_Icc.mp hk).1) s
      (fun k hk i hi' => (mem_Icc.mp hk).2.trans_lt (hi i hi').1) (fun i h => (hi i h).2)
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

/-- The short-free condition may become very rare with K. Its mass cancels
before the exponential bound, and the prime cutoff X may depend on K. -/
theorem relative_window_of_inputs (pit : DegreeOnePrimeIdealTheorem) (input : countingInput broad (1/3))
    {H : ℕ → ℕ} {L b z A : ℝ} (hL : 1<L) (hw : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L))
    (hz : 0<z) (hz₁ : z≤1) (hA : A<b*Real.log z-(L-1)/3*Real.log ((1+z)/2)) :
    ∀ᶠ K : ℕ in atTop, ∀ᶠ X : ℕ in atTop, 1-Real.exp (-A*K/Real.log K)<
      relativeWindow X K (family K (H K)) (b*K/Real.log K) := by
  filter_upwards [ConditionalGaps.window_exponent input hL hw hA,eventually_ge_atTop 3] with K hr hK
  obtain ⟨e,lim,low⟩ := relative_window_limit pit K (family K (H K)) (fun i hi => by
    obtain ⟨lo,_,hb⟩ := family_mem.mp hi
    exact ⟨lo,hb,by omega⟩) (b*K/Real.log K)
  exact lim.eventually_const_lt ((sub_lt_sub_left (Real.exp_lt_exp.mpr hr) 1).trans_le (low z hz hz₁))

#print axioms observed
#print axioms observed_endpoints
#print axioms observed_fixed
#print axioms relativeWindow
#print axioms relative_window_limit
#print axioms relative_window_of_inputs
end
end Erdos478.FirstCollision
