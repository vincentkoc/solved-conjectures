import Erdos478LowerDegreeActions
import Erdos478FairGapDomination

/-! # A weighted generating function after prescribed earlier factorial root counts -/

namespace Erdos478.FirstCollision
open Polynomial Equiv Finset BinaryGap FrobeniusCounts
open scoped Classical
noncomputable section

def combined (b : Finset ℕ) (s : Finset Nat.Primes) := b ∪ s.image Subtype.val

variable (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [Normal ℚ K]

/-- For every nonnegative weight on a finite batch of earlier counts, the weighted
generating function has the same upper factor per new eligible length. -/
theorem weighted_power (b : Finset ℕ) (bp : ∀ k∈b, 0<k) (s : Finset Nat.Primes)
    (below : ∀ k∈b, ∀ i∈s, k < i.val) (good : ∀ i∈s, broad i.val ∧ 3 < i.val)
    (split : ∀ k∈combined b s, ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (W : (b → ℕ) → ℝ) (hn : ∀ a, 0≤W a) {z : ℝ} (hz : 0≤z) (hz' : z≤1) :
    uniform (Aut K) (fun g => W (fun i => fixedGap K i.val g)*z^(ConditionalGaps.hits K s g).card) ≤
      uniform (Aut K) (fun g => W (fun i => fixedGap K i.val g))*((1+z)/2)^s.card := by
  classical
  let w (g : Aut K) := W (fun i => fixedGap K i.val g)
  induction s using Finset.induction_on_max_value (fun i : Nat.Primes => i.val) with
  | empty => simp [ConditionalGaps.hits]
  | insert l s hl top ih =>
    let old := combined b s
    have sub : old⊆combined b (insert l s) := union_subset_union_right (image_subset_image (subset_insert _ _))
    have lower (k : ℕ) (hk : k∈old) : 0<k ∧ k<l.val := by
      rcases mem_union.mp hk with hb | hs
      · exact ⟨bp k hb,below k hb l (mem_insert_self ..)⟩
      · obtain ⟨i,hi,rfl⟩ := mem_image.mp hs
        exact ⟨i.prop.pos,(top i hi).lt_of_ne (fun he => hl (Subtype.ext he ▸ hi))⟩
    have sp (k) (hk : k∈insert l.val old) : ((rationalGap k).map (algebraMap ℚ K)).Splits := by
      rcases mem_insert.mp hk with rfl|h
      · exact split _ (mem_union_right _ (mem_image_of_mem _ (mem_insert_self ..)))
      · exact split k (sub h)
    let u (g : Aut K) := w g*z^(ConditionalGaps.hits K s g).card
    have un (g) : 0≤u g := mul_nonneg (hn _) (pow_nonneg hz _)
    have st (n : LowerKernel K old) (g : Aut K) : u (n.val*g)=u g := by
      have we : w (n.val*g)=w g := congrArg W (funext fun i => stable_count K n g (mem_union_left _ i.prop))
      have he : ConditionalGaps.hits K s (n.val*g)=ConditionalGaps.hits K s g := by
        apply filter_congr
        intro i hi
        change 0<fixedGap K i.val (n.val*g) ↔ 0<fixedGap K i.val g
        rw [stable_count K n g (mem_union_right _ (mem_image_of_mem _ hi))]
      simp only [u,we,he]
    let v (g : Aut K) := if 0<fixedGap K l.val g then u g else 0
    have half := weighted_hit K old l.prop lower sp u un st
    rw [if_pos (good l (mem_insert_self ..))] at half
    change uniform (Aut K) u≤2*uniform (Aut K) v at half
    have eq : (fun g => w g*z^(ConditionalGaps.hits K (insert l s) g).card)=u-(1-z) • v := by
      funext g
      have hne : l∉ConditionalGaps.hits K s g := fun h => hl (mem_filter.mp h).1
      by_cases hit : 0<fixedGap K l.val g
      · have h : 0<ConditionalGaps.count K l g := hit
        have ins : ConditionalGaps.hits K (insert l s) g=insert l (ConditionalGaps.hits K s g) := by
          simp [ConditionalGaps.hits,filter_insert,h]
        rw [ins,card_insert_of_notMem hne,pow_succ]
        simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,u,v,if_pos hit]
        ring
      · have h : ¬0<ConditionalGaps.count K l g := hit
        simp [ConditionalGaps.hits,filter_insert,h,hit,u,v]
    have step : uniform (Aut K) (fun g => w g*z^(ConditionalGaps.hits K (insert l s) g).card) ≤
        uniform (Aut K) u*((1+z)/2) := by
      rw [eq,map_sub,map_smul,smul_eq_mul]
      nlinarith [mul_nonneg (sub_nonneg.mpr hz') (sub_nonneg.mpr half)]
    have prev := ih (fun k hk i hi => below k hk i (mem_insert_of_mem hi))
      (fun i hi => good i (mem_insert_of_mem hi)) (fun k hk => split k (sub hk))
    rw [card_insert_of_notMem hl,pow_succ,← mul_assoc]
    exact step.trans (mul_le_mul_of_nonneg_right prev (by positivity))

#print axioms combined
#print axioms weighted_power
end
end Erdos478.FirstCollision
