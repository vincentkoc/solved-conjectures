import Erdos478AbundantDyadicLengths
import Erdos478LocalizedEndpointVariance

/-!
# Near-linear factorial collision counts on frequent dyadic bands

The order of the quantifiers is essential: there are arbitrarily large band
indices j, and for each of them the observation-prime cutoff may depend on j.
-/

namespace Erdos478.BinaryGap
open Filter Topology Finset GapBands GapSieve GapDensity
noncomputable section

/-- The repeated endpoints and the factorial image use the same interval
1,…,p−1 as the pinned Erdős 478 predicate. -/
def witnessed (j D p : ℕ) := D≤(joined (family j) p).card ∧
  ((Ico 1 p).image (fun n => n.factorial%p)).card+D≤p-1

theorem scale_grows : Tendsto scale atTop atTop := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1:ℝ)<2)
  have pos : ∀ᶠ j : ℕ in atTop, (j:ℝ)^3/(2:ℝ)^j∈Set.Ioi 0 := by
    filter_upwards [eventually_gt_atTop 0] with j hj
    change 0<(j:ℝ)^3/(2:ℝ)^j
    positivity
  unfold scale
  simpa only [Pi.inv_def,inv_div] using (tendsto_nhdsWithin_iff.mpr ⟨h,pos⟩).inv_tendsto_nhdsGT_zero

private theorem fraction_mono (X : ℕ) {P Q : ℕ → Prop} (h : ∀ p, P p → Q p) :
    fraction X P≤fraction X Q := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  exact mem_filter.mpr ⟨(mem_filter.mp hp).1,h p (mem_filter.mp hp).2⟩

private theorem lower_fraction (j D X : ℕ) (hX : 2≤X) {t : ℝ}
    (hbad : ∀ p, (joined (family j) p).card<D → t≤|((joined (family j) p).card:ℝ)-(family j).card|) :
    1-fraction X (fun p => t≤|((joined (family j) p).card:ℝ)-(family j).card|)≤fraction X (witnessed j D) := by
  classical
  let bad (p : ℕ) := (joined (family j) p).card<D
  have iff (p) : witnessed j D p ↔ ¬bad p := by
    rw [witnessed,show ¬bad p ↔ D≤(joined (family j) p).card from not_lt]
    exact ⟨And.left,fun h => ⟨h,(Nat.add_le_add_left h _).trans (joined_deficit _ _)⟩⟩
  have pos : 0<(Nat.primesLE X).card := card_pos.mpr ⟨2,Nat.mem_primesLE.mpr ⟨hX,Nat.prime_two⟩⟩
  have total : fraction X bad+fraction X (witnessed j D)=1 := by
    rw [show witnessed j D=fun p => ¬bad p from funext fun p => propext (iff p)]
    rw [fraction,fraction,← add_div,← Nat.cast_add,card_filter_add_card_filter_not,div_self (by exact_mod_cast pos.ne')]
  have le : fraction X bad≤fraction X (fun p => t≤|((joined (family j) p).card:ℝ)-(family j).card|) :=
    fraction_mono X hbad
  linarith

/-- For every C and ε there are arbitrarily high dyadic gap bands giving
at least ceil(C·2^j/j³) distinct positive upper endpoints for more than a
1−ε proportion of observation primes, eventually at that fixed band. -/
theorem dyadic_of_pit (pit : DegreeOnePrimeIdealTheorem) {C ε : ℝ} (hC : 0<C) (hε : 0<ε) :
    ∃ᶠ j : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      1-ε<fraction X (witnessed j ⌈C*scale j⌉₊) := by
  have plentiful := frequently_many_lengths (mul_pos (by norm_num : (0:ℝ)<2) hC)
  have growth := scale_grows.eventually_gt_atTop (8/(ε*C))
  apply (plentiful.and_eventually growth).mono
  rintro j ⟨hm,hg⟩
  let m : ℝ := (family j).card
  change 2*C*scale j<m at hm
  have hh := (div_lt_iff₀ (mul_pos hε hC)).mp hg
  have hi : 8<m*ε := by nlinarith only [hh,mul_lt_mul_of_pos_right hm hε]
  have mpos : 0<m := by by_contra! hn; nlinarith only [hi,mul_nonpos_of_nonpos_of_nonneg hn hε.le]
  have hlim := finite_concentration pit (family j) (fun _ hi => (family_mem.mp hi).2.2)
    (t:=m/2) (half_pos mpos) (half_pos hε)
  have rate : m/(m/2)^2<ε/2 := by
    field_simp
    nlinarith only [hi]
  filter_upwards [hlim,eventually_ge_atTop 2] with X hx hX
  have lb := lower_fraction j ⌈C*scale j⌉₊ X hX (t:=m/2) (fun p hp => by
    have h := Nat.lt_ceil.mp hp
    apply le_trans _ (neg_le_abs _)
    change m/2≤-(((joined (family j) p).card:ℝ)-m)
    linarith only [h,hm])
  change fraction X _<m/(m/2)^2+ε/2 at hx
  linarith

#print axioms scale_grows
#print axioms dyadic_of_pit
end
end Erdos478.BinaryGap
