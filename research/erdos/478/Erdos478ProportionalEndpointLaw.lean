import Erdos478ProportionalPrimeLengths
import Erdos478LocalizedEndpointVariance

/-!
# Local law of large numbers for distinct repeated factorial endpoints

The ordinary-prime variance for a finite family of selected gaps equals
its cardinality. After scaling by log K / K, its variance tends to zero
for every gap interval whose upper endpoint is asymptotic to L K, L > 1.
-/

namespace Erdos478.Proportional
open Filter Finset BandWeights BinaryGap GapBands GapSieve GapDensity
open scoped Topology Classical
noncomputable section

def gaps (K H : ℕ) : Finset Nat.Primes := (lengths selected K H).subtype Nat.Prime

theorem gap_mem {K H : ℕ} {l : Nat.Primes} :
    l∈gaps K H ↔ K<l.val ∧ l.val≤H ∧ selected l.val := by
  apply (mem_subtype (a:=⟨l.val,l.property⟩) (p:=Nat.Prime) (s:=lengths selected K H)).trans
  simp [lengths,l.property,and_assoc]

theorem gap_card (K H : ℕ) : (gaps K H).card=(lengths selected K H).card := by
  change ((lengths selected K H).subtype Nat.Prime).card=_
  have hf : (lengths selected K H).filter Nat.Prime=lengths selected K H :=
    filter_eq_self.mpr (fun _ hl => (mem_filter.mp hl).2.2)
  rw [card_subtype,hf]

def scale (K : ℕ) : ℝ := Real.log K/K

theorem scale_zero : Tendsto scale atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

def family_good (K : ℕ) (s : Finset Nat.Primes) (c η : ℝ) (p : ℕ) :=
  let U := joined s p
  |(U.card:ℝ)*scale K-c|<η ∧ ((Ico 1 p).image (fun n => n.factorial%p)).card+U.card≤p-1

def good (K H : ℕ) := family_good K (gaps K H)

theorem fraction_lower {X : ℕ} (hX : 2≤X) {bad good : ℕ → Prop}
    (hg : ∀ p, ¬bad p → good p) : 1-fraction X bad≤fraction X good := by
  have pos : 0<(Nat.primesLE X).card := card_pos.mpr ⟨2,Nat.mem_primesLE.mpr ⟨hX,Nat.prime_two⟩⟩
  have total : fraction X bad+fraction X (fun p => ¬bad p)=1 := by
    rw [fraction,fraction,← add_div,← Nat.cast_add,card_filter_add_card_filter_not,div_self (by exact_mod_cast pos.ne')]
  have le : fraction X (fun p => ¬bad p)≤fraction X good := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Nat.cast_le.mpr
    apply card_le_card
    intro p hp
    simp only [mem_filter] at hp ⊢
    exact ⟨hp.1,hg p hp.2⟩
  linarith

private theorem mean_limit (input : countingInput selected (1/6)) {H : ℕ → ℕ} {L : ℝ}
    (hL : 1<L) (h : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L)) :
    Tendsto (fun K : ℕ => ((gaps K (H K)).card:ℝ)*scale K) atTop (𝓝 ((L-1)/6)) := by
  rw [show (L-1)/6=1/6*(L-1) by ring]
  simpa only [gap_card,scale,mul_div_assoc] using length_asymptotic input hL h

/-- The variance at the scale log K/K vanishes in the outer limit. -/
theorem scaled_variance_zero (input : countingInput selected (1/6)) {H : ℕ → ℕ} {L : ℝ}
    (hL : 1<L) (h : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L)) :
    Tendsto (fun K : ℕ => ((gaps K (H K)).card:ℝ)*(scale K)^2) atTop (𝓝 0) := by
  simpa only [mul_zero,pow_two,mul_assoc] using (mean_limit input hL h).mul scale_zero

/-- For every A above the limiting Chebyshev coefficient, the exceptional
prime proportion is less than A log K / K throughout the tail of windows. -/
theorem family_rate (pit : DegreeOnePrimeIdealTheorem) (family : ℕ → Finset Nat.Primes) {c η A : ℝ}
    (hmass : Tendsto (fun K => ((family K).card:ℝ)*scale K) atTop (𝓝 c))
    (moments : ∀ᶠ K : ℕ in atTop, ∀ i∈family K, secondMomentTwo (countingAverage pit) i)
    (hη : 0<η) (hA : c/η^2<A) :
    ∀ᶠ K : ℕ in atTop, ∀ᶠ X : ℕ in atTop, 1-A*scale K<fraction X (family_good K (family K) c η) := by
  let m (K : ℕ) : ℝ := (family K).card
  let d (K : ℕ) := η-|m K*scale K-c|
  have hm : Tendsto (fun K => m K*scale K) atTop (𝓝 c) := hmass
  have hd : Tendsto d atTop (𝓝 η) := by
    simpa only [sub_self,abs_zero,sub_zero] using
      (tendsto_const_nhds (x:=η)).sub ((hm.sub (tendsto_const_nhds (x:=c))).abs)
  let B := (c/η^2+A)/2
  have hB : c/η^2<B := by dsimp [B]; linarith
  have hBA : B<A := by dsimp [B]; linarith
  have small := (hm.div (hd.pow 2) (sq_pos_of_pos hη).ne').eventually_lt_const hB
  filter_upwards [small,hd.eventually_const_lt hη,eventually_gt_atTop 1,moments] with K hv hpos hk hmoment
  let s := family K
  let w := scale K
  have hw : 0<w := div_pos (Real.log_pos (by exact_mod_cast hk)) (by positivity)
  change m K*w/(d K)^2<B at hv
  have rate : (s.card:ℝ)/(d K/w)^2<B*w := by
    calc
      (s.card:ℝ)/(d K/w)^2 = (m K*w/(d K)^2)*w := by
        unfold m s
        rw [div_pow,div_div_eq_mul_div]
        ring
      _ < _ := mul_lt_mul_of_pos_right hv hw
  have concentration := finite_concentration_of_moments pit s hmoment
    (t:=d K/w) (div_pos hpos hw) (mul_pos (sub_pos.mpr hBA) hw)
  filter_upwards [concentration,eventually_ge_atTop 2] with X hbad hX
  have comparison := fraction_lower hX (bad:=fun p => d K/w≤|((joined s p).card:ℝ)-s.card|)
    (good:=family_good K (family K) c η) (fun p hp => by
      refine ⟨?_,joined_deficit s p⟩
      have ht := (lt_div_iff₀ hw).mp (lt_of_not_ge hp)
      change |((joined s p).card:ℝ)*w-c|<η
      have bound := abs_add_le ((((joined s p).card:ℝ)-s.card)*w) ((s.card:ℝ)*w-c)
      rw [abs_mul,abs_of_pos hw] at bound
      rw [show (((joined s p).card:ℝ)-s.card)*w+(s.card*w-c)=((joined s p).card:ℝ)*w-c by ring] at bound
      change |((joined s p).card:ℝ)-s.card| * w<η-|(s.card:ℝ)*w-c| at ht
      linarith only [ht,bound])
  change 1-A*w<fraction X (family_good K (family K) c η)
  linarith only [rate,hbad,comparison]

theorem endpoint_rate (pit : DegreeOnePrimeIdealTheorem) (input : countingInput selected (1/6))
    {H : ℕ → ℕ} {L η A : ℝ} (hL : 1<L) (h : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L))
    (hη : 0<η) (hA : (L-1)/6/η^2<A) :
    ∀ᶠ K : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      1-A*scale K<fraction X (good K (H K) ((L-1)/6) η) := by
  apply family_rate pit (fun K => gaps K (H K)) (mean_limit input hL h) _ hη hA
  exact Eventually.of_forall fun _ i hi => square_mean _ i (gap_mem.mp hi).2.2

theorem endpoint_law (pit : DegreeOnePrimeIdealTheorem) (input : countingInput selected (1/6))
    {H : ℕ → ℕ} {L η ε : ℝ} (hL : 1<L) (h : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L))
    (hη : 0<η) (hε : 0<ε) :
    ∀ᶠ K : ℕ in atTop, ∀ᶠ X : ℕ in atTop, 1-ε<fraction X (good K (H K) ((L-1)/6) η) := by
  let A := (L-1)/6/η^2+1
  have rate := endpoint_rate pit input hL h hη (show (L-1)/6/η^2<A by dsimp [A]; linarith)
  have small := (tendsto_const_nhds (x:=A)).mul scale_zero
  rw [mul_zero] at small
  filter_upwards [rate,small.eventually_lt_const hε] with K hk hs
  filter_upwards [hk] with X hx
  exact (sub_lt_sub_left hs 1).trans hx

theorem family_deficit_fraction {K X : ℕ} (s : Finset Nat.Primes) {c b : ℝ} (hK : 1<K) :
    fraction X (family_good K s c (c-b))≤fraction X (fun p =>
      let D := ⌈b*K/Real.log K⌉₊
      D≤(joined s p).card ∧
      ((Ico 1 p).image (fun n => n.factorial%p)).card+D≤p-1) := by
  have pos : 0<(K:ℝ) := by positivity
  have lg : 0<Real.log K := Real.log_pos (by exact_mod_cast hK)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hm,hg⟩ := mem_filter.mp hp
  obtain ⟨hc,hd⟩ := hg
  let U := joined s p
  have hlow := (abs_lt.mp hc).1
  have hbound : b< (U.card:ℝ)*scale K := by linarith only [hlow]
  have enough : ⌈b*K/Real.log K⌉₊≤U.card := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ lg).mpr
    change b<(U.card:ℝ)*(Real.log K/K) at hbound
    rw [← mul_div_assoc] at hbound
    exact ((lt_div_iff₀ pos).mp hbound).le
  simp only [mem_filter]
  exact ⟨hm,enough,(Nat.add_le_add_left enough _).trans hd⟩

#print axioms family_deficit_fraction
#print axioms family_good
#print axioms family_rate
#print axioms gap_mem
#print axioms gap_card
#print axioms fraction_lower
#print axioms scale_zero
#print axioms scaled_variance_zero
#print axioms endpoint_rate
#print axioms endpoint_law
end
end Erdos478.Proportional
