import Erdos478HitSetDensities

/-! # Exponential lower-tail bounds for the number of distinct hit lengths -/

namespace Erdos478.ConditionalGaps
open Finset BinaryGap GapDensity RootMoments Filter Topology
open scoped Classical
noncomputable section

private theorem fair_power (s : Finset Nat.Primes) (z : ℝ) :
    fair s (fun u => z^u.card)=((1+z)/2)^s.card := by
  have h := Finset.prod_one_add (f:=fun _ : Nat.Primes => z) s
  simpa [fair,div_pow] using congrArg (fun x : ℝ => x/2^s.card) h.symm

/-- A free generating-function parameter gives a Chernoff bound for every
integer count threshold. Each success counts a distinct gap length. -/
theorem tilted_upper (s : Finset Nat.Primes) (good : ∀ i∈s, broad i.val ∧ 3 < i.val)
    (t : ℕ) {z : ℝ} (hz : 0<z) (hz' : z≤1) :
    law s (fun u => u.card≤t)≤((1+z)/2)^s.card/z^t := by
  have upper := decreasing_upper s good (fun u => u.card≤t) (fun _ _ h ht => (card_le_card h).trans ht)
  apply le_trans upper
  rw [← fair_event,← fair_power]
  apply (le_div_iff₀ (pow_pos hz t)).mpr
  unfold fair
  rw [div_mul_eq_mul_div,Finset.sum_mul]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro u _
  by_cases h : u.card≤t
  · simpa [h] using pow_le_pow_of_le_one hz.le hz' h
  · simp [h,pow_nonneg hz.le]

/-- At most a third of the lengths hit on a prime set of density at most
(27/32) to the power floor(m/3). -/
theorem third_upper (s : Finset Nat.Primes) (good : ∀ i∈s, broad i.val ∧ 3 < i.val) :
    law s (fun u => u.card≤s.card/3)≤(27/32 : ℝ)^(s.card/3) := by
  have h := tilted_upper s good (s.card/3) (z:=1/2) (by norm_num) (by norm_num)
  norm_num only [show (1+(1/2 : ℝ))/2=3/4 by norm_num] at h
  apply le_trans h
  have powle := pow_le_pow_of_le_one (a:=(3/4 : ℝ)) (by norm_num) (by norm_num)
    (show 3*(s.card/3)≤s.card by omega)
  calc
    (3/4 : ℝ)^s.card/(1/2)^ (s.card/3) ≤ (3/4 : ℝ)^(3*(s.card/3))/(1/2)^(s.card/3) :=
      div_le_div_of_nonneg_right powle (by positivity)
    _ = _ := by rw [pow_mul,← div_pow]; norm_num

/-- Add a certificate using exactly the factorial image in the host. All
selected lengths can be counted against distinct nonzero-image losses
after excluding finitely many primes. -/
theorem certified_of_pit (pit : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes) (E : Finset Nat.Primes → Prop) :
    Tendsto (fun X => GapSieve.fraction X (fun p => E (GapSieve.hits s p) ∧
      ((Ico 1 p).image (fun n => n.factorial%p)).card+(GapSieve.hits s p).card≤p-1)) atTop (𝓝 (law s E)) := by
  classical
  obtain ⟨B,hB⟩ := GapSieve.hits_le_deficit s
  let A := countingAverage pit
  let a (p : ℕ) := if E (GapSieve.hits s p) ∧
      ((Ico 1 p).image (fun n => n.factorial%p)).card+(GapSieve.hits s p).card≤p-1 then (1:ℝ) else 0
  have h := CollisionLaw.mean_of_change A (a:=a)
    (b:=fun p => if E (GapSieve.hits s p) then (1:ℝ) else 0) B (by
      intro p hp hpr
      have b := hB p hp hpr
      unfold MeanDeficit.deficit at b
      have qty : ((Ico 1 p).image (fun n => n.factorial%p)).card+(GapSieve.hits s p).card≤p-1 := by omega
      simp [a,qty]) (hit_score_mean A s (fun u => if E u then (1:ℝ) else 0))
  apply h.congr
  intro X
  exact GapSieve.ordinary_eq X _

#print axioms tilted_upper
#print axioms third_upper
#print axioms certified_of_pit
end
end Erdos478.ConditionalGaps
