import ThetaMixedPowerEndpoint
import ThetaSievedOrbitMoments
import ThetaSievedWindows

/-! An upper sieve for arbitrary even moments of the centered low theta rows. -/
namespace Arxiv.«2501.03234».ThetaSievedCenteredMoment
open Finset Real Filter ThetaPrimeSieve ThetaPeriodMeans ThetaSmoothConditionalModel
open ThetaCenteredWindow ThetaCenteredMoment ThetaOrbitProjection ThetaReciprocalBlocks ThetaIdentityModels
open ThetaRowCorrelations ThetaWindowFiniteMoments ThetaTiltBudget
noncomputable section

/-- The two sieve factors cost a fixed sixth power of R at the endpoint.
Only the row-denominator factor is raised to the moment order. -/
theorem endpoint {Y R : ℕ} (hR : 1≤R) (hYR : Y≤R) (f : ℕ → ℕ → ℝ) (X k : ℕ)
    {B : ℝ} (hB : 0≤B) (hf : ∀ d∈Icc 2 Y, OnMod d (f d)) (hb : ∀ d∈Icc 2 Y, ∀ n, |f d n|≤B) :
    (∑ n∈range X,weight R n*(∑ d∈Icc 2 Y,f d n)^k) ≤
      (X:ℝ)*mean R.factorial (fun n => weight R n*(∑ d∈Icc 2 Y,f d n)^k)+
        2*(R:ℝ)^6*(B*(Y:ℝ)^2)^k := by
  classical
  let I := moduli R ×ˢ moduli R
  let c (r n : ℕ) := ramanujan r n/(r.totient:ℝ)/normalizer R
  let g (i : ℕ×ℕ) (n : ℕ) := c i.1 n*c i.2 n
  let F (n : ℕ) := (∑ d∈Icc 2 Y,f d n)^k
  have hsum (n : ℕ) : weight R n=∑ i∈I,g i n := by
    rw [weight,pow_two,sum_div,sum_product]
    simp only [g,c,Finset.sum_mul,Finset.mul_sum]
    exact sum_congr rfl (fun r _ => sum_congr rfl (fun s _ => mul_comm ..))
  have hG := one_le_normalizer hR
  have hc (r) (hr : r∈moduli R) (n) : |c r n|≤R := by
    obtain ⟨hri,hsq⟩ := mem_filter.mp hr
    obtain ⟨hr₁,hrR⟩ := mem_Icc.mp hri
    have hφ : (1:ℝ)≤r.totient := by exact_mod_cast (Nat.totient_pos.mpr hr₁)
    dsimp [c];rw [abs_div,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) r.totient),abs_of_nonneg (by linarith : 0≤normalizer R)]
    apply (div_le_self (by positivity) hG).trans
    exact (div_le_self (abs_nonneg _) hφ).trans ((ramanujan_bound hsq n).trans (by exact_mod_cast hrR))
  have hper (r) (hr : r∈moduli R) : OnMod r (c r) := fun n => by
    dsimp only [c];rw [ramanujan_onMod (mem_filter.mp hr).2 n]
  have hrd (r) (hr : r∈moduli R) : r∣R.factorial :=
    Nat.dvd_factorial (mem_Icc.mp (mem_filter.mp hr).1).1 (mem_Icc.mp (mem_filter.mp hr).1).2
  have hterm (i : ℕ×ℕ) (hi : i∈I) : ∑ n∈range X,g i n*F n≤
      (X:ℝ)*mean R.factorial (fun n => g i n*F n)+2*(R:ℝ)^4*(B*(Y:ℝ)^2)^k := by
    obtain ⟨hr,hs⟩ := mem_product.mp hi
    let q := Nat.lcm i.1 i.2
    have hd : q∣R.factorial := Nat.lcm_dvd (hrd _ hr) (hrd _ hs)
    have hq : (q:ℝ)≤(R:ℝ)^2 := by
      have h := (Nat.lcm_le_mul (mem_Icc.mp (mem_filter.mp hr).1).1 (mem_Icc.mp (mem_filter.mp hs).1).1).trans
        (Nat.mul_le_mul (mem_Icc.mp (mem_filter.mp hr).1).2 (mem_Icc.mp (mem_filter.mp hs).1).2)
      rw [←Nat.pow_two] at h;exact_mod_cast h
    have hg : OnMod q (g i) := fun n => by
      dsimp only [g];rw [onMod_lift (Nat.dvd_lcm_left ..) (hper _ hr) n,onMod_lift (Nat.dvd_lcm_right ..) (hper _ hs) n]
    have hgb (n : ℕ) : |g i n|≤(R:ℝ)^2 := by
      dsimp only [g];rw [abs_mul,pow_two]
      exact mul_le_mul (hc _ hr _) (hc _ hs _) (abs_nonneg _) (Nat.cast_nonneg _)
    apply (ThetaMixedPowerEndpoint.mixed (Nat.pos_of_dvd_of_pos hd (Nat.factorial_pos _)) (Nat.factorial_pos _)
      hd (Nat.factorial_dvd_factorial hYR) (g i) hg hgb f X k hB hf hb).trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hq (sq_nonneg (R:ℝ))]
  have hcard' : (moduli R).card≤R := (card_le_card (filter_subset (p:=Squarefree) (Icc 1 R))).trans (by simp [Nat.card_Icc])
  have hcard : (I.card:ℝ)≤(R:ℝ)^2 := by
    dsimp [I];rw [card_product,pow_two];exact_mod_cast Nat.mul_le_mul hcard' hcard'
  change (∑ n∈range X,weight R n*F n)≤(X:ℝ)*mean R.factorial (fun n => weight R n*F n)+_
  simp_rw [hsum,sum_mul]
  rw [sum_comm]
  apply (sum_le_sum hterm).trans
  rw [sum_add_distrib,←mul_sum]
  have he : (∑ i∈I,mean R.factorial (fun n => g i n*F n))=mean R.factorial (fun n => ∑ i∈I,g i n*F n) := by
    simp only [mean,←sum_div];rw [sum_comm]
  rw [he,sum_const,nsmul_eq_mul]
  apply add_le_add_right
  apply (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq
  ring

/-- Every finite subset of primes exceeding R satisfies the same moment
estimate, with the full prime-density logarithm in the leading term. -/
theorem primes : ∀ᶠ U : ℕ in atTop, ∀ Y R : ℕ, 2≤R → Y≤R → ∀ (W : Window) (X k : ℕ)
    (s : Finset ℕ), (∀ p∈s,p.Prime ∧ R<p ∧ p<X) →
    (∑ p∈s,(center Y U W p)^(2*k)) ≤
      (X:ℝ)*(Z/log R)*(2*exp total)*(((2*k:ℕ):ℝ)/tilt U)^(2*k)+
        2*(R:ℝ)^6*(12*Z*(Y:ℝ)^2)^(2*k) := by
  filter_upwards [ThetaSievedOrbitMoments.absolute,eventually_ge_atTop 1] with U H hU
  intro Y R hR hYR W X k s hs
  have hR' : 1≤R := by omega
  have ha := tilt_pos hU
  have hz : 0≤Z := tsum_nonneg (fun _ => by positivity)
  let f (d n : ℕ) := (commonWeight W.weightCutoff d/d)*row d (W.width d) n
  have hf (d : ℕ) : OnMod d (f d) := fun n =>
    congrArg (fun z => commonWeight W.weightCutoff d/d*z) (row_onMod d (W.width d) n)
  have hb (d : ℕ) (hd : d∈Icc 2 Y) (n : ℕ) : |f d n|≤6*Z := weighted_bound (mem_Icc.mp hd).1 W n
  let g (d n : ℕ) := f d n-smooth Y U (f d) n
  have hg (d : ℕ) : OnMod d (g d) := fun n => by dsimp only [g];rw [hf d n,smooth_periodic (hf d) Y U n]
  have he (n : ℕ) : (∑ d∈Icc 2 Y,g d n)=center Y U W n := by
    dsimp only [g]
    rw [sum_sub_distrib,←smooth_sum]
    rfl
  have hfin := endpoint hR' hYR g X (2*k) (show 0≤12*Z by positivity) (fun d _ => hg d)
    (fun d hd n => (abs_sub _ _).trans (by linarith only [hb d hd n,smooth_bound (hb d hd) Y U n]))
  simp_rw [he] at hfin
  let v := (((2*k:ℕ):ℝ)/tilt U)^(2*k)
  have hv : 0≤v := pow_nonneg (div_nonneg (Nat.cast_nonneg _) ha.le) _
  have hm : mean R.factorial (fun n => weight R n*(center Y U W n)^(2*k))≤v*((2*exp total)*(normalizer R)⁻¹) := by
    have h (n : ℕ) := mul_le_mul_of_nonneg_left (pointwise_power ha (2*k) (center Y U W n)) (show 0≤weight R n from sq_nonneg _)
    have h' (n : ℕ) : weight R n*(center Y U W n)^(2*k)≤v*(weight R n*exp (tilt U*|center Y U W n|)) := (h n).trans_eq (by dsimp [v];ring)
    have he' := sum_le_sum (s:=range R.factorial) (fun n _ => h' n)
    rw [←mul_sum] at he'
    apply (div_le_div_of_nonneg_right he' (Nat.cast_nonneg (α:=ℝ) R.factorial)).trans
    rw [mul_div_assoc];exact mul_le_mul_of_nonneg_left (H Y R hR' hYR W) hv
  have hn : (normalizer R)⁻¹≤Z/log R := ThetaSievedWindows.normalizer_bound hR
  have hsub : s⊆range X := fun p hp => mem_range.mpr (hs p hp).2.2
  calc
    _ = ∑ p∈s,weight R p*(center Y U W p)^(2*k) := sum_congr rfl (fun p hp => by rw [weight_prime hR' (hs p hp).1 (hs p hp).2.1,one_mul])
    _ ≤ _ := (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => mul_nonneg (sq_nonneg _) (Even.pow_nonneg (even_two_mul k) _))).trans hfin
    _ ≤ _ := by
      apply add_le_add_left
      have hw := hm.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (by positivity : 0≤2*exp total)) hv)
      exact (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg X)).trans_eq (by dsimp only [v];ring)

#print axioms endpoint
#print axioms primes
end
end Arxiv.«2501.03234».ThetaSievedCenteredMoment
