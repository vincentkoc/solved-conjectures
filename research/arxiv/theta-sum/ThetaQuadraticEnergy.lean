import ThetaSpectrumDecay
import ThetaPrimeLaw
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! Variance carried by all odd prime quadratic characters. -/
namespace Arxiv.«2501.03234».ThetaQuadraticEnergy
open Finset Filter Topology ThetaSpectrumDecay ThetaPrimeLaw ThetaNaturalPrimeMeans
open ThetaCharacterPrimeMeans ThetaDiagonalConstant

private noncomputable abbrev w (q : OddPrime) (n : ℕ) : ℝ := (legendreSym q.val (n:ℤ):ℝ)
private noncomputable abbrev partialQ (s : Finset OddPrime) (n : ℕ) : ℝ := ∑ r∈s,coefficient r*w r n

private theorem finite_pairing {f : ℕ → ℝ} {b : OddPrime → ℝ}
    (hf : ∀ r, Tendsto (primeMean (fun p => w r p*f p)) atTop (𝓝 (b r))) (s : Finset OddPrime) :
    Tendsto (primeMean (fun p => f p*partialQ s p)) atTop (𝓝 (∑ r∈s,coefficient r*b r)) := by
  have H := tendsto_finsetSum s (fun r _ => (hf r).const_mul (coefficient r))
  apply H.congr'
  filter_upwards with X
  simp only [primeMean,partialQ,mul_sum,← mul_div_assoc,← sum_div]
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  ring

private lemma uniform_mean_bound {f g h : ℕ → ℝ} {δ : ℝ}
    (hδ : ∀ p, |g p-h p| ≤ δ) (X : ℕ) :
    |primeMean (fun p => f p*g p) X - primeMean (fun p => f p*h p) X| ≤
      δ*primeMean (fun p => |f p|) X := by
  simp only [primeMean,← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) X.primeCounting),
    ← mul_div_assoc,mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (abs_sum_le_sum_abs ..).trans
  exact sum_le_sum (fun p _ => by rw [← mul_sub,abs_mul,mul_comm δ]; gcongr; exact hδ p)

/-- Pair a uniformly convergent quadratic series with an observable whose mean
absolute value remains bounded along primes. -/
theorem quadratic_pairing (hAP : ProgressionMangoldt) {f : ℕ → ℝ} {b : OddPrime → ℝ} {M : ℝ}
    (hM : 0≤M) (hB : ∀ᶠ X : ℕ in atTop, primeMean (fun p => |f p|) X≤M)
    (hf : ∀ r : OddPrime, Tendsto (primeMean (fun p => (legendreSym r.val (p:ℤ):ℝ)*f p)) atTop (𝓝 (b r)))
    (hsum : Summable (fun r => coefficient r*b r)) :
    Tendsto (primeMean (fun p => f p*quadraticPart p)) atTop (𝓝 (∑' r,coefficient r*b r)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := (ε/3)/(M+1)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδM : δ*M≤ε/3 := by
    calc δ*M ≤ δ*(M+1) := by gcongr; linarith
         _ = _ := by dsimp only [δ]; field_simp
  have hu := Metric.tendstoUniformly_iff.mp (uniform_quadratic_series hAP) δ hδ
  have hs := Metric.tendsto_nhds.mp hsum.hasSum (ε/3) (by positivity)
  obtain ⟨s,hU,hS⟩ := (hu.and hs).exists
  have hF := Metric.tendsto_nhds.mp (finite_pairing hf s) (ε/3) (by positivity)
  filter_upwards [hF,hB] with X hX hbound
  have hb := uniform_mean_bound (f:=f) (g:=quadraticPart) (h:=partialQ s)
    (fun p => (hU p).le) X
  let T := ∑' r,coefficient r*b r
  have h₁ := dist_triangle (primeMean (fun p => f p*quadraticPart p) X) (primeMean (fun p => f p*partialQ s p) X) T
  have h₂ := dist_triangle (primeMean (fun p => f p*partialQ s p) X) (∑ r∈s,coefficient r*b r) T
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hbound hδ.le)
  simp only [T,Real.dist_eq] at h₁ h₂ hX hS ⊢
  linarith only [h₁,h₂,hX,hS,hb',hδM]

/-- Total energy of the odd prime quadratic modes. -/
noncomputable def quadraticEnergy : ℝ := ∑' r : OddPrime, (coefficient r)^2

lemma coefficient_squares_summable (hAP : ProgressionMangoldt) : Summable (fun r : OddPrime => (coefficient r)^2) := by
  have H := summable_coefficients hAP
  let K := ∑' r : OddPrime, |coefficient r|
  have hK (r : OddPrime) : |coefficient r| ≤ K := H.le_tsum r (fun i _ => abs_nonneg _)
  apply Summable.of_nonneg_of_le (fun r => sq_nonneg _) _ (H.mul_left K)
  intro r
  rw [← sq_abs, sq]
  exact mul_le_mul_of_nonneg_right (hK r) (abs_nonneg _)

private lemma abs_part_le (hAP : ProgressionMangoldt) (p : ℕ) :
    |quadraticPart p| ≤ ∑' r : OddPrime,|coefficient r| := by
  have hχ (r : OddPrime) : |w r p| ≤ 1 := by
    rw [w,jacobiSym.legendreSym.to_jacobiSym]
    rcases jacobiSym.trichotomy (p:ℤ) r.val with h|h|h <;> norm_num [h]
  have hbound (r : OddPrime) : ‖coefficient r*w r p‖ ≤ |coefficient r| := by
    simp only [Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hχ r)
  have H := summable_coefficients hAP
  have hs := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound H
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hbound H)

private lemma prime_zero (hAP : ProgressionMangoldt) (r : OddPrime) :
    Tendsto (primeMean (w r)) atTop (𝓝 0) := by
  have h₂ : r.val≠2 := fun h => by have ho := r.property.2; rw [h] at ho; exact (by decide : ¬Odd 2) ho
  change Tendsto (primeMean (fun p => (legendreSym r.val (p:ℤ):ℝ))) atTop (𝓝 0)
  simpa only [legendreSym,ThetaLegendreFactors.symbol,Int.cast_natCast] using
    ThetaPrimeSpectrum.prime_character_mean r.val hAP h₂

private lemma const_mean (c : ℝ) : Tendsto (primeMean (fun _ => c)) atTop (𝓝 c) :=
  prime_mean_of_convergence (by intro ε he; simp [he])

private theorem mean_part (hAP : ProgressionMangoldt) : Tendsto (primeMean quadraticPart) atTop (𝓝 0) := by
  have H := quadratic_pairing hAP (f:=fun _ => 1) (b:=fun _ => 0) (M:=2) (by norm_num)
    (by simpa only [abs_one] using ((const_mean 1).eventually_le_const (by norm_num : (1:ℝ)<2)))
    (fun r => by simpa using prime_zero hAP r) (by simp)
  simpa using H

private theorem mean_residual_bounded (hAP : ProgressionMangoldt) :
    ∃ M : ℝ, 0≤M ∧ ∀ᶠ X : ℕ in atTop, primeMean (fun p => |ThetaCharacterPrimeMeans.residual p|) X ≤ M := by
  obtain ⟨_,V,_,_,_,_,hV,_⟩ := S_prime_class_statistics hAP
  let B := diagonalConstant
  have hb (p : ℕ) : |ThetaCharacterPrimeMeans.residual p| ≤ (ThetaCharacterPrimeMeans.residual p-B)^2 + (1+|B|) := by
    have H := abs_add_le (ThetaCharacterPrimeMeans.residual p-B) B
    rw [sub_add_cancel] at H
    have hs := sq_abs (ThetaCharacterPrimeMeans.residual p-B)
    nlinarith only [H,hs,sq_nonneg (|(ThetaCharacterPrimeMeans.residual p-B)|-1/2)]
  have H := hV.add (const_mean (1+|B|))
  refine ⟨|V|+2+|B|,by positivity,?_⟩
  filter_upwards [H.eventually_le_const (show V+(1+|B|) < |V|+2+|B| by linarith [le_abs_self V])] with X hX
  apply (mean_mono hb X).trans
  rwa [mean_add]

private theorem mean_RQ (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun p => ThetaCharacterPrimeMeans.residual p*quadraticPart p)) atTop (𝓝 quadraticEnergy) := by
  obtain ⟨M,hm,hM⟩ := mean_residual_bounded hAP
  simpa only [← sq,quadraticEnergy] using quadratic_pairing hAP hm hM
    (fun r => coefficient_limit hAP r) (by simpa only [← sq] using coefficient_squares_summable hAP)

private theorem mean_QQ (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun p => (quadraticPart p)^2)) atTop (𝓝 quadraticEnergy) := by
  let K := ∑' r : OddPrime,|coefficient r|
  have hK : 0≤K := tsum_nonneg (fun _ => abs_nonneg _)
  have hbd : ∀ᶠ X : ℕ in atTop, primeMean (fun p => |quadraticPart p|) X ≤ K+1 := by
    filter_upwards [(const_mean K).eventually_le_const (by linarith : K<K+1)] with X hX
    exact (mean_mono (fun p => abs_part_le hAP p) X).trans hX
  have hcoeff (r : OddPrime) : Tendsto (primeMean (fun p => w r p*quadraticPart p)) atTop (𝓝 (coefficient r)) := by
    have H := (coefficient_limit hAP r).sub (orthogonal_remainder hAP r)
    rw [sub_zero] at H
    apply H.congr'
    filter_upwards with X
    simp only [w,primeMean,← sub_div,← sum_sub_distrib,mul_sub,sub_sub_cancel]
  simpa only [← sq,quadraticEnergy] using quadratic_pairing hAP (by linarith : 0≤K+1) hbd
    hcoeff (by simpa only [← sq] using coefficient_squares_summable hAP)

#print axioms mean_RQ
#print axioms mean_QQ

/-- The limiting empirical variance splits into a series of squares and the
variance of the residual after removing all odd prime quadratic modes. -/
theorem variance_decomposition (hAP : ProgressionMangoldt) :
    ∃ V W : ℝ, 0≤W ∧ V = quadraticEnergy+W ∧
      Tendsto (sampleVariance ThetaCharacterPrimeMeans.residual) atTop (𝓝 V) ∧
      Tendsto (sampleVariance (fun p => ThetaCharacterPrimeMeans.residual p-quadraticPart p)) atTop (𝓝 W) ∧
      Tendsto (primeMean (fun p => (quadraticPart p)^2)) atTop (𝓝 quadraticEnergy) ∧
      Tendsto (primeMean (fun p => (ThetaCharacterPrimeMeans.residual p-quadraticPart p)*quadraticPart p)) atTop (𝓝 0) := by
  obtain ⟨_,V,_,_,_,_,hV,hvar⟩ := S_prime_class_statistics hAP
  let Q := quadraticPart
  let R := ThetaCharacterPrimeMeans.residual
  let B := diagonalConstant
  have hRQ := mean_RQ hAP
  have hQQ := mean_QQ hAP
  have hQ := mean_part hAP
  have hZ := (hV.sub (hRQ.const_mul 2)).add (hQ.const_mul (2*B)) |>.add hQQ
  have hlim : Tendsto (primeMean (fun p => (R p-Q p-B)^2)) atTop (𝓝 (V-quadraticEnergy)) := by
    convert hZ.congr' _ using 2
    · ring
    · filter_upwards with X
      simp only [R,Q,B,primeMean,← mul_div_assoc,← sub_div,← add_div,mul_sum,
        ← sum_sub_distrib,← sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro p _
      ring
  have hA : Tendsto (primeMean (fun p => R p-Q p)) atTop (𝓝 B) := by
    have H := (S_second_order_prime_mean hAP).sub hQ
    rw [sub_zero] at H
    apply H.congr'
    filter_upwards with X
    simp only [R,Q,ThetaCharacterPrimeMeans.residual,primeMean,sum_sub_distrib,sub_div]
  have hsample := hlim.sub ((hA.sub_const B).pow 2)
  rw [sub_self,zero_pow (by decide : 2≠0),sub_zero] at hsample
  have hπ : Tendsto (fun X : ℕ => (X.primeCounting:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  have hres : Tendsto (sampleVariance (fun p => R p-Q p)) atTop (𝓝 (V-quadraticEnergy)) := by
    apply hsample.congr'
    filter_upwards [hπ.eventually_gt_atTop 0] with X hx
    exact (variance_recentering _ B hx).symm
  have hz : 0 ≤ V-quadraticEnergy := ge_of_tendsto hlim (.of_forall fun X => by
    apply div_nonneg _ (Nat.cast_nonneg _); exact sum_nonneg fun _ _ => sq_nonneg _)
  refine ⟨V,V-quadraticEnergy,hz,by ring,hvar,hres,hQQ,?_⟩
  have hcross := hRQ.sub hQQ
  rw [sub_self] at hcross
  apply hcross.congr'
  filter_upwards with X
  simp only [primeMean,← sub_div,← sum_sub_distrib,sub_mul,pow_two]

/-- Omitting any positive squared coefficient lowers the captured variance. In particular
every finite set of odd prime conductors misses a positive amount. -/
theorem finite_energy_strict (hAP : ProgressionMangoldt) (s : Finset OddPrime) :
    ∑ r∈s,(coefficient r)^2 < quadraticEnergy := by
  obtain ⟨q,hgt,hp,hq⟩ := Nat.forall_exists_prime_gt_and_modEq (∑ r∈s,r.val) (q:=4) (a:=3) (by decide) (by decide)
  have h3 : q%4=3 := hq
  let : Fact q.Prime := ⟨hp⟩
  let r : OddPrime := ⟨q,hp,Nat.odd_iff.mpr (by omega)⟩
  have hr : r ∉ s := fun h => hgt.not_ge (single_le_sum (f:=fun r : OddPrime => r.val) (fun _ _ => Nat.zero_le _) h)
  have hc : coefficient r≠0 := by
    obtain ⟨_,C,_,_,H,hne,_⟩ := ThetaPrimeSpectrum.prime_correlation r.val hAP h3
    have he := coefficient_limit hAP r
    simp only [legendreSym,ThetaLegendreFactors.symbol,Int.cast_natCast,ThetaCharacterPrimeMeans.residual] at H he
    exact (tendsto_nhds_unique he H).symm ▸ hne
  calc ∑ t∈s,(coefficient t)^2 < ∑ t∈insert r s,(coefficient t)^2 := by rw [sum_insert hr]; linarith [sq_pos_of_ne_zero hc]
       _ ≤ quadraticEnergy := (coefficient_squares_summable hAP).sum_le_tsum _ (fun _ _ => sq_nonneg _)

#print axioms finite_energy_strict

#print axioms coefficient_squares_summable
#print axioms variance_decomposition
#print axioms quadratic_pairing
end Arxiv.«2501.03234».ThetaQuadraticEnergy
