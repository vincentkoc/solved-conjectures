import ThetaPrimeSpectrum
import ThetaPrimeVariance

/-! Every fixed-period subtraction leaves a nonzero quadratic-character
coefficient while its unweighted prime second moment remains bounded. -/
namespace Arxiv.«2501.03234».ThetaPeriodicCorrelationWitness
open Real Filter Finset ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans ThetaConditionalRows
open ThetaLegendreFactors ThetaPeriodMeans
open scoped Topology
noncomputable section

theorem periodic_bound {m : ℕ} [NeZero m] {g : ℕ → ℝ} (hg : OnMod m g) :
    ∃ B : ℝ,0≤B ∧ ∀ n,|g n|≤B := by
  refine ⟨∑ i∈range m,|g i|,sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  intro n
  rw [←hg n]
  exact single_le_sum (fun i _ => abs_nonneg (g i)) (mem_range.mpr (Nat.mod_lt _ (NeZero.pos _)))

theorem pnt (hAP : ProgressionMangoldt) :
    Tendsto (fun X : ℕ => (X.primeCounting:ℝ)*log X/X) atTop (𝓝 1) := by
  simpa [ThetaPrimeDensity.primeSet,Nat.mod_one,Nat.primesLE_card_eq_primeCounting] using
    prime_count_of_mangoldt (hAP (q:=1) (a:=0) (by decide) (by decide) (by decide))

theorem second (hAP : ProgressionMangoldt) {m : ℕ} [NeZero m] {g : ℕ → ℝ} (hg : OnMod m g) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ X : ℕ in atTop,(∑ p∈Nat.primesLE X,(residual p-g p)^2)*log X≤B*X := by
  obtain ⟨M,hM,hm⟩ := periodic_bound hg
  obtain ⟨A,hA,hh⟩ := ThetaPrimeVariance.prime_second_moment
  refine ⟨2*A+4*M^2,by positivity,?_⟩
  filter_upwards [(pnt hAP).eventually_lt_const (by norm_num : (1:ℝ)<2),eventually_ge_atTop (2:ℕ)]
    with X hπ hx
  have hX : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_pos (show (1:ℝ)<X by exact_mod_cast hx)
  have hπ' := (div_lt_iff₀ hX).mp hπ
  have ha := (le_div_iff₀ hl).mp (hh X hx)
  change (∑ p∈Nat.primesLE X,(residual p)^2)*log X≤A*X at ha
  have h (p : ℕ) : (residual p-g p)^2≤2*(residual p)^2+2*M^2 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg (g p)) (hm p) 2
    rw [sq_abs] at hsq
    nlinarith only [sq_nonneg (residual p+g p),hsq]
  have hs := sum_le_sum (s:=Nat.primesLE X) (fun p _ => h p)
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting] at hs
  nlinarith only [mul_le_mul_of_nonneg_right hs hl.le,ha,mul_le_mul_of_nonneg_right hπ'.le (sq_nonneg M)]

theorem spectral (hAP : ProgressionMangoldt) (m : ℕ) [NeZero m] :
    ∃ q : ℕ, m<q ∧ q.Prime ∧ q%4=3 ∧ ∃ v : ℕ → ℝ, OnMod q v ∧
    (∀ n,v n=0 ∨ v n=1 ∨ v n= -1) ∧ Tendsto (primeMean v) atTop (𝓝 0) ∧ ∃ C : ℝ,C≠0 ∧ ∀ g : ℕ → ℝ,OnMod m g →
    Tendsto (primeMean (fun n => v n*(residual n-g n))) atTop (𝓝 C) := by
  obtain ⟨q,hqm,hpr,hq⟩ := Nat.forall_exists_prime_gt_and_modEq m (q:=4) (a:=3) (by decide) (by decide)
  let : Fact q.Prime := ⟨hpr⟩
  have hq3 : q%4=3 := hq
  let v (n : ℕ) : ℝ := symbol q n
  have hv : OnMod q v := fun n => congrArg (Int.cast (R:=ℝ)) (symbol_mod q (dvd_refl q) n)
  have hc := hpr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (NeZero.pos m) hqm)
  obtain ⟨_,C,_,_,hC,hC₀,_⟩ := ThetaPrimeSpectrum.prime_correlation q hAP hq3
  refine ⟨q,hqm,hpr,hq3,v,hv,?_,ThetaPrimeSpectrum.prime_character_mean q hAP (by omega),C,hC₀,?_⟩
  · intro n
    by_cases h : q∣n
    · exact Or.inl (by simp [v,symbol_zero q h])
    · rcases symbol_unit q h with h|h
      · exact Or.inr (Or.inl (by simp [v,h]))
      · exact Or.inr (Or.inr (by simp [v,h]))
  intro g hg
  have hper : OnMod (q*m) (fun n => v n*g n) := fun n =>
    congrArg₂ (·*·) (onMod_lift (Nat.dvd_mul_right q m) hv n) (onMod_lift (Nat.dvd_mul_left m q) hg n)
  have hzero := periodic_prime_mean hAP hper
  rw [unitMean_mul hc hv hg,ThetaPrimeSpectrum.symbol_unitMean_zero q (by omega),zero_mul] at hzero
  have hh := hC.sub hzero
  rw [sub_zero] at hh
  change Tendsto (fun X : ℕ => primeMean (fun n => v n*(residual n-g n)) X) atTop (𝓝 C)
  simpa only [primeMean,v,←sub_div,←sum_sub_distrib,←mul_sub] using hh

theorem mean_lower (hAP : ProgressionMangoldt) {C : ℝ} (hC₀ : C≠0) {g : ℕ → ℝ}
    (hc : Tendsto (primeMean g) atTop (𝓝 C)) :
    ∀ᶠ X : ℕ in atTop, |C|/4*X≤|(∑ p∈Nat.primesLE X,g p)| * log X := by
  have hh := hc.abs
  have hpos := abs_pos.mpr hC₀
  have hlim := hh.eventually_const_lt (half_lt_self hpos)
  have hm := (pnt hAP).eventually_const_lt (by norm_num : (1:ℝ)/2<1)
  filter_upwards [hlim,hm,Nat.tendsto_primeCounting.eventually_gt_atTop (0:ℕ),eventually_ge_atTop (2:ℕ)]
    with X hL hπ hp hx
  have hpr' : 0<(X.primeCounting:ℝ) := by exact_mod_cast hp
  have hl := log_pos (show (1:ℝ)<X by exact_mod_cast hx)
  have hX : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  change |C|/2 < |primeMean g X| at hL
  rw [primeMean,abs_div,abs_of_pos hpr'] at hL
  have ha := (lt_div_iff₀ hpr').mp hL
  have hb := (lt_div_iff₀ hX).mp hπ
  linarith only [mul_le_mul_of_nonneg_right ha.le hl.le,mul_le_mul_of_nonneg_left hb.le (half_pos hpos).le]

theorem witness (hAP : ProgressionMangoldt) (m : ℕ) [NeZero m] :
    ∃ q : ℕ, m<q ∧ q.Prime ∧ q%4=3 ∧ ∃ v : ℕ → ℝ, (∀ n,|v n|≤1) ∧
      (∀ n j,v (n+q*j)=v n) ∧ ∃ c : ℝ,0<c ∧ ∀ g : ℕ → ℝ, OnMod m g →
      ∀ᶠ X : ℕ in atTop, c*X≤|(∑ p∈Nat.primesLE X,v p*(residual p-g p))| * log X := by
  obtain ⟨q,hqm,hpr,hq,v,hv,hs,_,C,hC,hh⟩ := spectral hAP m
  refine ⟨q,hqm,hpr,hq,v,?_,?_,|C|/4,by positivity,fun g hg => mean_lower hAP hC (hh g hg)⟩
  · intro n;rcases hs n with h|h|h <;> simp [h]
  · intro n j;rw [←hv (n+q*j),Nat.add_mul_mod_self_left,hv]

#print axioms second
#print axioms spectral
#print axioms witness
end
end Arxiv.«2501.03234».ThetaPeriodicCorrelationWitness
