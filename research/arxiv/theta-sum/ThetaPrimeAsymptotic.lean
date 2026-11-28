import ThetaNondivisibleCone
import ThetaPrimeDensity

/-! A density-one asymptotic for the original theta sum at primes. -/

namespace Arxiv.«2501.03234».ThetaPrimeAsymptotic

open Finset Filter ThetaCotangentTriangle ThetaReciprocalCutoff ThetaNondivisibleCone
open ThetaReciprocalInversion ThetaReciprocalVariance ThetaDivisibleDiagonal ThetaPrimeDensity

/-- The window interpolation reproduces the nondivisible cone at primes above its cutoff. -/
theorem cone_interpolation {p J K : ℕ} (hK : K%2=1) (hp : p.Prime) (hJ : 2*J<p) :
    windowExtension (coneWindow K) (2*J) p = (rationalCone p J K : ℂ) := by
  have hc (d : ℕ) (hd : d ∈ Icc 1 (2*J)) : p.Coprime d := hp.coprime_iff_not_dvd.mpr
    (fun h => (lt_of_le_of_lt (mem_Icc.mp hd).2 hJ).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 h))
  rw [windowExtension_nondivisible (by omega) hc]
  let f (u v : ℕ) : ℂ := (nondivSign p u v:ℂ)/((u:ℂ)*v)
  have h (u : ℕ) : (∑ v ∈ range (K*u), if u%2=1 ∧ v%2=1 ∧ ¬u∣v then
      (reciprocalSign p u v:ℂ)/((u:ℂ)*v) else 0) =
      (if u%2=1 then ∑ v ∈ range (K*u), (if v%2=1 then f u v else 0) else 0) := by
    by_cases hu : u%2=1
    · rw [if_pos hu]; apply sum_congr rfl; intro v _
      dsimp [f,nondivSign]; split_ifs <;> simp_all
    · simp [hu]
  simp_rw [h]
  rw [odds_interval _ J (by intro n hn; have := (mem_Icc.mp hn).2; omega)
    (by intro j hj; exact mem_Icc.mpr (by omega))]
  unfold rationalCone; push_cast
  apply sum_congr rfl; intro j _
  have ho : (K*(2*j+1))%2=1 := by rw [Nat.mul_mod,hK]; omega
  rw [odds_interval _ (K*(2*j+1)/2) (by intro n hn; have := mem_range.mp hn; omega)
    (by intro k hk; exact mem_range.mpr (by omega))]
  apply sum_congr rfl; intro k _
  dsimp [f]; push_cast; ring

/-- The scale and width errors separate after retaining one denominator power. -/
theorem vanishing_cone_error {K N p : ℕ} [Fact p.Prime] (hN : 2≤N) (hK : K%2=1)
    (hKN : K≤N) (hl : N^56≤p) (hh : p≤N^64) (ho : p%2=1) :
    |offDiagonal p - (8*p/Real.pi^2)*(rationalCone p (N^52) K:ℝ)| ≤
      2265642*(p:ℝ)/N + (2*(p:ℝ)/K)*(1+Real.log p) := by
  have hN₁ : 1≤N := by omega
  have hNr : 1≤(N:ℝ) := by exact_mod_cast hN₁
  have hpr : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hKr : 0<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hJ := cutoff_inside hN hl
  have hfit : K*(2*N^52) ≤ p := by
    calc _ ≤ N*(N*N^52) := Nat.mul_le_mul hKN (Nat.mul_le_mul_right _ hN)
         _ = N^54 := by ring
         _ ≤ N^56 := Nat.pow_le_pow_right hN₁ (by decide)
         _ ≤ p := hl
  have hKJ : K*N^52 ≤ N^64 := by
    calc _ ≤ N*N^52 := Nat.mul_le_mul_right _ hKN
         _ = N^53 := by ring
         _ ≤ N^64 := Nat.pow_le_pow_right hN₁ (by decide)
  have hH := small_harmonic hN₁ ((Nat.div_le_self p 2).trans hh)
  have hHK := small_harmonic hN₁ hKJ
  have hH₀ : (0:ℝ)≤harmonic (p/2) := by unfold harmonic; positivity
  have hs : p.sqrt ≤ N^32 := by
    apply (Nat.sqrt_le_sqrt hh).trans_eq
    rw [show N^64=(N^32)*(N^32) by ring,Nat.sqrt_eq]
  have hs' : (p.sqrt:ℝ)≤(N:ℝ)^50 := by exact_mod_cast hs.trans (Nat.pow_le_pow_right hN₁ (by decide : 32≤50))
  have hD : discrepancy p+2*(p.sqrt:ℝ) ≤ 17426*(N:ℝ)^50 := by linarith [scale_discrepancy hN₁ hh]
  have ht : 2*(discrepancy p+2*(p.sqrt:ℝ))*p*harmonic (p/2)/(2*(↑(N^52 : ℕ):ℝ)+1) ≤ 2265380*p/N := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; push_cast
    have he := mul_le_mul hD hH hH₀ (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right he (show 0≤(p:ℝ)*N by positivity),hpr.le,
      mul_nonneg (pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) 52) hpr.le]
  have hlin : 2*(↑(N^52:ℕ):ℝ)^2*(2*(harmonic (K*N^52):ℝ)+(K:ℝ)^2)/p ≤ 262*p/N := by
    rw [div_le_div_iff₀ hpr (by positivity)]; push_cast
    have h := pow_le_pow_left₀ hKr.le (show (K:ℝ)≤N by exact_mod_cast hKN) 2
    have hn : (N:ℝ)≤(N:ℝ)^2 := by nlinarith only [mul_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) (sub_nonneg.mpr hNr)]
    have he : 2*(harmonic (K*N^52):ℝ)+(K:ℝ)^2 ≤ 131*(N:ℝ)^2 := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left he (show 0≤(N:ℝ)^105 by positivity),
      pow_le_pow_right₀ hNr (by decide : 107≤112),
      pow_le_pow_left₀ (by positivity) (show (N:ℝ)^56≤p by exact_mod_cast hl) 2]
  have hH' : (harmonic (N^52):ℝ)≤1+Real.log p := by
    apply (harmonic_le_one_add_log _).trans; apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show N^52≤p by omega)
  have hw : 2*(p:ℝ)*harmonic (N^52)/K ≤ (2*(p:ℝ)/K)*(1+Real.log p) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hH' (by positivity)
  apply (offDiagonal_cone_error ho hK (by omega) hfit).trans
  exact (add_le_add (add_le_add ht hw) hlin).trans_eq (by ring)

/-- Uniform error in approximating the off-diagonal by the variable-width rational cone. -/
theorem uniform_approximation {K N p : ℕ} [Fact p.Prime] (hN : 2≤N) (hK : K%2=1)
    (hKN : K≤N) (hl : N^56≤p) (hh : p≤N^64) (ho : p%2=1) :
    |offDiagonal p - (8*p/Real.pi^2)*(rationalCone p (N^52) K:ℝ)| ≤
      2300000*(p:ℝ) + (2*(p:ℝ)/K)*(1+Real.log p) := by
  apply (vanishing_cone_error hN hK hKN hl hh ho).trans
  apply add_le_add _ le_rfl
  apply (div_le_self (by positivity) (by exact_mod_cast (show 1≤N by omega))).trans
  exact mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)

private noncomputable def coeff : ℝ := 8/Real.pi^2

private def bad (ε : ℝ) (p : ℕ) : Prop :=
  ε*(p:ℝ)*Real.log p ≤ |(S p:ℝ)-(p:ℝ)*Real.log p/2|

private lemma forces_cone {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℕ, K%2=1 ∧ ∃ δ : ℝ, 0<δ ∧ ∀ᶠ N : ℕ in atTop, ∀ p : ℕ,
    p.Prime → N^56≤p → p≤N^64 → bad ε p →
      δ*Real.log N ≤ ‖windowExtension (coneWindow K) (2*N^52) p‖ := by
  obtain ⟨C,hC,hdiag⟩ := S_sub_offDiagonal_asymptotic
  obtain ⟨m,hm⟩ := exists_nat_gt (8/ε)
  let K := 2*m+1
  have hK : K%2=1 := by dsimp [K]; omega
  have hKr : 0<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hκ : 2/(K:ℝ) ≤ ε/4 := by
    have h := (div_lt_iff₀ hε).mp hm
    rw [div_le_div_iff₀ hKr (by norm_num)]
    dsimp [K]; push_cast; nlinarith
  have hcoeff : 0<coeff := by dsimp [coeff]; positivity
  let A := C+2300000+2/(K:ℝ)
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (Real.exp (4*A/ε))
  refine ⟨K,hK,ε/(2*coeff),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max 2 (max K N₀))] with N hN
  intro p hp hlo hhi hb
  let : Fact p.Prime := ⟨hp⟩
  have hN₂ : 2≤N := by omega
  have hN₁ : 1≤N := by omega
  have hNl : N≤p := (Nat.le_self_pow (by decide : 56≠0) N).trans hlo
  have hpr : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have ho : p%2=1 := by
    rcases hp.eq_two_or_odd with h|h
    · have := cutoff_inside hN₂ hlo; have := Nat.one_le_pow 52 N (by omega); omega
    · exact h
  have hl : Real.log N ≤ Real.log p := Real.log_le_log (by positivity) (by exact_mod_cast hNl)
  have hpℓ := Real.log_nonneg (show (1:ℝ)≤p by exact_mod_cast hp.pos)
  have hlog : 4*A ≤ ε*Real.log p := by
    have he := Real.log_le_log (Real.exp_pos _) (hN₀.le.trans (show (N₀:ℝ)≤N by exact_mod_cast (by omega : N₀≤N)))
    rw [Real.log_exp] at he
    have h := (div_le_iff₀ hε).mp (he.trans hl)
    linarith
  let B := (rationalCone p (N^52) K:ℝ)
  have hU := uniform_approximation hN₂ hK (by omega : K≤N) hlo hhi ho
  rw [show (8:ℝ)*p/Real.pi^2=coeff*p by dsimp [coeff]; ring] at hU
  have hR : |offDiagonal p| ≤ 2300000*(p:ℝ)+(2*(p:ℝ)/K)*(1+Real.log p) + (coeff*p)*|B| := by
    have h := abs_sub_le (offDiagonal p) ((coeff*p)*B) 0
    rw [sub_zero,sub_zero,abs_mul,abs_of_pos (mul_pos hcoeff hpr)] at h
    exact h.trans (add_le_add hU le_rfl)
  have hS : |(S p:ℝ)-(p:ℝ)*Real.log p/2| ≤ C*p + |offDiagonal p| := by
    have h := abs_add_le ((S p:ℝ)-offDiagonal p-(p:ℝ)*Real.log p/2) (offDiagonal p)
    rw [show (S p:ℝ)-offDiagonal p-(p:ℝ)*Real.log p/2+offDiagonal p =
      (S p:ℝ)-(p:ℝ)*Real.log p/2 by ring] at h
    exact h.trans (add_le_add (hdiag p ho) le_rfl)
  have h₁ : ε*Real.log p ≤ A+(2/(K:ℝ))*Real.log p + coeff*|B| := by
    apply le_of_mul_le_mul_right (a:=(p:ℝ)) _ hpr
    change ε*(p:ℝ)*Real.log p ≤ _ at hb
    calc
      _ = ε*(p:ℝ)*Real.log p := by ring
      _ ≤ _ := hb.trans (hS.trans (add_le_add (le_refl (C*(p:ℝ))) hR))
      _ = _ := by dsimp [A]; ring
  have hm := mul_le_mul_of_nonneg_right hκ hpℓ
  rw [cone_interpolation hK hp (cutoff_inside hN₂ hlo),
    ← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs]
  change ε/(2*coeff)*Real.log N ≤ |B|
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  linarith only [h₁,hm,hlog,mul_le_mul_of_nonneg_left hl hε.le]

/-- Primes up to X for which the error from (p/2) log p is at least ε p log p. -/
noncomputable def deviations (ε : ℝ) : ℕ → Finset ℕ := primeSet (bad ε)

/-- Exact membership, written in the original normalized theta sum. -/
theorem deviation_mem {p X : ℕ} {ε : ℝ} :
    p ∈ deviations ε X ↔ p≤X ∧ p.Prime ∧ ε ≤ |(S p:ℝ)/((p:ℝ)*Real.log p)-1/2| := by
  classical
  simp only [deviations,primeSet,mem_filter,Nat.mem_primesLE,and_assoc]
  apply and_congr_right; intro _
  apply and_congr_right; intro hp
  have hlog : 0<Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpos : 0<(p:ℝ)*Real.log p := mul_pos (by exact_mod_cast hp.pos) hlog
  have hp₀ : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
  rw [show (S p:ℝ)/((p:ℝ)*Real.log p)-1/2 =
    ((S p:ℝ)-(p:ℝ)*Real.log p/2)/((p:ℝ)*Real.log p) by field_simp [hp₀,hlog.ne'],
    abs_div,abs_of_pos hpos,le_div_iff₀ hpos]
  unfold bad; rw [mul_assoc]

/-- For every tolerance ε>0 and every X≥2, the two-sided exception count for the
canonical theta sum at primes is at most C(ε) X / (log X)². -/
theorem prime_asymptotic_exception_bound {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X →
      ((deviations ε X).card : ℝ) ≤ C*X/(Real.log X)^2 := by
  obtain ⟨K,hK,δ,hδ,hforce⟩ := forces_cone hε
  have hwindow (d : ℕ) : coneWindow K d ≤ K*d := by unfold coneWindow; split_ifs <;> omega
  exact count_from_variance (bad ε) (fun N => windowExtension (coneWindow K) (2*N^52))
    (window_variance hwindow) ⟨δ,hδ,hforce⟩

/-- S(p)/(p log p) converges in relative prime density to 1/2. -/
theorem prime_density_asymptotic {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun X : ℕ => ((deviations ε X).card:ℝ) / Nat.primeCounting X) atTop (nhds 0) :=
  density_from_count _ (prime_asymptotic_exception_bound hε)

end Arxiv.«2501.03234».ThetaPrimeAsymptotic
#print axioms Arxiv.«2501.03234».ThetaPrimeAsymptotic.deviation_mem
#print axioms Arxiv.«2501.03234».ThetaPrimeAsymptotic.prime_asymptotic_exception_bound
#print axioms Arxiv.«2501.03234».ThetaPrimeAsymptotic.prime_density_asymptotic
#print axioms Arxiv.«2501.03234».ThetaPrimeAsymptotic.cone_interpolation
#print axioms Arxiv.«2501.03234».ThetaPrimeAsymptotic.vanishing_cone_error
#print axioms Arxiv.«2501.03234».ThetaPrimeAsymptotic.uniform_approximation
