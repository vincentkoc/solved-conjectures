import ThetaFiniteLowerTail

/-! Lower bounds on finite positive and negative prime moments, uniformly in
the moment order and endpoint, under ordinary Siegel--Walfisz. -/
namespace Arxiv.«2501.03234».ThetaFiniteLowerMoments
open Filter Finset Real ThetaFiniteLowerTail ThetaSiegelWalfiszBand
noncomputable section

private theorem cost_le {h : ℝ} (hh : 4≤h) : cost h≤exp (4*h) := by
  have hh₀ : 0≤3*h := by linarith
  have H := pow_div_factorial_le_exp _ hh₀ 2
  norm_num at H
  have hc : 48≤exp (3*h) := by nlinarith only [H,hh,mul_nonneg (show 0≤h-4 by linarith) (show 0≤h+4 by linarith)]
  calc cost h = 48*exp h := rfl
       _ ≤ exp (3*h)*exp h := mul_le_mul_of_nonneg_right hc (exp_pos _).le
       _ = _ := by rw [←exp_add]; congr 1; ring

def oneSidedMoment (q r : ℕ) (z : ℝ) (X k : ℕ) :=
  ∑ p∈(Nat.primesLE X).filter (fun p => p%q=r),(max 0 (z*((S p:ℝ)/p-log p/2)))^k

/-- The empirical moment root is at least a constant times the squared
minimum of log k and log log log X. The normalization counts all primes. -/
theorem original (hsw : Ordinary) : ∃ c δ : ℝ, 0<c ∧ 0<δ ∧ ∃ k₀ : ℕ,
    ∀ᶠ X : ℕ in atTop, ∀ k≥k₀, ∀ q r : ℕ, 0 < q → r < q → r.Coprime q →
      log q≤δ*min (log k) (log (log (log X))) → ∀ z : ℝ, |z|=1 →
      (X.primeCounting:ℝ)*(c*(min (log k) (log (log (log X))))^2)^k≤oneSidedMoment q r z X k := by
  obtain ⟨γ,η,H₀,hγ,hη,h₀⟩ := ThetaFiniteLowerTail.original hsw
  let c := exp (-2)/(4096*Real.pi^2)
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨c,η/8,hc,by positivity,?_⟩
  let A := max 4 H₀
  have h₁ := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h₂ := tendsto_log_atTop.comp h₁
  have h₃ := tendsto_log_atTop.comp h₂
  obtain ⟨k₀,hk₀⟩ := eventually_atTop.mp ((h₁.eventually_ge_atTop (8*A)).and
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (-log γ)))
  refine ⟨k₀,?_⟩
  filter_upwards [h₀,h₃.eventually_ge_atTop (8*A),h₂.eventually_ge_atTop (2*log 128),
    h₂.eventually_gt_atTop 0,h₁.eventually_gt_atTop 0] with X hx hX hl₁ hl₂ hl₃
  intro k hk q r hq hr hqr hqt z hz
  obtain ⟨hkl,hkγ⟩ := hk₀ k hk
  let L := log (log (X:ℝ))
  let t := min (log (k:ℝ)) (log L)
  let h := t/8
  have hAt : 8*A≤t := le_min hkl hX
  have h4 : 4≤h := by dsimp [h]; linarith only [hAt,le_max_left 4 H₀]
  have hH : H₀≤h := by dsimp [h]; linarith only [hAt,le_max_right 4 H₀]
  have hkp : 0<(k:ℝ) := by
    by_contra! he
    have h := le_antisymm he (Nat.cast_nonneg (α:=ℝ) k)
    change 8*A≤log (k:ℝ) at hkl
    rw [h,log_zero] at hkl; linarith only [hkl,le_max_left 4 H₀]
  have h8 : exp (8*h)≤L := by
    rw [←exp_log (show 0<L from hl₂)]
    apply exp_le_exp.mpr; dsimp only [h]; linarith only [min_le_right (log (k:ℝ)) (log L)]
  have h8k : exp (8*h)≤k := by
    rw [←exp_log hkp]; apply exp_le_exp.mpr
    change 8*(min (log (↑k:ℝ)) (log L)/8)≤log (↑k:ℝ)
    linarith only [min_le_left (log (k:ℝ)) (log L)]
  have hbig : 2≤exp (4*h) := by linarith only [add_one_le_exp (4*h),h4]
  have hsq : exp (4*h)*exp (4*h)=exp (8*h) := by rw [←exp_add]; congr 1; ring
  have hU := cost_le h4
  have hL : 2*cost h≤L := by
    nlinarith only [hU,mul_le_mul_of_nonneg_right hbig (exp_pos (4*h)).le,hsq,h8]
  have hcost : cost h≤k := hU.trans ((exp_le_exp.mpr (by linarith only [h4] : 4*h≤8*h)).trans h8k)
  have hfit : 128*exp (cost h)≤log X := by
    rw [←exp_log (by norm_num : (0:ℝ)<128),←exp_add,←exp_log (show 0<log (X:ℝ) from hl₃)]
    apply exp_le_exp.mpr; change log 128+cost h≤L
    change 2*log 128≤L at hl₁; linarith
  let G := excursions q r z h X
  let M : ℝ := X.primeCounting
  let a := h^2/(64*Real.pi^2)
  have ha : 0≤a := by dsimp [a]; positivity
  have hG := hx h hH hfit q r hq hr hqr (by dsimp only [h,t,L]; linarith only [hqt]) z hz
  have hg : exp (-(k:ℝ))≤γ := by rw [←exp_log hγ]; apply exp_le_exp.mpr; linarith only [hkγ]
  have hfrac : M*(exp (-2))^k≤(G.card:ℝ) := by
    calc _ = M*exp (-k:ℝ)*exp (-k:ℝ) := by
              rw [←exp_nat_mul, mul_assoc,←exp_add]; congr 2; ring
         _ ≤ M*γ*exp (-cost h) := mul_le_mul (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _))
              (exp_le_exp.mpr (neg_le_neg hcost)) (exp_pos _).le (by dsimp [M]; positivity)
         _ ≤ _ := by simpa only [mul_comm M γ] using hG
  have hsub : G⊆(Nat.primesLE X).filter (fun p => p%q=r) := fun p hp =>
    mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.1⟩
  have hscale : c*t^2=exp (-2)*a := by dsimp [c,a,h]; ring
  change M*(c*t^2)^k≤_
  rw [hscale,mul_pow,←mul_assoc]
  apply (mul_le_mul_of_nonneg_right hfrac (pow_nonneg ha _)).trans
  change (G.card:ℝ)*a^k≤_
  rw [←nsmul_eq_mul,←sum_const]
  apply (sum_le_sum (s:=G) (g:=fun p => (max 0 (z*((S p:ℝ)/p-log p/2)))^k) (fun p hp =>
    pow_le_pow_left₀ ha ((mem_filter.mp hp).2.2.trans (le_max_right ..)) _)).trans
  exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg (le_max_left ..) _)

#print axioms original

/-- For any fixed power of log log X, all sufficiently large orders through
that power have matching logarithmic-square upper and lower root growth. -/
theorem matching (hsw : Ordinary) : ∃ C : ℝ, 0<C ∧ ∀ {A : ℝ}, 0<A →
    ∃ c θ : ℝ, 0<c ∧ 0<θ ∧ ∃ k₀ : ℕ, ∀ᶠ X : ℕ in atTop,
    ∀ k≥k₀, (k:ℝ)≤(log (log X))^A → ∀ q r : ℕ, 0 < q → r < q → r.Coprime q →
      log q≤θ*log k → ∀ z : ℝ, |z|=1 →
      (X.primeCounting:ℝ)*(c*(1+log k)^2)^k≤oneSidedMoment q r z X k ∧
      oneSidedMoment q r z X k≤(X.primeCounting:ℝ)*(C*(1+log k)^2)^k := by
  obtain ⟨C,hC,hup⟩ := ThetaEmpiricalPrimeMoments.logarithmic
  obtain ⟨b,δ,hb,hδ,k₀,h⟩ := original hsw
  refine ⟨C,hC,?_⟩
  intro A hA
  let B := max 1 A
  have hB : 0<B := lt_of_lt_of_le (by norm_num) (le_max_left ..)
  refine ⟨b/(4*B^2),δ/B,by positivity,div_pos hδ hB,?_⟩
  have h₁ := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h₂ := tendsto_log_atTop.comp h₁
  obtain ⟨k₁,hk₁⟩ := eventually_atTop.mp (h₁.eventually_ge_atTop (1:ℝ))
  refine ⟨max (max k₀ k₁) 1,?_⟩
  have hpow := h₁.eventually ((isLittleO_log_rpow_rpow_atTop (2*A) (by norm_num : (0:ℝ)<1)).bound
    (by norm_num : (0:ℝ)<1))
  filter_upwards [h,hup,hpow,h₂.eventually_ge_atTop 1,h₁.eventually_gt_atTop 0] with X H U hpow hll hl
  intro k hk hkA q r hq hr hc hqt z hz
  let L := log (log (X:ℝ))
  have hk₀ := ((le_max_left k₀ k₁).trans (le_max_left _ _)).trans hk
  have hk' := (le_max_right _ _).trans hk
  have hkl := hk₁ k (((le_max_right k₀ k₁).trans (le_max_left _ _)).trans hk)
  change 1≤log (k:ℝ) at hkl
  have hkp : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hll
  have hlp : 0<log (X:ℝ) := hl
  have hh : L^(2*A)≤log X := by
    simpa only [rpow_one,one_mul,Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos hLp _),abs_of_pos hlp,L,Function.comp_apply] using hpow
  have hlim : (k:ℝ)^2≤log X*(1+log k) := by
    calc _ ≤ (L^A)^2 := pow_le_pow_left₀ hkp.le hkA _
         _ = L^(2*A) := by rw [←rpow_mul_natCast hLp.le]; norm_num; ring_nf
         _ ≤ _ := hh.trans (le_mul_of_one_le_right hlp.le (by linarith))
  have hlog := log_le_log hkp hkA
  rw [log_rpow hLp] at hlog
  have hn := log_nonneg (show 1≤L from hll)
  have hmax : log (k:ℝ)≤B*min (log k) (log L) := by
    by_cases hf : log (k:ℝ)≤log L
    · rw [min_eq_left hf]; exact le_mul_of_one_le_left (by linarith) (le_max_left ..)
    · rw [min_eq_right (le_of_not_ge hf)]
      exact hlog.trans (mul_le_mul_of_nonneg_right (le_max_right ..) hn)
  have hcut : b/(4*B^2)*(1+log k)^2≤b*(min (log k) (log L))^2 := by
    have h' := pow_le_pow_left₀ (by linarith : 0≤1+log (k:ℝ))
      (show 1+log k≤2*(B*min (log k) (log L)) by linarith only [hkl,hmax]) 2
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left h' hb.le]
  have hmod : log q≤δ*min (log k) (log L) := by
    apply hqt.trans
    rw [div_mul_eq_mul_div,div_le_iff₀ hB]
    nlinarith only [mul_le_mul_of_nonneg_left hmax hδ.le]
  refine ⟨(mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hcut _) (Nat.cast_nonneg _)).trans
    (H k hk₀ q r hq hr hc hmod z hz),?_⟩
  have he := U k hk' hlim
  apply le_trans _ he
  unfold oneSidedMoment
  apply (sum_le_sum (g:=fun p => |(S p:ℝ)/p-log p/2|^k) (fun p _ => ?_)).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => pow_nonneg (abs_nonneg _) _))
  apply pow_le_pow_left₀ (le_max_left ..) (max_le (abs_nonneg _) _) _
  calc _ ≤ |z*((S p:ℝ)/p-log p/2)| := le_abs_self _
       _ = _ := by rw [abs_mul,hz,one_mul]

#print axioms matching
end
end Arxiv.«2501.03234».ThetaFiniteLowerMoments
