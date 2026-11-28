import ThetaGrowingExcursionCounts

/-! Double-exponential lower bounds on moving signed deviations at finite endpoints. -/
namespace Arxiv.«2501.03234».ThetaFiniteLowerTail
open Real Finset Filter ThetaCompactModulus ThetaSiegelWalfiszBand
noncomputable section

def cost (h : ℝ) := 48*exp h

/-- Choose a compact modulus for a requested real height after any fixed cutoff. -/
theorem choose_height (P : ℕ → Prop) (H : ∀ᶠ T in atTop,P T) :
    ∀ᶠ h : ℝ in atTop, ∃ T : ℕ, P T ∧ 0≤h ∧ h≤log (T:ℝ) ∧
      (modulus T:ℝ)≤exp (cost h) := by
  have ht : Tendsto (fun h : ℝ => ⌈exp h⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp tendsto_exp_atTop
  filter_upwards [ht.eventually H,eventually_ge_atTop (0:ℝ)] with h hP hh
  let T := ⌈exp h⌉₊
  have h1 := one_le_exp hh
  have hlow : exp h≤(T:ℝ) := Nat.le_ceil _
  have hpos : 0<(T:ℝ) := (exp_pos _).trans_le hlow
  have hu : (T:ℝ)≤2*exp h := by
    have hh' := Nat.ceil_lt_add_one (exp_pos h).le
    change (T:ℝ)<exp h+1 at hh'
    linarith
  have hlog := log_le_log (exp_pos h) hlow
  rw [log_exp] at hlog
  refine ⟨T,hP,hh,hlog,?_⟩
  rw [←exp_log (show 0<(modulus T:ℝ) by exact_mod_cast positive T)]
  apply exp_le_exp.mpr
  have h4 : log (4:ℝ)≤2 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow]
    norm_num only [Nat.cast_ofNat]; linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hb := mul_le_mul_of_nonneg_right (show 4*(log 4+4)≤24 by linarith) hpos.le
  unfold cost
  linarith only [size T,hb,hu]

private theorem root :
    ∃ d : ℝ, 0<d ∧ ∀ᶠ X : ℕ in atTop, let N := Nat.nthRoot 64 X
      2≤N ∧ N^64≤X ∧ d*X.primeCounting≤(N^64).primeCounting ∧ log (X:ℝ)≤128*log N := by
  let κ := log 2/(2*(log 4+1)*(2:ℝ)^64)
  have hl2 := log_pos (by norm_num : (1:ℝ)<2)
  have hl4 := log_pos (by norm_num : (1:ℝ)<4)
  have hκ : 0<κ := by dsimp [κ]; positivity
  have hlim : Tendsto (Nat.nthRoot 64) atTop atTop := tendsto_atTop.mpr (fun a =>
    (eventually_ge_atTop (a^64)).mono fun X h => (Nat.le_nthRoot_iff (by decide)).mpr h)
  have hp := ((tendsto_pow_atTop (n:=64) (by decide)).comp hlim).eventually ThetaPrimeDensity.prime_count_lower
  have hu := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Chebyshev.eventually_primeCounting_le zero_lt_one)
  simp only [Nat.floor_natCast] at hu
  refine ⟨κ,hκ,?_⟩
  filter_upwards [hp,hu,hlim.eventually_ge_atTop 2] with X hπ hU h₂
  let N := Nat.nthRoot 64 X
  have hN : 2≤N := h₂
  have hlow : N^64≤X := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hhi : X≤2^64*N^64 := calc
    X ≤ (N+1)^64 := (Nat.lt_pow_nthRoot_add_one (by decide) X).le
    _ ≤ (2*N)^64 := Nat.pow_le_pow_left (by omega) _
    _ = _ := Nat.mul_pow ..
  have hh : (X:ℝ)≤(2:ℝ)^64*(N:ℝ)^64 := by exact_mod_cast hhi
  have hn : (2:ℝ)≤N := by exact_mod_cast hN
  have hnp : 0<(N:ℝ) := by linarith
  have hx : 0<(X:ℝ) := lt_of_lt_of_le (pow_pos hnp 64) (by exact_mod_cast hlow)
  have hlog := log_le_log hx hh
  rw [log_mul (by positivity) (by positivity),log_pow,log_pow] at hlog
  have hln := log_le_log (by norm_num : (0:ℝ)<2) hn
  have hxl := log_le_log (pow_pos hnp 64) (show (N:ℝ)^64≤X by exact_mod_cast hlow)
  rw [log_pow] at hxl
  have hxl' := log_pos (lt_of_lt_of_le (one_lt_pow₀ (by linarith only [hn] : (1:ℝ)<N) (by decide : (64:ℕ)≠0))
     (by exact_mod_cast hlow : (N:ℝ)^64≤X))
  refine ⟨hN,hlow,?_,by norm_num at hlog; linarith⟩
  have hupper := (le_div_iff₀ hxl').mp hU
  change log 2/2*(N^64:ℕ)≤(N^64).primeCounting*log (N^64:ℕ) at hπ
  simp only [Nat.cast_pow,log_pow,Nat.cast_ofNat] at hπ hxl
  have hbound : log 2/2*(N:ℝ)^64≤(N^64).primeCounting*log X :=
    hπ.trans (mul_le_mul_of_nonneg_left hxl (Nat.cast_nonneg _))
  apply (mul_le_mul_iff_left₀ hxl').mp
  calc κ*X.primeCounting*log X≤κ*((log 4+1)*(2^64*(N:ℝ)^64)) := by
          rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hκ.le
          exact hupper.trans (mul_le_mul_of_nonneg_left hh (by positivity))
       _ = log 2/2*(N:ℝ)^64 := by dsimp [κ]; field_simp
       _ ≤ _ := hbound

def excursions (q r : ℕ) (z h : ℝ) (X : ℕ) :=
  (Nat.primesLE X).filter (fun p => p%q=r ∧ h^2/(64*Real.pi^2)≤z*((S p:ℝ)/p-log p/2))

/-- At every sufficiently large endpoint, simultaneously over the stated
heights, the original signed residual has a double-exponential lower bound on either tail
in all reduced progressions with log q ≤ ηh. Only ordinary Siegel--Walfisz is assumed. -/
theorem original (hsw : Ordinary) : ∃ γ η H : ℝ, 0<γ ∧ 0<η ∧ ∀ᶠ X : ℕ in atTop,
    ∀ h≥H, 128*exp (cost h)≤log X → ∀ q r : ℕ, 0 < q → r < q → r.Coprime q →
    log q≤η*h → ∀ z : ℝ, |z|=1 →
    γ*X.primeCounting*exp (-(cost h))≤((excursions q r z h X).card:ℝ) := by
  obtain ⟨β,η,hβ,hη,N₀,hT⟩ := ThetaGrowingExcursionCounts.uniform hsw
  obtain ⟨d,hd,hr₀⟩ := root
  obtain ⟨H,hh₀⟩ := eventually_atTop.mp (choose_height _ hT)
  refine ⟨β*d,η,H,mul_pos hβ hd,hη,?_⟩
  filter_upwards [hr₀,eventually_ge_atTop (N₀^64)] with X hroot hx
  let N := Nat.nthRoot 64 X
  obtain ⟨hn,hl,hπ,hL⟩ := hroot
  have hN : N₀≤N := (Nat.le_nthRoot_iff (by decide : (64:ℕ)≠0)).mpr hx
  intro h hh hfit q r hq hr hc hqz z hz
  obtain ⟨T,hT,hhp,ht,hsize⟩ := hh₀ h hh
  obtain ⟨hm,hqm,b,hb,hbc,hbr,hg⟩ := hT q r hq hr hc (hqz.trans (mul_le_mul_of_nonneg_left ht hη.le)) z hz
  let m := modulus T
  have hmL : (m:ℝ)≤log N := by
    change log (X:ℝ)≤128*log (N:ℝ) at hL
    linarith only [hsize,hfit,hL]
  have hg' := hg N hN hmL
  let G := (band N).filter (fun p => p%m=b ∧ (log T)^2/(64*Real.pi^2)≤z*((S p:ℝ)/p-log p/2))
  have hsub : G⊆excursions q r z h X := by
    intro p hp; obtain ⟨hx,hb',he⟩ := mem_filter.mp hp
    obtain ⟨hpr,_,hhi⟩ := mem_band.mp hx
    refine mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hhi.trans hl,hpr⟩,?_,?_⟩
    · rw [←Nat.mod_mod_of_dvd p hqm,hb',hbr]
    · exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ hhp ht _) (by positivity)).trans he
  have hhφ : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (show 0 < m by omega)
  have hmass : exp (-cost h)≤1/(m.totient:ℝ) := by
    rw [exp_neg,←one_div]; exact one_div_le_one_div_of_le hhφ ((Nat.cast_le.mpr (Nat.totient_le m)).trans hsize)
  calc β*d*X.primeCounting*exp (-cost h) ≤ (β*(N^64).primeCounting)*(1/(m.totient:ℝ)) := by
          exact mul_le_mul (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hπ hβ.le)
            hmass (exp_pos _).le (by positivity)
       _ = β*(N^64).primeCounting/m.totient := by ring
       _ ≤ (G.card:ℝ) := hg'
       _ ≤ _ := Nat.cast_le.mpr (card_le_card hsub)

#print axioms choose_height
#print axioms original

/-- Both tails are attained at a height within a constant of log log log X
in all the stated reduced classes, with at most a log-power loss in prime count. -/
theorem edge (hsw : Ordinary) : ∃ γ η : ℝ, 0<γ ∧ 0<η ∧ ∀ {ε : ℝ}, 0<ε →
    ∃ b : ℝ, 0≤b ∧ ∀ᶠ X : ℕ in atTop,
    let h := log (log (log X))-b
    ∀ q r : ℕ, 0 < q → r < q → r.Coprime q → log q≤η*h → ∀ z : ℝ, |z|=1 →
    γ*X.primeCounting/(log X)^ε≤((excursions q r z h X).card:ℝ) := by
  obtain ⟨γ,η,H,hγ,hη,h₀⟩ := original hsw
  refine ⟨γ,η,hγ,hη,?_⟩
  intro ε heps
  let M := max 96 (48/ε)
  have hM : 0<M := lt_of_lt_of_le (by norm_num : (0:ℝ)<96) (le_max_left ..)
  let b := log M
  refine ⟨b,log_nonneg (le_trans (by norm_num : (1:ℝ)≤96) (le_max_left ..)),?_⟩
  have h₁ := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h₂ := tendsto_log_atTop.comp h₁
  have h₃ := tendsto_log_atTop.comp h₂
  filter_upwards [h₀,h₃.eventually_ge_atTop (H+b),h₂.eventually_ge_atTop (2*log 128),
    h₂.eventually_gt_atTop 0,h₁.eventually_gt_atTop 0] with X hx hH hfit hL hl
  let L := log (log (X:ℝ))
  let h := log L-b
  intro _ q r hq hr hc hqt z hz
  have hH' : H≤h := by change H+b≤log L at hH; dsimp only [h]; linarith only [hH]
  have heq : cost h=48/M*L := by
    unfold cost h b; rw [exp_sub,exp_log (show 0<L from hL),exp_log hM]; ring
  have hhalf : 48/M≤1/2 := (div_le_iff₀ hM).mpr (by linarith only [le_max_left (96:ℝ) (48/ε)])
  have heps' : 48/M≤ε := (div_le_iff₀ hM).mpr (by
    have h := (div_le_iff₀ heps).mp (le_max_right (96:ℝ) (48/ε)); dsimp only [M]; linarith only [h])
  have hf : 128*exp (cost h)≤log X := by
    rw [←exp_log (by norm_num : (0:ℝ)<128),←exp_add,←exp_log (show 0<log (X:ℝ) from hl)]
    apply exp_le_exp.mpr
    change 2*log 128≤L at hfit; change log 128+cost h≤L
    rw [heq]; linarith only [mul_le_mul_of_nonneg_right hhalf (show 0≤L from le_of_lt hL),hfit]
  have hlow := hx h hH' hf q r hq hr hc hqt z hz
  refine le_trans ?_ hlow
  rw [rpow_def_of_pos (show 0<log (X:ℝ) from hl),div_eq_mul_inv,←exp_neg]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hγ.le (Nat.cast_nonneg _))
  apply exp_le_exp.mpr; change -(L*ε)≤ -cost h
  rw [heq]; linarith only [mul_le_mul_of_nonneg_right heps' (show 0≤L from le_of_lt hL)]

#print axioms edge
end
end Arxiv.«2501.03234».ThetaFiniteLowerTail
