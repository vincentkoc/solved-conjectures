import ThetaMovingProgressionMean
import ThetaSiegelWalfiszBand

/-! Uniform signed lower deviations with a moving lcm progression. -/
namespace Arxiv.«2501.03234».ThetaGrowingPrimeExcursions
open Real Finset Filter ThetaIdentityModels ThetaCompactModulus ThetaSiegelWalfiszBand
open ThetaRowProgressionDiscrepancy
noncomputable section

private theorem budgets {L X M t φ κ : ℝ} (hκ : 0<κ) (ht : 1≤t) (hφ : 0<φ)
    (hφt : φ≤t) (hκt : 1≤κ*t) (htL : t≤L) (hL : 12*(1+Z)≤κ*L)
    (hX : 0≤X) (hM : 0≤M) (hbase : κ*X≤M*L) :
    let Y := t^256
    let δ := 2*X/L^520
    let w := M/φ
    δ≤w ∧ Y*(3*Z*(1+log Y)*δ)≤w ∧ X/(L*t^2)≤w := by
  intro Y δ w
  have hz : 0≤Z := tsum_nonneg (fun _ => by positivity)
  have h1 := ht.trans htL
  have hl : 0<L := by linarith
  have ht0 : 0<t := by linarith
  have hy1 : 1≤Y := one_le_pow₀ ht
  have hδ : 0≤δ := by dsimp [δ]; positivity
  have hb : κ*X/(L*t)≤w := by
    apply (div_le_div_iff₀ (mul_pos hl ht0) hφ).mpr
    calc κ*X*φ ≤ (M*L)*t := mul_le_mul hbase hφt hφ.le (mul_nonneg hM hl.le)
         _ = _ := by ring
  have hco : 2≤κ*L := by linarith
  have hY : Y≤L^256 := pow_le_pow_left₀ ht0.le htL _
  have hlog : 1+log Y≤2*L^256 := by linarith [log_le_self (show 0≤Y by linarith)]
  have hc : 3*Z*(1+log Y)≤3*Z*(2*L^256) := mul_le_mul_of_nonneg_left hlog (by positivity)
  have hu : 12*Z≤κ*L := by linarith
  have hg : 2*L*t≤κ*L^520 := calc
    _ ≤ (κ*L)*L*L := mul_le_mul (mul_le_mul_of_nonneg_right hco hl.le) htL ht0.le (by positivity)
    _ = κ*L^3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by decide)) hκ.le
  have hmain : Y*(3*Z*(1+log Y))*2*(L*t)≤κ*L^520 := calc
    _ ≤ L^256*(3*Z*(2*L^256))*2*(L*L) := by
         have hn : 0≤3*Z*(1+log Y) := by have := log_nonneg hy1; positivity
         have h2 : (0:ℝ)≤2 := by norm_num
         have hV := pow_nonneg hl.le 256
         have hmul := mul_le_mul hY hc hn hV
         have hprod := mul_le_mul_of_nonneg_right hmul h2
         have hright := mul_nonneg (mul_nonneg hV (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hz)
           (mul_nonneg h2 hV))) h2
         exact mul_le_mul hprod (mul_le_mul_of_nonneg_left htL hl.le) (mul_nonneg hl.le ht0.le) hright
    _ = (12*Z)*L^514 := by ring
    _ ≤ (κ*L)*L^514 := mul_le_mul_of_nonneg_right hu (by positivity)
    _ = κ*L^515 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by decide)) hκ.le
  refine ⟨le_trans ?_ hb,le_trans ?_ hb,le_trans ?_ hb⟩
  · change 2*X/L^520≤κ*X/(L*t)
    apply (div_le_div_iff₀ (pow_pos hl _) (mul_pos hl ht0)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hg hX]
  · change Y*(3*Z*(1+log Y)*(2*X/L^520))≤κ*X/(L*t)
    rw [←mul_div_assoc,←mul_div_assoc]
    apply (div_le_div_iff₀ (pow_pos hl _) (mul_pos hl ht0)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hmain hX]
  · apply (div_le_div_iff₀ (mul_pos hl (pow_pos ht0 _)) (mul_pos hl ht0)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hκt (mul_nonneg hX (mul_nonneg hl.le ht0.le))]

/-- The threshold in N is uniform in the lcm cutoff T. The refinement
and its signed lower bound hold throughout all bands with m≤log N. -/
theorem uniform (hsw : Ordinary) : ∃ η : ℝ, 0<η ∧ ∃ N₀ : ℕ, ∀ᶠ T : ℕ in atTop,
    ∀ q r : ℕ, 0 < q → r < q → r.Coprime q → Real.log q≤η*Real.log T → ∀ z : ℝ, |z|=1 →
    let m := modulus T
    1 < m ∧ q∣m ∧ ∃ b < m, b.Coprime m ∧ b%q=r ∧ ∀ N≥N₀, (m:ℝ)≤log N →
    (((band N).filter (fun p => p%m=b)).card:ℝ)≤2*((N^64).primeCounting:ℝ)/m.totient ∧
    ((N^64).primeCounting:ℝ)/m.totient*(log T)^2/(16*Real.pi^2) ≤
      ∑ p∈(band N).filter (fun n => n%m=b),z*((S p:ℝ)/p-log p/2) := by
  let κ := log 2/128
  have hκ : 0<κ := div_pos (log_pos (by norm_num)) (by norm_num)
  have ht : Tendsto (fun N : ℕ => log (N:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun N : ℕ => N^64) atTop atTop := tendsto_pow_atTop (by decide)
  have h := (classes hsw 257 520).and ((hp.eventually ThetaPrimeDensity.prime_count_lower).and
    ((log_power 256).and ((ht.eventually_ge_atTop (12*(1+Z)/κ)).and ((ht.eventually_ge_atTop 1).and
     (eventually_ge_atTop (3:ℕ))))))
  obtain ⟨N₀,h₀⟩ := eventually_atTop.mp h
  obtain ⟨η,hη,U⟩ := ThetaMovingProgressionMean.uniform
  refine ⟨η,hη,N₀,?_⟩
  filter_upwards [U,
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/κ),eventually_ge_atTop (1:ℕ)] with T htU htκ ht1
  intro q r hq hr hc hqt z hz
  have H := htU q r hq hr hc hqt z hz
  obtain ⟨hm,hqm,b,hb,hbco,hbr,hband⟩ := H
  let m := modulus T
  have hh : 0 < m := positive T
  have htM : T≤ m := Nat.le_of_dvd hh (contains ht1 le_rfl)
  have hκm : 1≤κ*(m:ℝ) := by
    change 1/κ≤(T:ℝ) at htκ
    have := (div_le_iff₀ hκ).mp (htκ.trans (by exact_mod_cast htM : (T:ℝ)≤ m)); linarith
  refine ⟨hm,hqm,b,hb,hbco,hbr,?_⟩
  intro N hN hmL
  obtain ⟨hcl,hπ,hpow,hlarge,hL,hN3⟩ := h₀ N hN
  let L := log (N:ℝ)
  let M : ℝ := (N^64).primeCounting
  let Y := m^256
  let δ := 2*(N:ℝ)^64/L^520
  have hφ := Nat.totient_pos.mpr hh
  have hbase : κ*(N:ℝ)^64≤M*L := by
    simp only [Nat.cast_pow,log_pow,Nat.cast_ofNat] at hπ
    dsimp [κ,M,L]; linarith only [hπ]
  have hmR : (1:ℝ)≤ m := by exact_mod_cast (show 1≤ m by omega)
  have hY : (Y:ℝ)≤L^256 := by
    change ((m^256:ℕ):ℝ)≤_; rw [Nat.cast_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hmL _
  have hYN : Y≤N := by exact_mod_cast hY.trans hpow
  have hmY : m≤Y := Nat.le_self_pow (by decide) m
  have hcl' {d : ℕ} (hd : 0<d) (hdy : d≤Y) : Classes (band N) (m*d) M δ := by
    apply hcl _ (Nat.mul_pos hh hd)
    rw [Nat.cast_mul]
    calc _ ≤ L*L^256 := mul_le_mul hmL ((Nat.cast_le.mpr hdy).trans hY) (Nat.cast_nonneg _) (by linarith only [hL])
         _ = _ := by dsimp [L]; ring
  have h1 := hcl' (by decide : 0<1) (show 1≤Y by omega)
  rw [mul_one] at h1
  have hd := budgets (t:=(m:ℝ)) hκ hmR (show 0<(m.totient:ℝ) by exact_mod_cast hφ)
    (by exact_mod_cast Nat.totient_le m) hκm hmL ((div_le_iff₀ hκ).mp hlarge |> fun H => by linarith)
    (show 0≤(N:ℝ)^64 by positivity) (show 0≤M from Nat.cast_nonneg _) hbase
  obtain ⟨hd₁,hd₂,hd₃⟩ := hd
  have hcast : (Y:ℝ)=(m:ℝ)^256 := Nat.cast_pow ..
  have hYpow : (Y:ℝ)^(1/128:ℝ)=(m:ℝ)^2 := by
    rw [hcast,←rpow_natCast_mul (Nat.cast_nonneg m)]; norm_num
  constructor
  · have hcnt := (abs_le.mp (h1 b hb)).2
    rw [if_pos hbco] at hcnt
    change _ ≤ 2*M/m.totient
    rw [mul_div_assoc]
    linarith only [hcnt,hd₁]
  apply hband (band N) (by omega) hmY hYN (Nat.cast_nonneg _) (by dsimp [δ,L]; positivity)
    (fun p hp => mem_band.mp hp) h1 (fun d h => hcl' (by have := (mem_Icc.mp h).1; omega) (mem_Icc.mp h).2) hd₁
  · simpa only [hcast] using hd₂
  · simpa only [hYpow] using hd₃

#print axioms uniform
end
end Arxiv.«2501.03234».ThetaGrowingPrimeExcursions
