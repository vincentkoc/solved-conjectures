import ThetaLocalExcursionBudgets
import ThetaWeilShortIntervals

/-! Excursions of the original signed residual on both sides of its leading
term in every sufficiently late short interval. -/
namespace Arxiv.«2501.03234».ThetaLocalSignedExcursions
open Real Finset Filter ThetaIdentityModels ThetaCompactModulus ThetaPrimeTailTransfer
open ThetaLocalPrimeCounts ThetaLocalExcursionScales ThetaRowProgressionDiscrepancy
open ThetaShortPrimeInterval ThetaCalibratedCone
noncomputable section

def excursions (X H q r : ℕ) (z h : ℝ) := (sample X H).filter (fun p =>
  p%q=r ∧ h^2/(64*π^2)≤z*((S p:ℝ)/p-log p/2))

/-- One residue refining each requested class works in every admitted window.
Its choice and the starting endpoint are independent of one another. -/
theorem refinement {e : ℕ} (he : 32≤e) (he' : e≤48) (kernel : Kernel e)
    {θ : ℝ} (hθ : (e:ℝ)/64<θ) (ordinary : Ordinary θ) :
    ∃ η : ℝ, 0<η ∧ ∃ X₀ : ℕ, ∀ᶠ T : ℕ in atTop,
    ∀ q r : ℕ, 0 < q → r < q → r.Coprime q → log q≤η*log T → ∀ z : ℝ, |z|=1 →
    let m := modulus T
    1 < m ∧ q∣m ∧ ∃ b < m, b.Coprime m ∧ b%q=r ∧ ∀ X≥X₀, ∀ H : ℕ, H≤X →
      (X:ℝ)^θ≤H → (m:ℝ)≤log X →
      (H:ℝ)/(2*log X*m.totient*height X)≤((excursions X H m b z (log T)).card:ℝ) := by
  obtain ⟨D,B,hD,hB,herror⟩ := ThetaLocalModelError.exceptions he he' kernel
  obtain ⟨X₀,h₀⟩ := eventually_atTop.mp ((ThetaLocalExcursionBudgets.eventual hθ hB).and
    ((classes ordinary 1025 1030).and (eventually_ge_atTop (2:ℕ))))
  obtain ⟨η,hη,hmodel⟩ := ThetaReflectedWindowMeans.uniform
  let c := 8/π^2
  have hc : 0<c := by dsimp [c]; positivity
  have ht := (tendsto_pow_atTop (n:=2) (by decide)).comp
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  refine ⟨η,hη,X₀,?_⟩
  filter_upwards [hmodel,ht.eventually_ge_atTop (max 512 (512*D/c))] with T hm hbig
  intro q r hq hr hqr hqt z hz
  obtain ⟨hm₁,hqm,b,hb,hbc,hbr,hu⟩ := hm q r hq hr hqr hqt z hz
  let m := modulus T
  have hmp : 0 < m := positive T
  refine ⟨hm₁,hqm,b,hb,hbc,hbr,?_⟩
  intro X hX H hHX hlen hmL
  obtain ⟨⟨N,hn,hlo,hhi,hyn,hbud⟩,hcl,h2⟩ := h₀ X hX
  let Y := ThetaLocalExcursionScales.cutoff X
  let L := log (X:ℝ)
  have hl : 0<L := log_pos (by exact_mod_cast (show 1<X by omega))
  let s := sample X H
  let w := ThetaLocalPrimeCounts.mass X H/m.totient
  let δ := (H:ℝ)/L^1030
  have Hbud := hbud H hHX hlen m hmp hmL
  obtain ⟨hy,hmy,hmn,hd,hrow,hcost,hmods⟩ := Hbud
  have cl (d : ℕ) (hd : d≤Y) (hp : 0<d) : Classes s (m*d) (ThetaLocalPrimeCounts.mass X H) δ :=
    hcl H hHX hlen _ (Nat.mul_pos hmp hp) (hmods d hd)
  have hmcl := cl 1 (by change 1≤ThetaLocalExcursionScales.cutoff X; omega) (by decide)
  rw [mul_one] at hmcl
  let R (p : ℕ) := (S p:ℝ)/p-log p/2
  have hE := herror hn hy hyn (X+1) H s (fun p hp => by
    obtain ⟨hI,hpr,_⟩ := mem_primes.mp hp
    obtain ⟨h₁,h₂⟩ := mem_Ioc.mp hI
    exact ⟨by omega,by omega,hpr,by omega,by omega⟩)
  have hv := (le_max_left (512:ℝ) (512*D/c)).trans hbig
  have hDv : D≤c*(log T)^2/512 := by
    have hh := (div_le_iff₀ hc).mp ((le_max_right (512:ℝ) (512*D/c)).trans hbig)
    change 512*D≤(log (T:ℝ))^2*c at hh; linarith
  have hM := mass_lower h2 hHX
  have hM0 : 0≤ThetaLocalPrimeCounts.mass X H := (show 0≤(H:ℝ)/(2*log X) by change 0≤(H:ℝ)/(2*L); positivity).trans hM
  have h := ThetaLocalExcursionCount.finite (s:=s) (N:=N) hmp hb hbc hmy hM0 (show 0≤δ by dsimp [δ]; positivity)
    hz hv hDv hmcl (fun d hd => cl d (mem_Icc.mp hd).2 (lt_of_lt_of_le (by decide) (mem_Icc.mp hd).1))
    hd hrow (hu Y hmy N hmn) hE hcost
  have hZ : 1≤Z := (weight_one (by decide : 0<1) (le_refl 1)).trans (ThetaReciprocalBlocks.commonWeight_bounds 1 1).2
  have hLg := log_nonneg (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega))
  have hU : 0≤height X := by change 0≤3*Z*(1+log Y)^2; positivity
  refine le_trans ?_ h
  change (H:ℝ)/(2*log X*m.totient*height X)≤(ThetaLocalPrimeCounts.mass X H/m.totient)/height X
  rw [←div_div,←div_div]
  exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hM (Nat.cast_nonneg _)) hU

#print axioms refinement
end
end Arxiv.«2501.03234».ThetaLocalSignedExcursions
