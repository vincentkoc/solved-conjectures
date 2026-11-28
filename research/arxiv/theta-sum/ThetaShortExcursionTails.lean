import ThetaLocalSignedExcursions
import ThetaFiniteLowerTail

/-! Both signed excursions at the triple-logarithmic height in every short
interval and every reduced class in the indicated growing range. -/
namespace Arxiv.«2501.03234».ThetaShortExcursionTails
open Real Filter Finset ThetaCalibratedCone ThetaLocalPrimeCounts ThetaLocalExcursionScales
open ThetaLocalSignedExcursions ThetaCompactModulus
open ThetaFiniteLowerTail (cost choose_height)
noncomputable section

theorem finite {e : ℕ} (he : 32≤e) (he' : e≤48) (kernel : Kernel e)
    {θ : ℝ} (hθ : (e:ℝ)/64<θ) (ordinary : Ordinary θ) :
    ∃ η H₀ : ℝ, 0<η ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
    ∀ h≥H₀, exp (cost h)≤log X → ∀ q r : ℕ, 0 < q → r < q → r.Coprime q →
      log q≤η*h → ∀ z : ℝ, |z|=1 →
      (H:ℝ)/(2*log X*exp (cost h)*height X)≤((excursions X H q r z h).card:ℝ) := by
  obtain ⟨η,hη,X₀,hT⟩ := refinement he he' kernel hθ ordinary
  obtain ⟨H₀,hchoose⟩ := eventually_atTop.mp (choose_height _ hT)
  refine ⟨η,H₀,hη,?_⟩
  filter_upwards [eventually_ge_atTop (max X₀ 3),cutoff_bounds] with X hx hY
  intro H hHX hlen h hh hfit q r hq hr hqr hqz z hz
  obtain ⟨T,hT,h₀,ht,hm⟩ := hchoose h hh
  obtain ⟨hm1,hqm,b,hb,hbc,hbr,hh⟩ := hT q r hq hr hqr (hqz.trans (mul_le_mul_of_nonneg_left ht hη.le)) z hz
  let m := modulus T
  have hlow := hh X ((le_max_left ..).trans hx) H hHX hlen (hm.trans hfit)
  have sub : excursions X H m b z (log T)⊆excursions X H q r z h := by
    intro p hp; obtain ⟨hpr,hb',hgt⟩ := mem_filter.mp hp
    refine mem_filter.mpr ⟨hpr,?_,(div_le_div_of_nonneg_right (pow_le_pow_left₀ h₀ ht _) (by positivity)).trans hgt⟩
    rw [←Nat.mod_mod_of_dvd p hqm,hb',hbr]
  have hy : 2≤ThetaLocalExcursionScales.cutoff X := hY.1
  have hZ : 1≤ThetaIdentityModels.Z := (ThetaIdentityModels.weight_one (by decide : 0<1) (le_refl 1)).trans
    (ThetaReciprocalBlocks.commonWeight_bounds 1 1).2
  have hlg := log_nonneg (show (1:ℝ)≤ThetaLocalExcursionScales.cutoff X by exact_mod_cast (show 1≤ThetaLocalExcursionScales.cutoff X by omega))
  have hU : 0<height X := by unfold height; positivity
  have hφ : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (positive T)
  have hl : 0<log (X:ℝ) := log_pos (by exact_mod_cast (show 1<X by omega))
  apply le_trans _ (hlow.trans (Nat.cast_le.mpr (card_le_card sub)))
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
  apply mul_le_mul_of_nonneg_right _ hU.le
  exact mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (Nat.totient_le m)).trans hm) (by positivity)

def Edge (θ : ℝ) := ∃ η : ℝ, 0<η ∧ ∀ {ε : ℝ}, 0<ε → ∃ b : ℝ, 0≤b ∧
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
      let h := log (log (log X))-b
      ∀ q r : ℕ, 0 < q → r < q → r.Coprime q → log q≤η*h → ∀ z : ℝ, |z|=1 →
      (H:ℝ)/(2*(log X)^(1+ε))≤((excursions X H q r z h).card:ℝ)

theorem edge {e : ℕ} (he : 32≤e) (he' : e≤48) (kernel : Kernel e)
    {θ : ℝ} (hθ : (e:ℝ)/64<θ) (ordinary : Ordinary θ) : Edge θ := by
  obtain ⟨η,H₀,hη,h₀⟩ := finite he he' kernel hθ ordinary
  refine ⟨η,hη,?_⟩
  intro ε hε
  let M := max 48 (96/ε)
  have hM : 0<M := lt_of_lt_of_le (by norm_num : (0:ℝ)<48) (le_max_left ..)
  let b := log M
  refine ⟨b,log_nonneg (le_trans (by norm_num : (1:ℝ)≤48) (le_max_left ..)),?_⟩
  have h₁ := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h₂ := tendsto_log_atTop.comp h₁
  have h₃ := tendsto_log_atTop.comp h₂
  filter_upwards [h₀,h₃.eventually_ge_atTop (H₀+b),h₂.eventually_gt_atTop 0,
    h₁.eventually_ge_atTop 1,height_small (half_pos hε),cutoff_bounds] with X hwin hH hlog hx hU hY
  intro H hHX hlen h q r hq hr hqr hqz z hz
  let L := log (X:ℝ)
  have h1 : 1≤L := hx
  have hl : 0<L := lt_of_lt_of_le (by norm_num) h1
  have hh : H₀≤h := by change H₀+b≤log (log L) at hH; change H₀≤log (log L)-b; linarith only [hH]
  have heq : exp (cost h)=L^(48/M) := by
    change exp (48*exp (log (log L)-log M))=_
    rw [exp_sub,exp_log (show 0<log L from hlog),exp_log hM,rpow_def_of_pos hl]; congr 1; ring
  have hm1 : 48/M≤1 := (div_le_one hM).mpr (le_max_left ..)
  have hmε : 48/M≤ε/2 := (div_le_iff₀ hM).mpr (by
    have hh := (div_le_iff₀ hε).mp (le_max_right (48:ℝ) (96/ε)); dsimp only [M]; linarith only [hh])
  have hfit : exp (cost h)≤L := by rw [heq]; exact (rpow_le_rpow_of_exponent_le h1 hm1).trans_eq (rpow_one _)
  apply le_trans _ (hwin H hHX hlen h hh hfit q r hq hr hqr hqz z hz)
  have hZ : 1≤ThetaIdentityModels.Z := (ThetaIdentityModels.weight_one (by decide : 0<1) (le_refl 1)).trans
    (ThetaReciprocalBlocks.commonWeight_bounds 1 1).2
  have hh₁ := log_nonneg (show (1:ℝ)≤ThetaLocalExcursionScales.cutoff X by exact_mod_cast (show 1≤ThetaLocalExcursionScales.cutoff X from (by decide : 1≤2).trans hY.1))
  have hU₀ : 0<height X := by unfold height; positivity
  have hprod : exp (cost h)*height X≤L^ε := calc
    _ ≤ L^(ε/2)*L^(ε/2) := mul_le_mul (heq.le.trans (rpow_le_rpow_of_exponent_le h1 hmε)) hU hU₀.le (rpow_nonneg hl.le _)
    _ = _ := by rw [←rpow_add hl]; congr 1; ring
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (show 0<2*L*exp (cost h)*height X by positivity)
  change 2*L*exp (cost h)*height X≤2*L^(1+ε)
  rw [rpow_add hl,rpow_one]
  nlinarith only [mul_le_mul_of_nonneg_left hprod hl.le]

/-- The elementary complete-sum bound suffices above the three-quarter scale. -/
theorem elementary {θ : ℝ} (hθ : 3/4<θ) (ordinary : Ordinary θ) : Edge θ :=
  edge (e:=48) (by decide) (le_refl 48) elementary_kernel (by norm_num; linarith) ordinary

/-- The complete Weil estimate reaches the range of the ordinary
Thorner--Zaman short-interval prime number theorem in progressions. -/
theorem weil {θ : ℝ} (hθ : 1/2<θ) (weil : ThetaWeilShortIntervals.Weil) (ordinary : Ordinary θ) : Edge θ :=
  edge (e:=32) (le_refl 32) (by decide) (ThetaWeilShortIntervals.kernel weil) (by norm_num; linarith) ordinary

#print axioms finite
#print axioms edge
#print axioms elementary
#print axioms weil
end
end Arxiv.«2501.03234».ThetaShortExcursionTails
