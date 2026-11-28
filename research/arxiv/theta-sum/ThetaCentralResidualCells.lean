import ThetaBoundedResidualTriples
import ThetaShortResidualSupport

/-! One fixed refined class with few failures of an arbitrarily narrow residual test
in each sufficiently large central prime window. -/
namespace Arxiv.«2501.03234».ThetaCentralResidualCells
open Real Filter Finset ThetaTernaryErrorBudget ThetaTernaryWindows ThetaCalibratedCone
open ThetaCharacterPrimeMeans ThetaLocalPrimeCounts ThetaLocalIntervalTests ThetaCompactModulus
open ThetaCentralResidualBudget ThetaClassConcentration ThetaNaturalPrimeMeans
noncomputable section

theorem class_upper {β : ℝ} (ord : Ordinary β) {q r : ℕ} (hq : 0<q) (hr : r<q)
    (hu : r.Coprime q) : ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,H≤X → (X:ℝ)^β≤H →
      ((cell q r (sample X H)).card:ℝ)*log X ≤ 2*H/q.totient := by
  let hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ord 1 2,hlog.eventually_ge_atTop (q:ℝ),hlog.eventually_ge_atTop (q.totient:ℝ),
      hlog.eventually_ge_atTop 1,eventually_ge_atTop (2:ℕ)] with X h hqL hφL hL hx H hHX hlen
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  change (q:ℝ)≤log (X:ℝ) at hqL
  change (q.totient:ℝ)≤log (X:ℝ) at hφL
  change 1≤log (X:ℝ) at hL
  have hl : 0<log (X:ℝ) := by linarith
  have hd := (abs_le.mp (h H hHX hlen q hq (by simpa using hqL) r hr hu)).2
  change ((cell q r (sample X H)).card:ℝ)-mass X H/q.totient≤H/(log X)^2 at hd
  have he : (H:ℝ)/(log X)^2≤H/(log X*q.totient) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_left hφL hl.le]
  have hmass := div_le_div_of_nonneg_right (mass_upper (H:=H) hx) hφ.le
  rw [div_div] at hmass
  have hh : ((cell q r (sample X H)).card:ℝ) ≤ 2*H/(log X*q.totient) := by
    rw [mul_div_assoc];linarith only [hd,he,hmass]
  rw [←div_div,div_right_comm] at hh
  exact (le_div_iff₀ hl).mp hh

def misses (M a : ℕ) (y d : ℝ) (A : Finset ℕ) :=
  (cell M a A).filter (fun p => d≤|residual p-y|)

theorem sparse {e : ℕ} (he : 32≤e) (hc : e≤48) (hk : Kernel e)
    {β θ : ℝ} (hβ : (e:ℝ)/64<β) (hθ : β<θ) (ht : θ<1) (ord : Ordinary β)
    (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (y : ℝ) {d η : ℝ} (hd : 0<d) (hη : 0<η) (N : ℕ) :
    ∃ T≥N, q∣m T ∧ ∃ a < m T,a.Coprime (m T) ∧ a%q=r ∧ ∀ᶠ n : ℕ in atTop,
      ((misses (m T) a y d (window n θ)).card:ℝ)*width n ≤ η*(n:ℝ)^θ/(m T).totient := by
  let κ := η/64
  have hκ : 0<κ := by dsimp [κ];positivity
  obtain ⟨T,hT,hqT,a,ha,hu',hr',hc'⟩ :=
    ThetaShortResidualSupport.refinement he hc hk hβ (hθ.trans ht).le ord hAP hq hr hu y hd hκ N
  let M := m T
  have hm : 0<M := positive T
  have hφ : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  obtain ⟨X₀,h₀⟩ := eventually_atTop.mp (hc'.and (class_upper ord hm ha hu'))
  obtain ⟨Z,hZ⟩ := eventually_atTop.mp ((tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1)
  have hb : 0≤β := le_trans (by positivity) hβ.le
  refine ⟨T,hT,hqT,a,ha,hu',hr',?_⟩
  filter_upwards [scales hb hθ ht 0 (show 0<(1:ℝ) by norm_num) (max X₀ Z)] with n hn
  obtain ⟨X,H,hX,hHX,hfit,hH,hw,hV,hcontain⟩ := hn
  have hL : 1≤log (X:ℝ) := hZ X ((le_max_right ..).trans hX)
  have hV₁ : 1≤width X := by unfold width;linarith
  have hlen : (X:ℝ)^β≤H := by
    calc _ = (X:ℝ)^β*1 := (mul_one _).symm
         _ ≤ (X:ℝ)^β*(width X)^(8+0) := mul_le_mul_of_nonneg_left (one_le_pow₀ hV₁) (by positivity)
         _ ≤ H := by simpa only [one_mul] using hfit
  obtain ⟨hgood,hcard⟩ := h₀ X ((le_max_left ..).trans hX)
  let P := sample X H
  let E := misses M a y d (window n θ)
  have hsub : E ⊆ misses M a y d P := by
    intro p hp
    obtain ⟨hpm,hout⟩ := mem_filter.mp hp
    obtain ⟨hp,hres⟩ := mem_filter.mp hpm
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨ThetaShortPrimeInterval.mem_primes.mpr ⟨hcontain p hp,
      (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2,trivial⟩,hres⟩,hout⟩
  have hpart : (misses M a y d P).card+(hits M a y d P).card=(cell M a P).card := by
    simpa only [misses,hits,not_le] using
      (card_filter_add_card_filter_not (s:=cell M a P) (p:=fun p => d≤|residual p-y|))
  have heq : ((misses M a y d P).card:ℝ)+(hits M a y d P).card=(cell M a P).card := by exact_mod_cast hpart
  have hgood' := hgood H hHX hlen
  change (1-κ)*((cell M a P).card:ℝ)≤(hits M a y d P).card at hgood'
  have hm' : (E.card:ℝ)≤κ*(cell M a P).card := by
    linarith only [heq,hgood',Nat.cast_le (α:=ℝ).mpr (card_le_card hsub)]
  have hcard' := hcard H hHX hlen
  change ((cell M a P).card:ℝ)*log X ≤ 2*H/M.totient at hcard'
  have hwidth : width n≤4*log X := by unfold width at hw ⊢;linarith only [hw,hL]
  have hprod := mul_le_mul hm' hwidth (by unfold width;linarith only [Real.log_natCast_nonneg n]) (by positivity)

  change (E.card:ℝ)*width n≤η*(n:ℝ)^θ/M.totient
  dsimp [κ] at hprod
  calc _ ≤ _ := hprod
       _ = (η/16)*(((cell M a P).card:ℝ)*log X) := by ring
       _ ≤ (η/16)*(2*H/M.totient) := mul_le_mul_of_nonneg_left hcard' (by positivity)
       _ = (η/(8*M.totient))*H := by field_simp;ring
       _ ≤ (η/(8*M.totient))*(8*(n:ℝ)^θ) := mul_le_mul_of_nonneg_left hH (by positivity)
       _ = _ := by field_simp

#print axioms class_upper
#print axioms sparse
end
end Arxiv.«2501.03234».ThetaCentralResidualCells
