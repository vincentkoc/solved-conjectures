import ThetaLocalIntervalTests
import ThetaFullResidualSupport

/-! Every residual interval occurs with a positive proportion of the prime
scale in every sufficiently late eligible short interval and fixed reduced class. -/
namespace Arxiv.«2501.03234».ThetaShortResidualSupport
open Real Filter Finset ThetaLocalPrimeCounts ThetaLocalDyadicReference ThetaLocalWeightedLimits
open ThetaLocalIntervalTests ThetaClassConcentration ThetaIdentityFiber ThetaCharacterPrimeMeans
open ThetaPrimeDensity ThetaNaturalPrimeMeans ThetaCalibratedCone
open scoped Topology
noncomputable section

theorem class_count {θ : ℝ} (h : Ordinary θ) {q r : ℕ} (hq : 0<q) (hr : r<q) (hc : r.Coprime q) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
    mass X H/(2*q.totient)≤((cell q r (sample X H)).card:ℝ) := by
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h 1 2,ht.eventually_ge_atTop (q:ℝ),ht.eventually_ge_atTop (4*q.totient:ℝ),
    eventually_ge_atTop (2:ℕ)] with X hcl hqL hL hx
  intro H hHX hlen
  have hlog : 0<log (X:ℝ) := log_pos (by exact_mod_cast hx)
  change (q:ℝ)≤log (X:ℝ) at hqL
  have HH := (abs_le.mp (hcl H hHX hlen q hq (by rw [pow_one];exact hqL) r hr hc)).1
  have hb : (H:ℝ)/(log X)^2≤ mass X H/(2*q.totient) := by
    apply le_trans _ (div_le_div_of_nonneg_right (mass_lower hx hHX) (by positivity : 0≤2*(q.totient:ℝ)))
    rw [div_div,div_le_div_iff₀ (by positivity) (by positivity)]
    change 4*(q.totient:ℝ)≤log (X:ℝ) at hL
    nlinarith only [mul_le_mul_of_nonneg_left hL (show 0≤H*log (X:ℝ) by positivity)]
  change -((H:ℝ)/(log X)^2)≤((cell q r (sample X H)).card:ℝ)-mass X H/q.totient at HH
  have heq : mass X H/q.totient=2*(mass X H/(2*q.totient)) := by ring
  linarith only [hb,HH,heq]

/-- A single refinement attains the specified concentration in the prescribed
residual interval at every late endpoint and simultaneously for all eligible lengths. -/
theorem refinement {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hc : r.Coprime q) (y : ℝ) {d κ : ℝ} (hd : 0<d) (hκ : 0<κ)
    (N : ℕ) : ∃ T≥N, q∣m T ∧ ∃ a< m T, a.Coprime (m T) ∧ a%q=r ∧ ∀ᶠ X : ℕ in atTop,
      ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
      (1-κ)*((cell (m T) a (sample X H)).card:ℝ)≤((hits (m T) a y d (sample X H)).card:ℝ) := by
  classical
  let τ := min 1 κ/4
  have ht : 0<τ := by dsimp [τ];positivity
  have ht₁ : τ≤1 := by dsimp [τ];linarith only [min_le_left 1 κ]
  have hτκ : 3*τ≤κ := by dsimp [τ];linarith only [min_le_right 1 κ,hκ]
  obtain ⟨T,hT,hqT,a,ha,hu,hr',hh⟩ := ThetaFullResidualSupport.refinement hAP hq hr hc y
    (mul_pos hd ht) ht N
  let M := m T
  have hm : 0<M := ThetaCompactModulus.positive T
  have hφ : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  let η := d*τ/(2*M.totient)
  have hη : 0<η := by dsimp [η];positivity
  let f := test M a y d τ
  have hB (n : ℕ) : |selectClass a M n|≤1 := by unfold selectClass;split <;> norm_num
  obtain ⟨v,hv,hshort⟩ := common he h48 hk hθ hθ₁ h hAP hm (selectClass_mod a M) hB (lip y d (d*(1-2*τ)))
  change Tendsto (primeMean f) atTop (𝓝 v) at hv
  have hv₀ : 0≤v := by
    apply ge_of_tendsto hv
    filter_upwards [hh] with X hx
    have heq : ThetaFullResidualSupport.hits M a y (d*τ) X=hits M a y (d*τ) (Nat.primesLE X) := by
      apply Finset.ext;intro n;simp [ThetaFullResidualSupport.hits,hits,cell,primeSet,and_assoc]
    have hcell : primeSet (fun n => n%m T=a) X=cell M a (Nat.primesLE X) := by
      apply Finset.ext;intro n;simp only [primeSet,cell,mem_filter,M]
    rw [hcell] at hx
    rw [heq] at hx
    exact div_nonneg (lower M a y hd ht₁ _ hx) (Nat.cast_nonneg _)
  refine ⟨T,hT,hqT,a,ha,hu,hr',?_⟩
  filter_upwards [hshort η hη,class_count h hm ha hu,ThetaLocalMomentBudgets.count h] with X hs hc hm'
  intro H hHX hlen
  let s := sample X H
  have hmass := (hm' H hHX hlen).1
  have hl := (abs_lt.mp (hs H hHX hlen)).1
  change -η<avg X H f-v at hl
  have hlow : -η*mass X H≤∑ n∈s,f n :=
    (le_div_iff₀ hmass).mp (show -η≤avg X H f by linarith only [hl,hv₀])
  have HH := upper M a y hd τ s
  have hcost : η*mass X H≤d*τ*(cell M a s).card := by
    dsimp [η];rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hc H hHX hlen) (mul_nonneg hd.le ht.le)
  change (∑ n∈s,f n)≤_ at HH
  change (1-κ)*((cell M a s).card:ℝ)≤((hits M a y d s).card:ℝ)
  apply (mul_le_mul_iff_right₀ hd).mp
  nlinarith only [HH,hlow,hcost,mul_le_mul_of_nonneg_right hτκ
    (show 0≤d*((cell M a s).card:ℝ) by positivity)]

/-- The lower bound counts primes in the original class and is proportional
to H/log X rather than an unspecified subsequence of endpoints. -/
theorem density {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hc : r.Coprime q) (y : ℝ) {d : ℝ} (hd : 0<d) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
      δ*H/log X≤((hits q r y d (sample X H)).card:ℝ) := by
  obtain ⟨T,_,hdiv,a,ha,hu,har,hfine⟩ := refinement he h48 hk hθ hθ₁ h hAP hq hr hc y hd
    (by norm_num : (0:ℝ)<1/2) 0
  let M := m T
  have hm : 0<M := ThetaCompactModulus.positive T
  have hφ : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  refine ⟨1/(8*M.totient),by positivity,?_⟩
  filter_upwards [hfine,class_count h hm ha hu,eventually_ge_atTop (2:ℕ)] with X hf hcnt hX
  intro H hHX hlen
  let s := sample X H
  have hsub : hits M a y d s⊆hits q r y d s := by
    intro n hn
    obtain ⟨hcell,hi⟩ := mem_filter.mp hn
    obtain ⟨hs,hr'⟩ := mem_filter.mp hcell
    have hmod : n%M=a := hr'
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hs,by rw [←Nat.mod_mod_of_dvd n hdiv,hmod,har]⟩,hi⟩
  apply le_trans _ (Nat.cast_le.mpr (card_le_card hsub))
  apply le_trans _ (hf H hHX hlen)
  have hh := div_le_div_of_nonneg_right (mass_lower hX hHX) (by positivity : 0≤2*(M.totient:ℝ))
  have h := hh.trans (hcnt H hHX hlen)
  calc _ = (1-1/2:ℝ)*((H:ℝ)/(2*log X)/(2*M.totient)) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

#print axioms refinement
#print axioms density
end
end Arxiv.«2501.03234».ThetaShortResidualSupport
