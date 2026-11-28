import ThetaIdentityModels
import ThetaDyadicLaw

/-! Conditional means of the original residual on identity progressions. -/
namespace Arxiv.«2501.03234».ThetaIdentityPrimeMeans
open Finset Filter ThetaIdentityFiber ThetaPeriodMeans ThetaConditionalRows ThetaNaturalPrimeMeans
open ThetaPrimeTailTransfer ThetaCharacterPrimeMeans ThetaDyadicLaw ThetaDiagonalConstant ThetaPrimeDensity
open scoped Topology
noncomputable section

private theorem scaled (hAP : ProgressionMangoldt) {m : ℕ} (hm : 1 < m) {B : ℝ}
    (H : ∀ᶠ Y : ℕ in atTop, ∀ᶠ V : ℕ in atTop,
      letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
      m∣Y.factorial ∧ B≤ m.totient*unitMean Y.factorial (fun n => select m n*model Y V n)) : ∃ L : ℝ,
    B≤ m.totient*L ∧ Tendsto (primeMean (fun p => select m p*scaledOff p)) atTop (𝓝 L) := by
  have hφ : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < m)
  have hw (n : ℕ) : |select m n|≤1 := by unfold select; split <;> norm_num
  suffices ∃ L : ℝ, B/m.totient≤ L ∧ Tendsto (primeMean (fun p => select m p*scaledOff p)) atTop (𝓝 L) by
    obtain ⟨L,hL,h⟩ := this; exact ⟨L,by simpa only [mul_comm L] using (div_le_iff₀ hφ).mp hL,h⟩
  apply limit_of_prime_models
  intro ε he
  obtain ⟨Y,hy,hh⟩ := (H.and (bounded_twist_approx_eventually _ hw he)).exists
  obtain ⟨V,⟨hmP,hb⟩,hv⟩ := (hy.and hh).exists
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  have hp : OnMod Y.factorial (model Y V) := low_onMod
    (fun d hd _ => Nat.dvd_factorial (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2) _ _
  refine ⟨_,_,(div_le_iff₀ hφ).mpr (by simpa only [mul_comm (m.totient:ℝ)] using hb),?_,hv⟩
  exact periodic_prime_mean hAP (show OnMod Y.factorial _ from fun n => congrArg₂ (·*·) (onMod_lift hmP (select_mod m) n) (hp n))

/-- Transfer any uniform lower bound on the nested model means to the original class mean. -/
theorem transfer (hAP : ProgressionMangoldt) {m : ℕ} (hm : 1 < m) {B : ℝ}
    (H : ∀ᶠ Y : ℕ in atTop, ∀ᶠ V : ℕ in atTop,
      letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
      m∣Y.factorial ∧ B≤ m.totient*unitMean Y.factorial (fun n => select m n*model Y V n)) :
    ∃ M : ℝ, diagonalConstant+8/Real.pi^2*B≤ M ∧ Tendsto (progressionMean m 1 residual) atTop (𝓝 M) := by
  let c := 8/Real.pi^2
  have hc : 0< c := by dsimp [c]; positivity
  obtain ⟨L,hl,H⟩ := scaled hAP hm H
  have hφ : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < m)
  let D (X : ℕ) := ((primeSet (fun n => n%m=1) X).card:ℝ)/X.primeCounting
  have hD : Tendsto D atTop (𝓝 (1/(m.totient:ℝ))) := class_prime_density hAP (by omega) (Nat.coprime_one_left _) hm
  have hw : Tendsto (primeMean (select m)) atTop (𝓝 (1/(m.totient:ℝ))) := by
    apply hD.congr'
    apply Eventually.of_forall; intro X
    simp [D,primeMean,select,primeSet,sum_boole]
    congr 3; ext p; simp
  have hL := bounded_residual_mean (select m) (fun p => by unfold select; split <;> norm_num) hw H
  have hdiv := hL.div hD (one_div_ne_zero hφ.ne')
  refine ⟨_,?_,hdiv.congr' ?_⟩
  · change diagonalConstant+c*B ≤ (diagonalConstant*(1/m.totient)+c*L)/(1/m.totient)
    have he : (diagonalConstant*(1/(m.totient:ℝ))+c*L)/(1/m.totient)=diagonalConstant+c*(m.totient*L) := by field_simp
    rw [he]; exact add_le_add_right (mul_le_mul_of_nonneg_left hl hc.le) _
  · have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
    filter_upwards [hπ.eventually_ne_atTop 0] with X hX
    have hs : ∑ p∈Nat.primesLE X,select m p*residual p=∑ p∈primeSet (fun n => n%m=1) X,residual p := by
      rw [primeSet,sum_filter]; apply sum_congr rfl; intro p _
      unfold select; split_ifs <;> simp
    change _ / D X = _
    dsimp only [D]
    rw [primeMean,hs,progressionMean,div_div_div_cancel_right₀ (by exact hX : (X.primeCounting:ℝ)≠0)]

/-- Every fixed height is exceeded by the limiting mean of the original
residual in some identity progression. The mean uses primes in that class. -/
theorem arbitrarily_large (hAP : ProgressionMangoldt) (b : ℝ) :
    ∃ m : ℕ, 1 < m ∧ ∃ L : ℝ, b< L ∧ Tendsto (progressionMean m 1 residual) atTop (𝓝 L) := by
  let c := 8/Real.pi^2
  have hc : 0< c := by dsimp [c]; positivity
  obtain ⟨m,hm,H⟩ := ThetaIdentityModels.large ((b+1-diagonalConstant)/c)
  obtain ⟨M,hl,hM⟩ := transfer hAP hm H
  change diagonalConstant+c*((b+1-diagonalConstant)/c)≤ M at hl
  rw [mul_div_cancel₀ _ hc.ne'] at hl
  exact ⟨m,hm,M,by linarith,hM⟩
#print axioms transfer
#print axioms arbitrarily_large
end
end Arxiv.«2501.03234».ThetaIdentityPrimeMeans
