import ThetaExposureLayers
import ThetaTiltBudget

/-! A uniform exponential-moment estimate for the finite reciprocal-row models. -/
namespace Arxiv.«2501.03234».ThetaModelExponentialMoment
open Real Filter Finset ThetaUnitExposure ThetaSmoothFiltration ThetaExposureLayers
open ThetaTiltBudget ThetaSmoothConditionalModel ThetaConditionalRows ThetaPrimeTailTransfer
noncomputable section

def height (T : ℕ) := envelope*(238*(log T)^2)

theorem model_mgf : ∀ᶠ T : ℕ in atTop, ∀ Y V : ℕ, [NeZero Y.factorial] → 2≤Y →
    ∀ v : ℝ, |v|=tilt T →
    unitMean Y.factorial (fun n => exp (v*model Y V n)) ≤ exp (total+tilt T*height T) := by
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp eventual_size
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨L,hL⟩ := eventually_atTop.mp hlog
  filter_upwards [eventually_ge_atTop (max 2 (max Q L))] with T hT
  intro Y V _ hY v hv
  have h₀ : 2≤T := by omega
  have h₁ : Q≤T := by omega
  have h₂ : L≤T := by omega
  let F (t : ℕ) := ∑ x : (ZMod Y.factorial)ˣ, exp (v*value Y V t x)
  have hF (t : ℕ) : 0≤F t := sum_nonneg fun _ _ => (exp_pos _).le
  have hstep (t : ℕ) (ht : T≤t) : F (t+1) ≤ exp (charge (t+1))*F t := by
    have H := within (by omega : 1≤T) (by omega : T≤t+1) hv
    calc
      _ ≤ exp (v^2*(size (t+1))^2)*F t := one_step (hL (t+1) (by omega)) V (hQ _ (by omega)) H.1
      _ ≤ _ := mul_le_mul_of_nonneg_right (exp_le_exp.mpr H.2) (hF _)
  have telescope (t : ℕ) (ht : T≤t) :
      F t≤exp (∑ q∈Ico (T+1) (t+1),charge q)*F T := by
    induction t,ht using Nat.le_induction with
    | base => simp
    | succ t ht ih =>
      rw [sum_Ico_succ_top (by omega),exp_add,mul_right_comm]
      calc
        _ ≤ exp (charge (t+1))*F t := hstep _ ht
        _ ≤ _ := by
          have h := mul_le_mul_of_nonneg_left ih (exp_pos (charge (t+1))).le
          linarith only [h,show exp (charge (t+1))*(exp (∑ q∈Ico (T+1) (t+1),charge q)*F T)=
              exp (∑ q∈Ico (T+1) (t+1),charge q)*F T*exp (charge (t+1)) by ring]
  have hbase : F T ≤ Y.factorial.totient*exp (tilt T*height T) := by
    calc
      _ ≤ ∑ _x : (ZMod Y.factorial)ˣ,exp (tilt T*height T) := by
        apply sum_le_sum
        intro x _
        apply exp_le_exp.mpr
        calc
          _ ≤ |v*value Y V T x| := le_abs_self _
          _ = tilt T*|value Y V T x| := by rw [abs_mul,hv]
          _ ≤ _ := mul_le_mul_of_nonneg_left (baseline hY h₀ (hL _ h₂) V x) (tilt_pos (by omega)).le
      _ = _ := by simp [ZMod.card_units_eq_totient]
  let t := max T Y.factorial
  have hend : F t=(∑ x : (ZMod Y.factorial)ˣ,exp (v*model Y V (x:ZMod Y.factorial).val)) := by
    unfold F value
    rw [terminal (Nat.factorial_pos _) (le_max_right ..)]
    simp only [final_project]
  unfold unitMean
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.factorial_pos _)))).mpr
  rw [← hend,exp_add]
  calc
    F t ≤ exp (∑ q∈Ico (T+1) (t+1),charge q)*F T := telescope _ (le_max_left ..)
    _ ≤ exp total*(Y.factorial.totient*exp (tilt T*height T)) :=
      mul_le_mul (exp_le_exp.mpr (bounded _)) hbase (hF _) (exp_pos _).le
    _ = _ := by ring

#print axioms model_mgf
end
end Arxiv.«2501.03234».ThetaModelExponentialMoment
