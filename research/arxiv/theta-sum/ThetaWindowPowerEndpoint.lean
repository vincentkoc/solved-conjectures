import ThetaAllWindowMoments

/-! A finite-interval moment uses the period of each product of rows. -/
namespace Arxiv.«2501.03234».ThetaWindowPowerEndpoint
open Finset ThetaPeriodMeans ThetaRowCorrelations ThetaSmoothConditionalModel
noncomputable section

theorem power_endpoint {Y : ℕ} (f : ℕ → ℕ → ℝ) (X k : ℕ) {B : ℝ} (hB : 0≤B)
    (hf : ∀ d∈Icc 2 Y, OnMod d (f d)) (hb : ∀ d∈Icc 2 Y, ∀ n, |f d n|≤B) :
    (∑ n∈range X,(∑ d∈Icc 2 Y,f d n)^k) ≤
      (X:ℝ)*mean Y.factorial (fun n => (∑ d∈Icc 2 Y,f d n)^k)+2*(B*(Y:ℝ)^2)^k := by
  classical
  let D := ↥(Icc 2 Y)
  let period (v : Fin k → D) := univ.lcm (fun i => (v i).val)
  let term (v : Fin k → D) (n : ℕ) := ∏ i,f (v i).val n
  have hexp (n : ℕ) : (∑ d∈Icc 2 Y,f d n)^k = ∑ v : Fin k → D,term v n := by
    rw [← sum_attach]
    calc
      _ = ∏ _i : Fin k,∑ d : D,f d.val n := by simp [D]
      _ = _ := by simpa [term] using prod_univ_sum (fun _i : Fin k => (univ:Finset D)) (fun _ d => f d.val n)
  have hper (v : Fin k → D) : period v∣Y.factorial := Finset.lcm_dvd (fun i _ =>
    Nat.dvd_factorial (by have := (mem_Icc.mp (v i).property).1;omega) (mem_Icc.mp (v i).property).2)
  have hsize (v : Fin k → D) : period v≤Y^k := by
    have hpos : 0 < ∏ i,(v i).val := prod_pos (fun i _ => by have := (mem_Icc.mp (v i).property).1;omega)
    apply (Nat.le_of_dvd hpos (Finset.lcm_dvd (fun i _ => dvd_prod_of_mem (fun i => (v i).val) (mem_univ i)))).trans
    calc _ ≤ ∏ _i : Fin k,Y := prod_le_prod' (fun i _ => (mem_Icc.mp (v i).property).2)
         _ = _ := by simp
  have hmod (v : Fin k → D) : OnMod (period v) (term v) := by
    intro n
    apply prod_congr rfl
    intro i _
    exact onMod_lift (dvd_lcm (f:=fun i => (v i).val) (mem_univ i)) (hf _ (v i).property) n
  have hbound (v : Fin k → D) (n : ℕ) : |term v n|≤B^k := by
    dsimp only [term]
    rw [abs_prod]
    simpa using prod_le_prod (s:=univ) (fun i _ => abs_nonneg (f (v i).val n))
      (fun i _ => hb _ (v i).property n)
  have hh (v : Fin k → D) : ∑ n∈range X,term v n ≤ (X:ℝ)*mean Y.factorial (term v)+2*(Y:ℝ)^k*B^k := by
    have h := (le_abs_self _).trans (finite_period_error (Nat.pos_of_dvd_of_pos (hper v) (Nat.factorial_pos _))
      (Nat.factorial_pos _) (hper v) (hmod v) (hbound v) X)
    have hs : (period v:ℝ) ≤ (Y:ℝ)^k := by exact_mod_cast hsize v
    linarith only [h,mul_le_mul_of_nonneg_right hs (pow_nonneg hB k)]
  simp_rw [hexp]
  rw [sum_comm]
  apply (sum_le_sum (s:=univ) (fun v _ => hh v)).trans
  rw [sum_add_distrib,← mul_sum]
  have he : (∑ v : Fin k → D,mean Y.factorial (term v)) = mean Y.factorial (fun n => ∑ v,term v n) := by
    simp only [mean,← sum_div];rw [sum_comm]
  rw [he]
  apply add_le_add_right
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
  have hd : (Fintype.card D:ℝ)≤Y := by
    exact_mod_cast (show Fintype.card D≤Y by simp [D,Nat.card_Icc])
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hd k) (by positivity)).trans_eq
  rw [mul_pow,show ((Y:ℝ)^2)^k=(Y:ℝ)^k*(Y:ℝ)^k by rw [pow_two,mul_pow]]
  ring

#print axioms power_endpoint
end
end Arxiv.«2501.03234».ThetaWindowPowerEndpoint
