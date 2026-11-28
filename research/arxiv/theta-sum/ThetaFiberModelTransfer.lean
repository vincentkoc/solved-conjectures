import ThetaFiberDiscrepancy

/-! Transfer the selected denominator model with a weighted discrepancy on the selected class. -/
namespace Arxiv.«2501.03234».ThetaFiberModelTransfer
open Finset Real ThetaFiberDiscrepancy ThetaConditionalRows ThetaPeriodMeans ThetaIdentityFiber
open ThetaRowCorrelations ThetaIdentityModels ThetaPrimeTailTransfer ThetaReciprocalBlocks ThetaPrimeMeanSquare
open ThetaReciprocalInversion
noncomputable section

theorem selected_model {s : Finset ℕ} {v : ℕ → ℝ} {m r Y V : ℕ} (hm : 0 < m)
    (hmY : m ≤ Y) {M δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ d∈Icc 2 Y,OnClass s v m r (m*d) M δ) :
    letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
    |(∑ n∈s,v n*(selectClass r m n*model Y V n))-
      M*unitMean Y.factorial (fun n => selectClass r m n*model Y V n)| ≤
      Y*(m*(3*Z*(1+log Y)*δ)) := by
  classical
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  let P := m*Y.factorial
  let : NeZero P := ⟨(Nat.mul_pos hm (Nat.factorial_pos _)).ne'⟩
  let K := coneWindow (coneWidth V)
  let a := commonWeight (2*V^52)
  let g (d n : ℕ) := selectClass r m n*row d (K d) n
  have hmfac := Nat.dvd_factorial hm hmY
  have hdv {d : ℕ} (hd : d∈Icc 2 Y) : d∣Y.factorial :=
    Nat.dvd_factorial (by have := (mem_Icc.mp hd).1;omega) (mem_Icc.mp hd).2
  have hmod : OnMod Y.factorial (fun n => selectClass r m n*model Y V n) := by
    intro n;apply congrArg₂ (·*·) (onMod_lift hmfac (selectClass_mod r m) n)
    unfold model low;apply sum_congr rfl;intro d hd;rw [onMod_lift (hdv hd) (row_onMod d _) n]
  rw [← unitMean_lift (show Y.factorial∣P from dvd_mul_left _ _) hmod]
  have hs : (∑ n∈s,v n*(selectClass r m n*model Y V n))=
      ∑ d∈Icc 2 Y,(a d/d)*∑ n∈s,v n*g d n := by
    unfold model low g;simp_rw [mul_sum];rw [sum_comm]
    apply sum_congr rfl;intro d _;apply sum_congr rfl;intros;ring
  rw [hs,show (fun n => selectClass r m n*model Y V n)=(fun n => selectClass r m n*low Y K a n) from rfl,
    mean_low,mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  have hlog : 0 ≤ 1+log Y := by
    linarith [Real.log_nonneg (show (1:ℝ) ≤ Y by exact_mod_cast (show 1 ≤ Y by omega))]
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => by positivity)
  calc _ ≤ ∑ _d∈Icc 2 Y,m*(3*Z*(1+log Y)*δ) := by
         apply sum_le_sum;intro d hd
         obtain ⟨h₂,hY⟩ := mem_Icc.mp hd
         have hd₀ : 0 < d := by omega
         have hdR : 0<(d:ℝ) := Nat.cast_pos.mpr hd₀
         have hB (n : ℕ) : |row d (K d) n|≤3*(1+log Y) := by
           have hh := row_fiber (q:=d) (m:=1) hd₀ (by decide) (by simpa using (show 1<d by omega)) (Nat.mod_lt n hd₀) (K d)
           have hrow : |row d (K d) n|≤3*(harmonic d:ℝ) := by simpa [row_onMod d (K d) n] using hh
           linarith [harmonic_le_one_add_log d,Real.log_le_log hdR (by exact_mod_cast hY : (d:ℝ)≤Y)]
         have hb := selected hm hd₀ (Nat.mul_dvd_mul_left m (hdv hd) : m*d∣P) hδ (h d hd) _ (row_onMod d _) hB
         change |a d/d*(∑ n∈s,v n*g d n)-M*(a d/d*unitMean P (g d))|≤_
         rw [mul_left_comm M,←mul_sub,abs_mul,abs_of_nonneg (div_nonneg (commonWeight_bounds _ _).1 hdR.le)]
         apply (mul_le_mul_of_nonneg_left hb (div_nonneg (commonWeight_bounds _ _).1 hdR.le)).trans
         calc a d/d*((m*d:ℕ)*(3*(1+log Y)*δ)) = a d*(m*(3*(1+log Y)*δ)) := by push_cast;field_simp
              _ ≤ Z*(m*(3*(1+log Y)*δ)) := mul_le_mul_of_nonneg_right (commonWeight_bounds _ _).2 (by positivity)
              _ = _ := by ring
       _ ≤ _ := by
         simp only [sum_const,nsmul_eq_mul]
         apply mul_le_mul_of_nonneg_right _ (by positivity)
         exact_mod_cast (show (Icc 2 Y).card≤Y by rw [Nat.card_Icc];omega)

#print axioms selected_model
end
end Arxiv.«2501.03234».ThetaFiberModelTransfer
