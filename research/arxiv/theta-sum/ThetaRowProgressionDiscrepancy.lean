import ThetaIdentityFiber
import ThetaIdentityModels

/-! Transfer a finite signed-denominator model using only its individual row periods. -/
namespace Arxiv.«2501.03234».ThetaRowProgressionDiscrepancy
open Finset ThetaConditionalRows ThetaIdentityFiber ThetaPeriodMeans ThetaRowCorrelations
noncomputable section

/-- Absolute counting discrepancy per residue against a specified total mass. -/
def Classes (s : Finset ℕ) (q : ℕ) (M δ : ℝ) : Prop :=
  ∀ b < q, |((s.filter (fun n => n%q=b)).card : ℝ) -
    (if b.Coprime q then M/q.totient else 0)| ≤ δ

theorem periodic {s : Finset ℕ} {q : ℕ} [NeZero q] {M δ : ℝ}
    (h : Classes s q M δ) {f : ℕ → ℝ} (hf : OnMod q f)
    : |(∑ n∈s,f n)-M*unitMean q f| ≤ (∑ b∈range q,|f b|)*δ := by
  classical
  let c (b : ℕ) := ((s.filter (fun n => n%q=b)).card : ℝ)
  let u (b : ℕ) := if b.Coprime q then M/q.totient else 0
  have hh : ∑ b∈range q, f b*c b=∑ n∈s,f n := by
    unfold c
    calc _ = ∑ b∈range q,∑ n∈s,if n%q=b then f b else 0 := by
              apply sum_congr rfl; intro b _
              rw [← sum_filter]; simp [mul_comm]
         _ = _ := by
              rw [sum_comm]; apply sum_congr rfl; intro n _
              simpa [eq_comm,Nat.mod_lt n (NeZero.pos q)] using hf n
  have hu : ∑ b∈range q, f b*u b=M*unitMean q f := by
    rw [unitMean,ThetaReciprocalFibers.unit_sum_nat,← mul_div_assoc,mul_sum,sum_div,sum_filter]
    apply sum_congr rfl; intro b _
    by_cases hb : b.Coprime q
    · simp only [u,if_pos hb]; ring
    · simp [u,hb]
  rw [← hh,← hu,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  rw [sum_mul]
  apply sum_le_sum; intro b hb
  rw [← mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left (h b (mem_range.mp hb)) (abs_nonneg _)

#print axioms periodic

private theorem selected_mass {m d r : ℕ} (hm : 0 < m) (hr : r < m)
    {f : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |f n|≤B) :
    (∑ b∈range (m*d),|selectClass r m b*f b|)≤d*B := by
  rw [sum_fibers hm]
  calc _ ≤ ∑ i∈range m, ∑ _j∈range d,if i=r then B else 0 := by
           apply sum_le_sum; intro i hi
           apply sum_le_sum; intro j _
           simp only [selectClass,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (mem_range.mp hi)]
           by_cases h : i=r <;> simp [h,hB]
       _ = _ := by
           simp only [sum_const,nsmul_eq_mul,mul_ite,mul_zero]
           simp [mem_range.mpr hr]

/-- A selected row costs at most one full denominator of residue classes,
regardless of the progression modulus. -/
theorem selected_row {s : Finset ℕ} {m d P r : ℕ} [NeZero P]
    (hm : 0 < m) (hd : 0 < d) (hr : r < m) (hmP : m*d∣P) {M δ B : ℝ}
    (hδ : 0≤δ) (h : Classes s (m*d) M δ) (K : ℕ)
    (hB : ∀ n, |row d K n|≤B) :
    |(∑ n∈s,selectClass r m n*row d K n)-
      M*unitMean P (fun n => selectClass r m n*row d K n)| ≤ d*B*δ := by
  let : NeZero (m*d) := ⟨(Nat.mul_pos hm hd).ne'⟩
  have hmod : OnMod (m*d) (fun n => selectClass r m n*row d K n) :=
    fun n => congrArg₂ (·*·) (onMod_lift (dvd_mul_right m d) (selectClass_mod r m) n)
      (onMod_lift (dvd_mul_left d m) (row_onMod d K) n)
  rw [unitMean_lift hmP hmod]
  exact (periodic h hmod).trans (mul_le_mul_of_nonneg_right (selected_mass hm hr hB) hδ)

#print axioms selected_row
open ThetaIdentityModels ThetaPrimeTailTransfer ThetaReciprocalBlocks ThetaReciprocalInversion ThetaPrimeMeanSquare

/-- The moving prime model needs only progression counts through modulus
`m*Y`. Its total error is independent of the factorial period. -/
theorem selected_model {s : Finset ℕ} {m r Y V : ℕ} (hm : 0 < m) (hr : r < m)
    (hmY : m≤Y) {M δ : ℝ} (hδ : 0≤δ)
    (h : ∀ d∈Icc 2 Y, Classes s (m*d) M δ) :
    letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
    |(∑ n∈s,selectClass r m n*model Y V n)-
      M*unitMean Y.factorial (fun n => selectClass r m n*model Y V n)| ≤
      Y*(3*Z*(1+Real.log Y)*δ) := by
  classical
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  let P := m*Y.factorial
  let : NeZero P := ⟨(Nat.mul_pos hm (Nat.factorial_pos _)).ne'⟩
  let K := coneWindow (coneWidth V)
  let a := commonWeight (2*V^52)
  let g (d n : ℕ) := selectClass r m n*row d (K d) n
  have hmfac := Nat.dvd_factorial hm hmY
  have hdv {d : ℕ} (hd : d∈Icc 2 Y) : d∣Y.factorial :=
    Nat.dvd_factorial (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2
  have hmod : OnMod Y.factorial (fun n => selectClass r m n*model Y V n) := by
    intro n; apply congrArg₂ (·*·) (onMod_lift hmfac (selectClass_mod r m) n)
    unfold model low
    apply sum_congr rfl; intro d hd
    rw [onMod_lift (hdv hd) (row_onMod d _) n]
  rw [← unitMean_lift (show Y.factorial∣P from dvd_mul_left _ _) hmod]
  change |(∑ n∈s,selectClass r m n*low Y K a n)-
    M*unitMean P (fun n => selectClass r m n*low Y K a n)|≤_
  rw [mean_low,mul_sum]
  have hs : (∑ n∈s,selectClass r m n*low Y K a n)=
      ∑ d∈Icc 2 Y,(a d/d)*∑ n∈s,g d n := by
    unfold low g; simp_rw [mul_sum]; rw [sum_comm]
    apply sum_congr rfl; intro d _
    apply sum_congr rfl; intros; ring
  rw [hs,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  have hlog : 0≤1+Real.log Y := by
    have h1 : (1:ℝ)≤Y := by exact_mod_cast (show 1≤Y by omega)
    linarith [Real.log_nonneg h1]
  have hZ : 0≤Z := tsum_nonneg (fun _ => by positivity)
  calc _ ≤ ∑ _d∈Icc 2 Y,3*Z*(1+Real.log Y)*δ := by
           apply sum_le_sum; intro d hd
           obtain ⟨h₂,hY⟩ := mem_Icc.mp hd
           have hd0 : 0 < d := by omega
           have hdR : 0<(d:ℝ) := by exact_mod_cast hd0
           have hB (n : ℕ) : |row d (K d) n|≤3*(1+Real.log Y) := by
             have hh := row_fiber (q:=d) (m:=1) hd0 (by decide) (by simpa using (show 1 < d by omega))
               (Nat.mod_lt n hd0) (K d)
             have hrow : |row d (K d) n|≤3*(harmonic d:ℝ) := by simpa [row_onMod d (K d) n] using hh
             linarith [harmonic_le_one_add_log d,Real.log_le_log hdR (by exact_mod_cast hY : (d:ℝ)≤Y)]
           have hb := selected_row hm hd0 hr (Nat.mul_dvd_mul_left m (hdv hd) : m*d∣P) hδ (h d hd) (K d) hB
           change |a d/d*(∑ n∈s,g d n)-M*(a d/d*unitMean P (g d))|≤_
           rw [mul_left_comm M,←mul_sub,abs_mul,abs_of_nonneg (div_nonneg (commonWeight_bounds _ _).1 hdR.le)]
           apply (mul_le_mul_of_nonneg_left hb (div_nonneg (commonWeight_bounds _ _).1 hdR.le)).trans
           calc a d/d*(d*(3*(1+Real.log Y))*δ) = a d*(3*(1+Real.log Y)*δ) := by field_simp
                _ ≤ Z*(3*(1+Real.log Y)*δ) := mul_le_mul_of_nonneg_right (commonWeight_bounds _ _).2 (by positivity)
                _ = _ := by ring
       _ ≤ _ := by
           simp only [sum_const,nsmul_eq_mul]
           apply mul_le_mul_of_nonneg_right _ (by positivity)
           exact_mod_cast (show (Icc 2 Y).card≤Y by rw [Nat.card_Icc]; omega)

#print axioms selected_model
end
end Arxiv.«2501.03234».ThetaRowProgressionDiscrepancy
