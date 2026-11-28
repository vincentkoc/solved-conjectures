import ThetaRowProgressionDiscrepancy

/-! A log-weighted prime progression estimate is needed only on the chosen fiber. -/
namespace Arxiv.«2501.03234».ThetaFiberDiscrepancy
open Finset ThetaConditionalRows ThetaPeriodMeans ThetaIdentityFiber ThetaRowCorrelations
noncomputable section

def mass (s : Finset ℕ) (v : ℕ → ℝ) (q b : ℕ) := ∑ n∈s.filter (fun n => n%q=b),v n

def OnClass (s : Finset ℕ) (v : ℕ → ℝ) (m r q : ℕ) (M δ : ℝ) : Prop :=
  ∀ b<q,b%m=r → |mass s v q b-(if b.Coprime q then M/q.totient else 0)| ≤ δ

/-- Only residues where the test can be nonzero enter the discrepancy estimate. -/
theorem test {s : Finset ℕ} {v f : ℕ → ℝ} {q m r : ℕ} [NeZero q] {M δ B : ℝ}
    (hh : OnClass s v m r q M δ) (hδ : 0 ≤ δ) (hf : OnMod q f)
    (hs : ∀ b,b%m≠r → f b=0) (hb : ∀ b,|f b| ≤ B) :
    |(∑ n∈s,v n*f n)-M*unitMean q f| ≤ q*(B*δ) := by
  classical
  let u (b : ℕ) := if b.Coprime q then M/q.totient else 0
  have he : ∑ b∈range q,f b*mass s v q b=∑ n∈s,v n*f n := by
    simp only [mass,mul_sum,sum_filter]
    rw [sum_comm];apply sum_congr rfl;intro n _
    simpa [mul_ite,eq_comm,Nat.mod_lt n (NeZero.pos q),mul_comm] using congrArg (fun a => v n*a) (hf n)
  have hu : ∑ b∈range q,f b*u b=M*unitMean q f := by
    rw [unitMean,ThetaReciprocalFibers.unit_sum_nat,←mul_div_assoc,mul_sum,sum_div,sum_filter]
    apply sum_congr rfl;intro b _
    by_cases h : b.Coprime q
    · simp only [u,if_pos h];ring
    · simp [u,h]
  rw [←he,←hu,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc _ ≤ ∑ _b∈range q,B*δ := by
         apply sum_le_sum;intro b hq
         rw [←mul_sub,abs_mul]
         by_cases h : b%m=r
         · exact mul_le_mul (hb b) (hh b (mem_range.mp hq) h) (abs_nonneg _) ((abs_nonneg _).trans (hb b))
         · rw [hs b h,abs_zero,zero_mul];exact mul_nonneg ((abs_nonneg _).trans (hb b)) hδ
       _ = _ := by simp

theorem selected {s : Finset ℕ} {v : ℕ → ℝ} {m d P r : ℕ} [NeZero P] {M δ B : ℝ}
    (hm : 0 < m) (hd : 0 < d) (hdiv : m*d∣P) (hδ : 0 ≤ δ) (h : OnClass s v m r (m*d) M δ)
    (f : ℕ → ℝ) (hf : OnMod d f) (hb : ∀ n,|f n| ≤ B) :
    |(∑ n∈s,v n*(selectClass r m n*f n))-M*unitMean P (fun n => selectClass r m n*f n)| ≤ (m*d:ℕ)*(B*δ) := by
  let : NeZero (m*d) := ⟨(Nat.mul_pos hm hd).ne'⟩
  have hf' : OnMod (m*d) (fun n => selectClass r m n*f n) := fun n =>
    congrArg₂ (·*·) (onMod_lift (dvd_mul_right m d) (selectClass_mod r m) n) (onMod_lift (dvd_mul_left d m) hf n)
  rw [unitMean_lift hdiv hf']
  apply test h hδ hf' (fun b h => by simp [selectClass,h])
  intro b
  by_cases H : b%m=r
  · simpa [selectClass,H] using hb b
  · simpa [selectClass,H] using (abs_nonneg _).trans (hb b)

#print axioms selected
end
end Arxiv.«2501.03234».ThetaFiberDiscrepancy
