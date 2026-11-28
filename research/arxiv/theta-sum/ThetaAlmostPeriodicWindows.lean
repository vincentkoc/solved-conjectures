import ThetaWindowApproximation

/-! Fixed-modulus inputs on ordinary prime counts in almost all short windows.
Periodic tests cost only their own single modulus. -/
namespace Arxiv.«2501.03234».ThetaAlmostPeriodicWindows
open Real Finset Filter ThetaWindowApproximation ThetaLocalPrimeCounts ThetaPeriodMeans ThetaConditionalRows
open scoped Topology
noncomputable section

def scaledCount (X n H q b : ℕ) : ℝ :=
  log X/H*((sample n H).filter (fun p => p%q=b)).card

def Admits (θ : ℝ) (X H : ℕ) := 0<H ∧ H≤X ∧ (X:ℝ)^θ≤H

/-- Simultaneous ordinary lower prime counts in each fixed reduced class.
The exceptional proportion of starting integers tends to zero. -/
def Lower (θ c : ℝ) := ∀ q : ℕ, 0<q → Almost (fun X n =>
  ∀ H : ℕ, Admits θ X H → ∀ b<q, b.Coprime q → c/(q.totient:ℝ) ≤ scaledCount X n H q b)

/-- The two-sided ordinary prime-count discrepancy for fixed moduli. -/
def Equidistributed (θ : ℝ) := ∀ q : ℕ, 0<q → ∀ δ : ℝ, 0<δ → Almost (fun X n =>
  ∀ H : ℕ, Admits θ X H → ∀ b<q,
    |scaledCount X n H q b-(if b.Coprime q then (1:ℝ)/q.totient else 0)|≤δ)

theorem decompose {q : ℕ} [NeZero q] {f : ℕ → ℝ} (hp : OnMod q f) (X n H : ℕ) :
    avg X n H f=∑ b∈range q, f b*scaledCount X n H q b := by
  classical
  unfold avg scaledCount
  rw [Finset.mul_sum]
  simp_rw [show ∀ b : ℕ, f b*(log X/H*(((sample n H).filter (fun p => p%q=b)).card:ℝ))=
    ∑ p∈sample n H,if p%q=b then log X/H*f b else 0 by
      intro b;rw [←sum_filter,sum_const,nsmul_eq_mul];ring]
  rw [sum_comm];apply sum_congr rfl;intro p _
  simpa [eq_comm,Nat.mod_lt p (NeZero.pos q)] using congrArg (fun x => log X/H*x) (hp p).symm

theorem center {q : ℕ} [NeZero q] (f : ℕ → ℝ) (a : ℝ) :
    a*unitMean q f=∑ b∈range q, f b*(if b.Coprime q then a/q.totient else 0) := by
  rw [unitMean,ThetaReciprocalFibers.unit_sum_nat,←mul_div_assoc,mul_sum,sum_div,sum_filter]
  apply sum_congr rfl;intro b _
  by_cases h : b.Coprime q
  · rw [if_pos h,if_pos h];ring
  · simp [h]

theorem lower {θ c : ℝ} (h : Lower θ c) {q : ℕ} [NeZero q] {f : ℕ → ℝ}
    (hp : OnMod q f) (hf : ∀ p, 0≤f p) :
    Almost (fun X n => ∀ H : ℕ, Admits θ X H → c*unitMean q f≤avg X n H f) := by
  apply mono (h q (NeZero.pos q))
  filter_upwards [eventually_ge_atTop (2:ℕ)] with X hX
  intro n _ hh H hH
  rw [decompose hp,center]
  apply sum_le_sum;intro b hb;apply mul_le_mul_of_nonneg_left _ (hf b)
  by_cases hc : b.Coprime q
  · exact (if_pos hc).le.trans (hh H hH b (mem_range.mp hb) hc)
  · rw [if_neg hc,scaledCount]
    exact mul_nonneg (div_nonneg (log_nonneg (by exact_mod_cast (show 1≤X by omega))) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem limit {θ : ℝ} (h : Equidistributed θ) {q : ℕ} [NeZero q] {f : ℕ → ℝ}
    (hp : OnMod q f) {τ : ℝ} (hτ : 0<τ) :
    Almost (fun X n => ∀ H : ℕ, Admits θ X H → |avg X n H f-unitMean q f|≤τ) := by
  let B := ∑ b∈range q, |f b|
  have hB : 0≤B := sum_nonneg (fun _ _ => abs_nonneg _)
  let δ := τ/(B+1)
  have hδ : 0<δ := by dsimp [δ]; positivity
  apply mono (h q (NeZero.pos q) δ hδ)
  filter_upwards with X
  intro n _ hh H hH
  rw [decompose hp,←one_mul (unitMean q f),center,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc _ ≤ ∑ b∈range q,|f b| * δ := by
          apply sum_le_sum;intro b hb
          rw [←mul_sub,abs_mul];exact mul_le_mul_of_nonneg_left (hh H hH b (mem_range.mp hb)) (abs_nonneg _)
       _ = B*δ := by rw [←sum_mul]
       _ ≤ (B+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
       _ = τ := by dsimp only [δ];field_simp [show B+1≠0 by linarith]

#print axioms lower
#print axioms limit
end
end Arxiv.«2501.03234».ThetaAlmostPeriodicWindows
