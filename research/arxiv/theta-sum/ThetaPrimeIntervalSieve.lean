import ThetaSievedWindows
import ThetaIntervalPowerEndpoint
import ThetaLocalPrimeCounts

/-! A translated upper-bound sieve for the number of potential prime starting
points removed when a witness window is selected. -/
namespace Arxiv.«2501.03234».ThetaPrimeIntervalSieve
open Real Finset Filter ThetaPrimeSieve ThetaPeriodMeans ThetaIntervalPowerEndpoint
noncomputable section

def marks (M H : ℕ) := (Ico M (M+H)).filter Nat.Prime
def Z := ∑' j : ℕ, ((j:ℝ)^2)⁻¹

theorem finite {R M : ℕ} (hR : 2≤R) (hRM : R<M) (H : ℕ) :
    ((marks M H).card:ℝ)≤H*(Z/log R)+2*(R:ℝ)^6 := by
  classical
  let s := moduli R
  let G := normalizer R
  let f (r n : ℕ) := ramanujan r n/(r.totient:ℝ)/G
  let P := R.factorial^2
  have hP : 0<P := pow_pos (Nat.factorial_pos _) _
  have hG : 1≤G := one_le_normalizer (by omega)
  have info {r : ℕ} (hr : r∈s) : 0<r ∧ r≤R ∧ r∣R.factorial ∧ Squarefree r := by
    obtain ⟨hi,hq⟩ := mem_filter.mp hr;obtain ⟨h₁,h₂⟩ := mem_Icc.mp hi
    exact ⟨h₁,h₂,Nat.dvd_factorial h₁ h₂,hq⟩
  have hf : ∀ r∈s,OnMod r (f r) := by
    intro r hr n;dsimp [f];rw [ramanujan_onMod (info hr).2.2.2 n]
  have hh (n : ℕ) : (∑ r∈s,f r n)^2=weight R n := by unfold weight;dsimp only [f,G,s];rw [←sum_div]
  have hw : OnMod P (weight R) := by
    intro n;rw [←hh,←hh];congr 1;apply sum_congr rfl;intro r hr
    exact onMod_lift ((info hr).2.2.1.trans (by dsimp [P]; exact dvd_pow_self _ (by decide))) (hf r hr) n
  have hs := finite_period_square s id (fun r i => f r (M+i)) hP
    (fun r hr => ⟨(info hr).1,(info hr).2.1⟩) (fun r hr t ht => by
      simpa [P,pow_two] using Nat.mul_dvd_mul (info hr).2.2.1 (info ht).2.2.1)
    (fun r hr => translate_period (hf r hr) M) (Nat.cast_nonneg R) (fun r hr j => by
      have hφ : (1:ℝ)≤r.totient := by exact_mod_cast Nat.totient_pos.mpr (info hr).1
      dsimp [f];rw [abs_div,abs_div,abs_of_nonneg (Nat.cast_nonneg r.totient (α:=ℝ)),abs_of_nonneg (by linarith : 0≤G)]
      exact (div_le_self (by positivity) hG).trans ((div_le_self (abs_nonneg _) hφ).trans
        ((ramanujan_bound (info hr).2.2.2 _).trans (Nat.cast_le.mpr (info hr).2.1)))) H
  simp_rw [hh] at hs
  rw [translate_mean hP hw M,mean_weight (by omega) hP (fun r hr =>
    (info hr).2.2.1.trans (by dsimp [P];exact dvd_pow_self _ (by decide)))] at hs
  have hcard : s.card≤R := (card_le_card (filter_subset ..)).trans (by simp [Nat.card_Icc])
  have hmain : ((marks M H).card:ℝ)≤∑ n∈range H,weight R (M+n) := calc
    _ = ∑ n∈marks M H,weight R n := by
      have hp (n : ℕ) (hn : n∈marks M H) : weight R n=1 :=
        weight_prime (by omega) (mem_filter.mp hn).2 (hRM.trans_le (mem_Ico.mp (mem_filter.mp hn).1).1)
      rw [sum_congr rfl hp];simp
    _ ≤ ∑ n∈Ico M (M+H),weight R n := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => sq_nonneg _)
    _ = _ := by simpa [Nat.add_comm] using (sum_Ico_eq_sum_range (weight R) M (M+H))
  apply hmain.trans (hs.trans (add_le_add (mul_le_mul_of_nonneg_left (ThetaSievedWindows.normalizer_bound hR)
    (Nat.cast_nonneg H)) ?_))
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg s.card (α:=ℝ)) (Nat.cast_le.mpr hcard) 2
  calc _ ≤ (R:ℝ)^2*(2*(R:ℝ)^2*(R:ℝ)^2) := mul_le_mul_of_nonneg_right hb (by positivity)
       _ = _ := by ring

/-- A single absolute constant for all translates once the starting point is
at least the length. Only the already formalized square sieve is used. -/
theorem uniform : ∃ C : ℝ,0<C ∧ ∀ᶠ H : ℕ in atTop,∀ M : ℕ,H≤M →
    ((marks M H).card:ℝ)*log H≤C*H := by
  have hZ : 0≤Z := tsum_nonneg fun _ => by positivity
  refine ⟨24*Z+48,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2^12:ℕ)] with H hH
  intro M hM
  let R := Nat.nthRoot 12 H
  have hr : 2≤R := (Nat.le_nthRoot_iff (by decide)).mpr hH
  have hlow : R^12≤H := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hhigh : H≤(2*R)^12 := (Nat.lt_pow_nthRoot_add_one (by decide) H).le.trans
    (Nat.pow_le_pow_left (by omega) _)
  have hRM : R<M := (lt_of_lt_of_le (by simpa only [pow_one] using Nat.pow_lt_pow_right (a:=R) (by omega : 1<R) (by decide : 1<12)) (hlow.trans hM))
  have hr' : 1<(R:ℝ) := by exact_mod_cast hr
  have hl := log_pos hr'
  have hp : 0<(H:ℝ) := by exact_mod_cast (show 0<H by omega)
  have hlog := log_le_log hp (show (H:ℝ)≤(2*(R:ℝ))^12 by exact_mod_cast hhigh)
  rw [log_pow,log_mul (by norm_num) (by linarith)] at hlog
  have h2 := log_le_log (by norm_num : (0:ℝ)<2) (Nat.cast_le.mpr hr)
  have hlog' : log (H:ℝ)≤24*log R := by norm_num at hlog;linarith
  have hh := mul_le_mul (finite hr hRM H) hlog' (log_nonneg (by exact_mod_cast (show 1≤H by omega)))
    (show (0:ℝ)≤H*(Z/log R)+2*(R:ℝ)^6 by positivity)
  have heq : (H*(Z/log R)+2*(R:ℝ)^6)*(24*log R)=24*Z*H+48*((R:ℝ)^6*log R) := by field_simp;ring
  rw [heq] at hh
  have herr : (R:ℝ)^6*log R≤H := calc
    _ ≤ (R:ℝ)^6*R := mul_le_mul_of_nonneg_left ((log_le_sub_one_of_pos (by linarith : 0<(R:ℝ))).trans (by linarith)) (by positivity)
    _ = (R:ℝ)^7 := by ring
    _ ≤ (R:ℝ)^12 := pow_le_pow_right₀ hr'.le (by decide)
    _ ≤ _ := by exact_mod_cast hlow
  linarith only [hh,herr]

#print axioms finite
#print axioms uniform
end
end Arxiv.«2501.03234».ThetaPrimeIntervalSieve
