import ThetaProgressionProjection
import ThetaIdentityFiber

/-! Transfer finite periodic estimates to one prime progression with its own
normalization. The endpoint can depend on the modulus. -/
namespace Arxiv.«2501.03234».ThetaConditionalApproximation
open Finset Filter Real ThetaPeriodMeans ThetaConditionalRows ThetaIdentityFiber
open ThetaDyadicLaw ThetaNaturalPrimeMeans ThetaPrimeDensity ThetaCharacterPrimeMeans
open ThetaPrimeLaw
open scoped Topology
noncomputable section

theorem periodic (hAP : ProgressionMangoldt) {M P r : ℕ} [NeZero P] (hM : 0< M)
    (hdiv : M∣P) (hr : r< M) (hc : r.Coprime M) {f : ℕ → ℝ} (hf : OnMod P f) :
    Tendsto (progressionMean M r f) atTop
      (𝓝 ((M.totient:ℝ)*unitMean P (fun n => selectClass r M n*f n))) := by
  have hon : OnMod P (fun n => selectClass r M n*f n) := fun n => by
    simp only [selectClass,Nat.mod_mod_of_dvd _ hdiv,hf n]
  have ha := periodic_prime_mean hAP hon
  have hd := class_prime_density hAP hM hc hr
  have ht : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  have h := ha.div hd (one_div_ne_zero ht.ne')
  rw [one_div,div_inv_eq_mul,mul_comm] at h
  apply h.congr'
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [hπ.eventually_ne_atTop 0] with X hx
  have hs : ∑ p∈Nat.primesLE X,selectClass r M p*f p=∑ p∈primeSet (fun n => n%M=r) X,f p := by
    rw [primeSet,sum_filter]; apply sum_congr rfl; intro p _; unfold selectClass; split_ifs <;> simp
  change (∑ p∈Nat.primesLE X,selectClass r M p*f p)/X.primeCounting/
    (((primeSet (fun n => n%M=r) X).card:ℝ)/X.primeCounting)=_
  change (X.primeCounting:ℝ)≠0 at hx
  rw [hs,div_div_div_cancel_right₀ hx]; rfl

theorem restrict_error (hAP : ProgressionMangoldt) {M r : ℕ} (hM : 0< M)
    (hr : r< M) (hc : r.Coprime M) {f : ℕ → ℝ} (hf : ∀ n,0≤f n) {δ : ℝ}
    (he : ∀ᶠ X : ℕ in atTop,primeMean f X≤δ) :
    ∀ᶠ X : ℕ in atTop,progressionMean M r f X≤2*(M.totient:ℝ)*δ := by
  let A (X : ℕ) := primeSet (fun n => n%M=r) X
  have ht : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  have hd := (class_prime_density hAP hM hc hr).eventually_const_lt
    (show 1/(2*(M.totient:ℝ))<1/M.totient by apply one_div_lt_one_div_of_lt (by positivity);linarith)
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [he,hd,hπ.eventually_gt_atTop 0] with X H hc' hx
  change 0<(X.primeCounting:ℝ) at hx
  change 1/(2*(M.totient:ℝ))<((A X).card:ℝ)/X.primeCounting at hc'
  have hcnt : 0<((A X).card:ℝ) := by by_contra! hz; have := div_nonpos_of_nonpos_of_nonneg hz hx.le; linarith [one_div_pos.mpr (by positivity : 0<2*(M.totient:ℝ))]
  have hratio := (div_lt_div_iff₀ (by positivity) hx).mp hc'
  have herr := (div_le_iff₀ hx).mp H
  have hδ : 0≤δ := (div_nonneg (sum_nonneg fun _ _ => hf _) hx.le).trans H
  change (∑ p∈A X,f p)/_≤_; rw [div_le_iff₀ hcnt]
  have sub : A X⊆Nat.primesLE X := by intro n hn; simp only [A,primeSet,mem_filter] at hn;exact hn.1
  apply (sum_le_sum_of_subset_of_nonneg sub (fun p _ _ => hf p)).trans
  apply herr.trans
  nlinarith only [mul_le_mul_of_nonneg_left hratio.le hδ]

private theorem avg_add {s : Finset ℕ} (f g : ℕ → ℝ) (a : ℝ) :
    (∑ p∈s,|f p-a|)/(s.card:ℝ) ≤ (∑ p∈s,|f p-g p|)/(s.card:ℝ)+(∑ p∈s,|g p-a|)/(s.card:ℝ) := by
  rw [←add_div,←sum_add_distrib]
  exact div_le_div_of_nonneg_right (sum_le_sum fun p _ => abs_sub_le ..) (Nat.cast_nonneg _)

theorem recenter {s : Finset ℕ} (hs : s.Nonempty) (f g : ℕ → ℝ) (a μ : ℝ) :
    (∑ p∈s,|f p-μ|)/(s.card:ℝ)≤
      2*((∑ p∈s,|f p-g p|)/(s.card:ℝ)+(∑ p∈s,|g p-a|)/(s.card:ℝ))+
      |(∑ p∈s,f p)/(s.card:ℝ)-μ| := by
  have hc : 0<(s.card:ℝ) := Nat.cast_pos.mpr (card_pos.mpr hs)
  let av := (∑ p∈s,f p)/(s.card:ℝ)
  have hconst (u : ℝ) : (∑ _p∈s,u)/(s.card:ℝ)=u := by rw [sum_const,nsmul_eq_mul]; field_simp
  have H : |av-a|≤(∑ p∈s,|f p-a|)/(s.card:ℝ) := by
    dsimp only [av]; nth_rw 1 [←hconst a]; rw [←sub_div,←sum_sub_distrib,abs_div,abs_of_pos hc]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs ..) hc.le
  have h := avg_add (s:=s) f (fun _ => a) μ
  rw [hconst] at h
  have htri := abs_sub_le a av μ
  rw [abs_sub_comm a av] at htri
  linarith only [htri,H,h,avg_add (s:=s) f g a]

#print axioms periodic
#print axioms restrict_error
#print axioms recenter
end
end Arxiv.«2501.03234».ThetaConditionalApproximation
