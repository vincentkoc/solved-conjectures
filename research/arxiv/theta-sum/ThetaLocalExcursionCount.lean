import ThetaLocalModelError
import ThetaReflectedWindowMeans

/-! A bounded low model with a large class mean forces many actual signed
excursions after deletion of the translated high-row exceptions. -/
namespace Arxiv.«2501.03234».ThetaLocalExcursionCount
open Real Finset ThetaPrimeTailTransfer ThetaIdentityFiber ThetaConditionalRows
open ThetaRowProgressionDiscrepancy ThetaIdentityModels
noncomputable section

theorem delete {s : Finset ℕ} (f R : ℕ → ℝ) {z c w v U D : ℝ} (hz : |z|=1) (hc : 0<c)
    (hw : 0≤w) (hv : 512≤v) (hU : 0<U) (hD : D≤c*v/512)
    (hs : (s.card:ℝ)≤2*w) (hb : ∀ n∈s, |f n|≤U)
    (hm : w*v/64-w≤∑ n∈s,z*f n)
    (he : U*((s.filter (fun n => D≤|R n-c*f n|)).card:ℝ)≤w) :
    w/U≤((s.filter (fun n => c*v/512≤z*R n)).card:ℝ) := by
  classical
  let P (n : ℕ) := c*v/512≤z*R n
  let Q (n : ℕ) := D≤|R n-c*f n|
  have pt (n : ℕ) (hn : n∈s) : z*f n≤v/256+(if P n then U else 0)+(if Q n then U else 0) := by
    have hh : z*f n≤U := (le_abs_self _).trans (by rw [abs_mul,hz,one_mul]; exact hb n hn)
    by_cases h : P n
    · rw [if_pos h]; split_ifs <;> linarith
    rw [if_neg h,add_zero]
    by_cases h' : Q n
    · rw [if_pos h']; linarith
    rw [if_neg h',add_zero]
    have hlow : z*R n<c*v/512 := lt_of_not_ge h
    have herr : |R n-c*f n|<D := lt_of_not_ge h'
    have hh' : |z*(R n-c*f n)|<D := by rw [abs_mul,hz,one_mul]; exact herr
    have hi := (abs_lt.mp hh').1
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith only [hi,hlow,hD]
  have h := sum_le_sum pt
  rw [sum_add_distrib,sum_add_distrib,←sum_filter,←sum_filter] at h
  simp only [sum_const,nsmul_eq_mul] at h
  change U*((s.filter Q).card:ℝ)≤w at he
  apply (div_le_iff₀ hU).mpr
  change w≤((s.filter P).card:ℝ)*U
  nlinarith only [hm,h,he,mul_le_mul_of_nonneg_right hs (show 0≤v/256 by linarith),mul_le_mul_of_nonneg_left hv hw]

/-- Transfer only uses the individual row periods md and the total number
of high-row errors on the tested set. -/
theorem finite {s : Finset ℕ} {m r Y N : ℕ} (hm : 0 < m) (hr : r < m) (hc : r.Coprime m)
    (hmY : m≤Y) {M δ z v D E : ℝ} (hM : 0≤M) (hδ : 0≤δ) (hz : |z|=1) (hv : 512≤v)
    (hD : D≤(8/π^2)*v/512) (hcl : Classes s m M δ)
    (hrows : ∀ d∈Icc 2 Y,Classes s (m*d) M δ) :
    letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
    let w := M/m.totient
    let U := 3*Z*(1+log Y)^2
    let R (p : ℕ) := (S p:ℝ)/p-log p/2
    δ≤w → Y*(3*Z*(1+log Y)*δ)≤w →
    v/64≤z*(m.totient*unitMean Y.factorial (fun j => selectClass r m j*model Y N j)) →
    ((s.filter (fun p => D≤|R p-(8/π^2)*model Y N p|)).card:ℝ)≤E → U*E≤w →
    w/U≤((s.filter (fun p => p%m=r ∧ v/(64*π^2)≤z*R p)).card:ℝ) := by
  classical
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  intro w U R hd herr hmodel he hUE
  let A := s.filter (fun p => p%m=r)
  have hw : 0≤w := div_nonneg hM (Nat.cast_nonneg _)
  have hφ : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  have hZ : 1≤Z := (weight_one (by decide : 0<1) (le_refl 1)).trans (ThetaReciprocalBlocks.commonWeight_bounds 1 1).2
  have hL := Real.log_nonneg (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega))
  have hU : 0<U := by dsimp [U]; positivity
  have hA : (A.card:ℝ)≤2*w := by
    have hh := (abs_le.mp (hcl r hr)).2; simp only [if_pos hc] at hh
    change (A.card:ℝ)-w≤δ at hh; linarith
  have hscale : w*(m.totient:ℝ)=M := by dsimp [w]; field_simp
  have hs : (∑ p∈s,selectClass r m p*model Y N p)=∑ p∈A,model Y N p := by
    unfold A selectClass; rw [sum_filter]; apply sum_congr rfl; intro n _; split_ifs <;> simp
  have hmod := selected_model (V:=N) hm hr hmY hδ hrows
  rw [hs] at hmod
  let u := unitMean Y.factorial (fun j => selectClass r m j*model Y N j)
  have l : w*(v/64)≤z*(M*u) := by
    calc _ ≤ w*(z*(m.totient*u)) := mul_le_mul_of_nonneg_left hmodel hw
         _ = _ := by rw [←hscale]; ring
  have hc' : |z*((∑ p∈A,model Y N p)-M*u)|≤w := by rw [abs_mul,hz,one_mul]; exact hmod.trans herr
  have hf : w*v/64-w≤∑ p∈A,z*model Y N p := by rw [←mul_sum]; nlinarith only [(abs_le.mp hc').1,l]
  have he' : U*((A.filter (fun p => D≤|R p-(8/π^2)*model Y N p|)).card:ℝ)≤w :=
    (mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (card_le_card (filter_subset_filter _ (filter_subset _ _)))).trans he) hU.le).trans hUE
  have H := delete (s:=A) (model Y N) R hz (show 0<(8/π^2:ℝ) by positivity) hw hv hU hD hA
    (fun p _ => ThetaLocalModelError.height (by omega) N p) hf he'
  simpa only [A,filter_filter,show (8/π^2)*v/512=v/(64*π^2) by ring] using H

#print axioms delete
#print axioms finite
end
end Arxiv.«2501.03234».ThetaLocalExcursionCount
