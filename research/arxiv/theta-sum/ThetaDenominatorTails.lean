import ThetaUniformWindows
/-! Coefficient tails after removing small original reduced moduli. -/

namespace Arxiv.«2501.03234».ThetaDenominatorTails

open Finset ThetaReciprocalBlocks ThetaUniformWindows ThetaReciprocalLargeSieve

private noncomputable def zeta (s : ℝ) : ℝ := ∑' n : ℕ, ((n:ℝ)^s)⁻¹

private lemma zeta_nonneg (s : ℝ) : 0≤zeta s := tsum_nonneg (by intros; positivity)

private lemma cw_bound (Y d : ℕ) : 0≤commonWeight Y d ∧ commonWeight Y d≤zeta 2 := by
  simpa only [zeta,Real.rpow_two] using commonWeight_bounds Y d

private lemma term_rankin (L : ℕ → ℕ) {T q m Y : ℕ} [NeZero q] (hT : 1≤T)
    (cut : ∀ d≤T, L d=0) (hm : 0 < m) :
    (T:ℝ)^(1/128:ℝ) * ‖(commonWeight Y (q*m)/((q:ℝ)*m)) • numeratorWindow q m (L (q*m))‖ ≤
      (30*zeta 2*(1+Real.log q)*(q:ℝ)^(1/128:ℝ)/q)*((m:ℝ)^(159/128:ℝ))⁻¹ := by
  have hq := NeZero.pos q
  have hqp : (0:ℝ)<q := by exact_mod_cast hq
  have hmp : (0:ℝ)< m := by exact_mod_cast hm
  have hl := Real.log_nonneg (show 1≤(q:ℝ) by exact_mod_cast hq)
  have hz := zeta_nonneg 2
  by_cases hd : q*m≤T
  · rw [cut _ hd,numeratorWindow,sum_range_zero,smul_zero,norm_zero,mul_zero]; positivity
  have hqmul : 1<q*m := by omega
  obtain ⟨hw,hW⟩ := cw_bound Y (q*m)
  have hR := numeratorWindow_uniform hqmul (L (q*m))
  have ht := Real.rpow_le_rpow (Nat.cast_nonneg T) (show (T:ℝ)≤(q:ℝ)*m by exact_mod_cast Nat.le_of_lt (lt_of_not_ge hd))
    (show (0:ℝ)≤1/128 by norm_num)
  rw [Real.mul_rpow hqp.le hmp.le] at ht
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hw (by positivity))]
  apply (mul_le_mul ht (mul_le_mul (div_le_div_of_nonneg_right hW (by positivity)) hR (norm_nonneg _) (by positivity))
    (by positivity) (by positivity)).trans
  have hh := harmonic_divisors hq hm
  have hr : (m:ℝ)^(1/128:ℝ)*((m:ℝ)^(5/4:ℝ))⁻¹ = ((m:ℝ)^(159/128:ℝ))⁻¹ := by
    rw [← Real.rpow_neg hmp.le,← Real.rpow_add hmp,← Real.rpow_neg hmp.le]; norm_num
  calc
    _ = ((3*zeta 2*(q:ℝ)^(1/128:ℝ)/q)*(m:ℝ)^(1/128:ℝ))*
          ((harmonic (q*m):ℝ)*m.divisors.card/(m:ℝ)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      rw [show 30*zeta 2*(1+Real.log q)*(q:ℝ)^(1/128:ℝ)/q*((m:ℝ)^(159/128:ℝ))⁻¹ =
          (30*zeta 2*(1+Real.log q)*(q:ℝ)^(1/128:ℝ)/q)*
            ((m:ℝ)^(1/128:ℝ)*((m:ℝ)^(5/4:ℝ))⁻¹) by rw [hr]]
      ring

/-- Deleting all original denominators up to T gains a factor T^(1/128)
in every block, at the price of q^(1/128). -/
theorem block_rankin : ∃ A : ℝ, 0≤A ∧ ∀ {T : ℕ}, 1≤T → ∀ L : ℕ → ℕ, (∀ d≤T, L d=0) →
    ∀ (Y q : ℕ) [NeZero q], (T:ℝ)^(1/128:ℝ)*‖windowBlock L Y q‖ ≤ A*(q:ℝ)^(1/64:ℝ)/q := by
  let Z := zeta (159/128)
  have hz : 0≤Z := zeta_nonneg _
  have hz' := zeta_nonneg 2
  refine ⟨30*zeta 2*129*Z,by positivity,?_⟩; intro T hT L cut Y q _
  have hq := NeZero.pos q
  have hqp : (0:ℝ)<q := by exact_mod_cast hq
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hl := Real.log_nonneg hq1
  have hs := (Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<159/128)).sum_le_tsum (Icc 1 (Y/q))
    (by intros; positivity)
  have hlog := Real.log_natCast_le_rpow_div q (show (0:ℝ)<1/128 by norm_num)
  have hh : 1+Real.log q≤129*(q:ℝ)^(1/128:ℝ) := by linarith only [hlog,Real.one_le_rpow hq1 (show (0:ℝ)≤1/128 by norm_num)]
  unfold windowBlock
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity)).trans
  rw [mul_sum]
  apply (sum_le_sum (fun m hm => term_rankin L hT cut (Y:=Y) (q:=q) (mem_Icc.mp hm).1)).trans
  rw [← mul_sum]
  change ∑ m ∈ Icc 1 (Y/q), ((m:ℝ)^(159/128:ℝ))⁻¹ ≤ Z at hs
  apply (mul_le_mul_of_nonneg_left hs (by positivity)).trans
  have he : (q:ℝ)^(1/128:ℝ)*(q:ℝ)^(1/128:ℝ)=(q:ℝ)^(1/64:ℝ) := by rw [← Real.rpow_add hqp]; norm_num
  rw [← he]
  calc
    _ = (30*zeta 2*(q:ℝ)^(1/128:ℝ)*Z/q)*(1+Real.log q) := by ring
    _ ≤ (30*zeta 2*(q:ℝ)^(1/128:ℝ)*Z/q)*(129*(q:ℝ)^(1/128:ℝ)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring
/-- Squared energy above exact Fourier denominator Q when the original moduli
up to T have been removed. Both gains hold simultaneously. -/
theorem cut_energy : ∃ B : ℝ, 0≤B ∧ ∀ {T : ℕ}, 1≤T → ∀ L : ℕ → ℕ, (∀ d≤T, L d=0) →
    ∀ Y Q : ℕ, 0<Q → ∀ s : Finset ℕ, (∀ q ∈ s, Q≤q) →
      ∑ q ∈ s, windowMass L Y q ≤ (B/(T:ℝ)^(1/64:ℝ))/(Q:ℝ)^(15/16:ℝ) := by
  obtain ⟨A,_,ha⟩ := block_rankin
  obtain ⟨B,hB,h⟩ := power_envelope_tail A
  refine ⟨B,hB,?_⟩; intro T hT L cut Y Q hQ s hs
  have hr : 0<(T:ℝ) := by exact_mod_cast hT
  have he : (T:ℝ)^(1/64:ℝ)=((T:ℝ)^(1/128:ℝ))^2 := by rw [← Real.rpow_mul_natCast hr.le]; norm_num
  have hb (q : ℕ) (hq : q ∈ s) : (T:ℝ)^(1/64:ℝ)*windowMass L Y q ≤ (A*(q:ℝ)^(1/64:ℝ)/q)^2 := by
    let : NeZero q := ⟨(hQ.trans_le (hs q hq)).ne'⟩
    have hm : windowMass L Y q ≤ ‖windowBlock L Y q‖^2 := by
      simpa only [windowMass,windowCoordinate,dif_neg (NeZero.ne q)] using primitive_mass_le q (windowBlock L Y q)
    rw [he]
    apply (mul_le_mul_of_nonneg_left hm (sq_nonneg _)).trans
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (ha hT L cut Y q) 2
  have hh := (sum_le_sum hb).trans (h hQ s hs)
  rw [← mul_sum] at hh
  have htr := Real.rpow_pos_of_pos hr (1/64)
  calc
    _ ≤ (B/(Q:ℝ)^(15/16:ℝ))/(T:ℝ)^(1/64:ℝ) := (le_div_iff₀ htr).mpr (by rwa [mul_comm])
    _ = _ := by ring

/-- The large-sieve variance gains T^(-1/64) after deleting small original
moduli; the numerator cutoffs may be chosen independently at each scale. -/
theorem cut_variance : ∃ B : ℝ, 0≤B ∧ ∀ {T : ℕ}, 1≤T → ∀ L : ℕ → ℕ, (∀ d≤T, L d=0) →
    ∀ N : ℕ, 1≤N →
    ∑ n ∈ range (N^64+1), ‖ThetaReciprocalInversion.windowExtension L (2*N^52) n‖^2 ≤
      B*(N:ℝ)^64/(T:ℝ)^(1/64:ℝ) := by
  obtain ⟨B,hB,ht⟩ := cut_energy
  refine ⟨15876*B,by positivity,?_⟩; intro T hT L cut N hN
  exact (ThetaReciprocalVariance.window_variance_from_energy (by positivity) (ht hT L cut) N hN).trans_eq (by ring)

open ThetaReciprocalInversion ThetaCotangentTriangle

/-- Reflection in the numerator reverses the sign on unit arguments. -/
theorem primitive_reflect {p d : ℕ} (hd : 1<d) (hc : p.Coprime d) {j : ℕ} (hj : j≤2*d) :
    primitiveTerm p d (2*d-j) = -primitiveTerm p d j := by
  let : NeZero d := ⟨by omega⟩
  let : Nontrivial (ZMod d) := ZMod.nontrivial_iff.mpr (by omega)
  have hz : ((2*d-j:ℕ):ZMod d) = -(j:ZMod d) := by
    rw [Nat.cast_sub hj,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_sub]
  have hcop : (2*d-j).Coprime d ↔ j.Coprime d := by
    rw [← ZMod.isUnit_iff_coprime,← ZMod.isUnit_iff_coprime,hz,IsUnit.neg_iff]
  have hpar : (2*d-j)%2=j%2 := by omega
  simp only [primitiveTerm,hpar,hcop]
  split_ifs with h
  · let y := (j:ZMod d)*(p:ZMod d)⁻¹
    have hne : y≠0 := by
      have he : (↑(ZMod.unitOfCoprime _ h.2.2 / ZMod.unitOfCoprime _ hc) : ZMod d) = y := rfl
      rw [← he]; exact Units.ne_zero _
    let : NeZero y := ⟨hne⟩
    unfold reciprocalSign
    rw [hz,neg_mul]
    rw [show (j:ZMod d)*(p:ZMod d)⁻¹=y by rfl,ZMod.val_neg_of_ne_zero y]
    have := ZMod.val_lt y
    split_ifs <;> norm_num <;> omega
  · exact neg_zero.symm

/-- The numerator sign has period twice the reduced modulus. -/
theorem primitive_period (p d j : ℕ) :
    primitiveTerm p d (2*d+j) = primitiveTerm p d j := by
  have hz : ((2*d+j:ℕ):ZMod d) = (j:ZMod d) := by simp
  have hc : (2*d+j).Coprime d ↔ j.Coprime d := by rw [← ZMod.isUnit_iff_coprime,← ZMod.isUnit_iff_coprime,hz]
  have hpar : (2*d+j)%2=j%2 := by omega
  simp only [primitiveTerm,reciprocalSign,hc,hpar,hz]

private lemma scalar_row_bound {p d : ℕ} (hd : 1<d) (hc : p.Coprime d) (n : ℕ) :
    ‖∑ i ∈ range n, ((↑(i+1:ℕ):ℂ)⁻¹)*primitiveTerm p d (i+1)‖ ≤ 3*(harmonic d:ℝ) := by
  have hv (j : ℕ) : ‖primitiveTerm p d j‖≤1 := by
    unfold primitiveTerm reciprocalSign; split_ifs <;> norm_num
  have h := reciprocal_window (d:=d) (by omega) (primitiveTerm p d) hv
    (by simp [primitiveTerm]) (primitive_period p d) (fun _ => primitive_reflect hd hc) n
  simpa [Complex.real_smul,Complex.ofReal_inv] using h

/-- Clear the original reduced moduli at most T. -/
def above (T : ℕ) (L : ℕ → ℕ) (d : ℕ) : ℕ := if d≤T then 0 else L d

/-- At integers coprime to every retained modulus, the omitted small rows
have total size O(H_T²), uniformly in the numerator widths. -/
private lemma small_rows {T Y p : ℕ} (L : ℕ → ℕ) (hL : L 1=0)
    (hc : ∀ d ∈ Icc 1 Y, p.Coprime d) :
    ‖windowExtension L Y p-windowExtension (above T L) Y p‖ ≤ 3*zeta 2*(harmonic T:ℝ)^2 := by
  classical
  let W (d : ℕ) := (commonWeight Y d:ℂ)/d
  let f (d n : ℕ) := ∑ i ∈ range n, (↑(i+1:ℕ):ℂ)⁻¹*primitiveTerm p d (i+1)
  let s := Icc 1 (min Y T)
  have he : windowExtension L Y p-windowExtension (above T L) Y p=∑ d ∈ s, W d*f d (L d) := by
    rw [window_primitive_rows L hc,window_primitive_rows (above T L) hc,← sum_sub_distrib]
    have hs : s=(Icc 1 Y).filter (·≤T) := by ext i; simp [s]; omega
    rw [hs,sum_filter]
    apply sum_congr rfl; intro d _
    by_cases h : d≤T <;> simp [above,h,W,f]
  have hH : 0≤(harmonic T:ℝ) := by unfold harmonic; positivity
  have hZ := zeta_nonneg 2
  have hterm (d : ℕ) (hd : d ∈ s) : ‖W d*f d (L d)‖ ≤ (3*zeta 2*(harmonic T:ℝ))*(d:ℝ)⁻¹ := by
    obtain ⟨hd₀,hd'⟩ := mem_Icc.mp hd
    have hdT := le_trans hd' (min_le_right _ _)
    have hdy := le_trans hd' (min_le_left _ _)
    have hr : (0:ℝ)<d := by exact_mod_cast hd₀
    by_cases h1 : d=1
    · subst d; simp [hL,f]; positivity
    have hb := scalar_row_bound (show 1<d by omega) (hc d (mem_Icc.mpr ⟨hd₀,hdy⟩)) (L d)
    have hw := cw_bound Y d
    rw [norm_mul]
    have hnorm : ‖W d‖ = commonWeight Y d/d := by
      dsimp [W]; rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1,Complex.norm_natCast]
    rw [hnorm]
    apply (mul_le_mul (div_le_div_of_nonneg_right hw.2 hr.le)
      (hb.trans (mul_le_mul_of_nonneg_left (harmonic_mono_real hdT) (by norm_num))) (norm_nonneg _) (by positivity)).trans_eq
    ring
  rw [he]
  apply (norm_sum_le ..).trans ((sum_le_sum hterm).trans ?_)
  rw [← mul_sum]
  have hmass : ∑ d ∈ s, (d:ℝ)⁻¹ ≤ (harmonic T:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    intro d hd; exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans (min_le_right _ _)⟩
  exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (by ring)

/-- A logarithmic-square uniform bound for the contribution of small original moduli. -/
theorem small_rows_bound : ∃ D : ℝ, 0≤D ∧ ∀ {T : ℕ}, 1≤T → ∀ L : ℕ → ℕ, L 1=0 →
    ∀ {Y p : ℕ}, (∀ d ∈ Icc 1 Y, p.Coprime d) →
    ‖windowExtension L Y p-windowExtension (above T L) Y p‖ ≤ D*(1+Real.log T)^2 := by
  have hz := zeta_nonneg 2
  refine ⟨3*zeta 2,by positivity,?_⟩; intro T _ L hL Y p hc
  apply (small_rows L hL hc).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hH : 0≤(harmonic T:ℝ) := by unfold harmonic; positivity
  exact pow_le_pow_left₀ hH (harmonic_le_one_add_log _) 2

end Arxiv.«2501.03234».ThetaDenominatorTails
#print axioms Arxiv.«2501.03234».ThetaDenominatorTails.block_rankin
#print axioms Arxiv.«2501.03234».ThetaDenominatorTails.cut_energy
#print axioms Arxiv.«2501.03234».ThetaDenominatorTails.cut_variance
#print axioms Arxiv.«2501.03234».ThetaDenominatorTails.small_rows_bound
#print axioms Arxiv.«2501.03234».ThetaDenominatorTails.primitive_reflect
#print axioms Arxiv.«2501.03234».ThetaDenominatorTails.primitive_period
