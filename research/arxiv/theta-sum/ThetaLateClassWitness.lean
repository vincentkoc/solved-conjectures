import ThetaPrimeClassCoverage

/-! A populous reduced class has a theta-selected prime above a fixed fraction of π(X). -/
namespace Arxiv.«2501.03234».ThetaLateClassWitness
open Filter Finset Real ThetaPrimeClassBV ThetaProgressionIncidence
noncomputable section

theorem witness (P : ℕ → Prop) {X q : ℕ} (hq : 0<q) (a : (ZMod q)ˣ)
    (hsize : 8*q≤X.primeCounting)
    (hcount : (X.primeCounting:ℝ)/(2*q.totient)≤ selectedCount P X q a) :
    ∃ p : ℕ,p.Prime ∧ (p:ZMod q)=a ∧ ¬P p ∧ p≤X ∧ X.primeCounting<8*p := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let Z := X.primeCounting/8
  let b := (a:ZMod q).val
  let E := {p : ℕ | p.Prime ∧ (p:ZMod q)=(a:ZMod q) ∧ p≤(X:ℝ) ∧ ¬P p}
  by_contra! hbad
  have hsub : E ⊆ (pair 0 Z q q b b : Finset ℕ) := by
    intro p hp
    obtain ⟨hpr,hr,hp,hP⟩ := hp
    have hp' : p≤X := Nat.cast_le.mp hp
    have hsmall := hbad p hpr hr hP hp'
    have hz : p≤Z := by dsimp [Z];omega
    have hm : p%q=b := by rw [←ZMod.val_natCast q p,hr]
    simp [pair,hm,hz]
  have hcard : selectedCount P X q a≤(pair 0 Z q q b b).card := by
    simpa only [selectedCount,Set.ncard_coe_finset,E] using Set.ncard_le_ncard hsub
  have hupper := (Nat.cast_le (α:=ℝ).mpr hcard).trans (pair_count 0 Z q q b b hq hq)
  rw [Nat.lcm_self] at hupper
  have hqr : 0<(q:ℝ) := Nat.cast_pos.mpr hq
  have hf : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hφ : (q.totient:ℝ)≤q := by exact_mod_cast Nat.totient_le q
  have hM := (div_le_iff₀ (by positivity)).mp hcount
  have hM' := hM.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφ (by norm_num : (0:ℝ)≤2)) (Nat.cast_nonneg _))
  have hz : (Z:ℝ)*8 ≤ X.primeCounting := by exact_mod_cast Nat.div_mul_le_self X.primeCounting 8
  have hq' : 8*(q:ℝ) ≤ X.primeCounting := by exact_mod_cast hsize
  have hb := mul_le_mul_of_nonneg_right hupper hqr.le
  rw [add_mul,div_mul_cancel₀ _ hqr.ne',one_mul] at hb
  nlinarith only [hM',hz,hq',hb,hqr]

theorem lower {v : ℝ} (hv : v<1) : ∀ᶠ X : ℕ in atTop,8*(X:ℝ)^v≤X.primeCounting := by
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hpos : 0<log (2:ℝ) := log_pos (by norm_num)
  have h := hn.eventually ((isLittleO_log_rpow_rpow_atTop 1 (sub_pos.mpr hv)).bound
    (show 0<log (2:ℝ)/16 by positivity))
  filter_upwards [h,ThetaPrimeDensity.prime_count_lower,hn.eventually_gt_atTop 1] with X h hπ hx
  have hp : 0<(X:ℝ) := by linarith
  have hL := log_pos hx
  change ‖(log (X:ℝ))^(1:ℝ)‖ ≤ log 2/16*‖(X:ℝ)^(1-v)‖ at h
  rw [rpow_one,Real.norm_of_nonneg hL.le,Real.norm_of_nonneg (rpow_nonneg hp.le _)] at h
  apply (mul_le_mul_iff_left₀ hL).mp
  have hh := mul_le_mul_of_nonneg_left h (rpow_nonneg hp.le v)
  have hcancel : (X:ℝ)^v*(log 2/16*(X:ℝ)^(1-v))=log 2/16*X := by
    rw [mul_left_comm,←rpow_add hp,show v+(1-v)=1 by ring,rpow_one]
  rw [hcancel] at hh
  linarith only [hh,hπ]

#print axioms witness
#print axioms lower
end
end Arxiv.«2501.03234».ThetaLateClassWitness
