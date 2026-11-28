import ThetaReciprocalLargeSieve

/-! Uniform finite-interval second moment of the interpolating rational cutoff. -/

namespace Arxiv.«2501.03234».ThetaReciprocalVariance

open Finset ThetaReciprocalBlocks ThetaReciprocalInversion ThetaReciprocalLargeSieve

private lemma band_cut (row : ℕ → ℕ) (Y r Q n : ℕ) (hr : 1≤r) (hQ : r≤Q) :
    windowBand row Y (Icc 1 Q) n = windowBand row Y (Icc 1 r) n + windowBand row Y (Ioc r Q) n := by
  have he : Icc 1 r ∪ Ioc r Q = Icc 1 Q := by ext k; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  have hd : Disjoint (Icc 1 r) (Ioc r Q) := disjoint_left.mpr (by
    intro k hk ht; exact (mem_Ioc.mp ht).1.not_ge (mem_Icc.mp hk).2)
  unfold windowBand; rw [← he,sum_union hd]

private lemma sum_three_sq (a b c : ℂ) : ‖a+b+c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have hh := (norm_add_le (a+b) c).trans (add_le_add (norm_add_le a b) (le_refl ‖c‖))
  apply (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans
  nlinarith only [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

private lemma harmonic_scale {Q N : ℕ} (hN : 1≤N) (hQ : 0<Q) (h : Q≤2*N^52) :
    (harmonic (Q^2) : ℝ) ≤ 110*N := by
  have hN' : 1≤(N:ℝ) := by exact_mod_cast hN
  have hQ' : 0<(Q:ℝ) := by exact_mod_cast hQ
  have hN0 : 0<(N:ℝ) := by linarith
  have ht : (Q:ℝ) ≤ 2*(N:ℝ)^52 := by exact_mod_cast h
  apply (harmonic_le_one_add_log _).trans
  rw [Nat.cast_pow,Real.log_pow]
  have hl := Real.log_le_log hQ' ht
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hN0.ne'),Real.log_pow] at hl
  norm_num at hl ⊢
  linarith [Real.log_le_self hN0.le,Real.log_le_self (by norm_num : (0:ℝ)≤2)]

private lemma band_scale (row : ℕ → ℕ) {Y N Q L : ℕ} (hN : 1≤N) (hQ : 0<Q) (_hL : 0<L) (hQY : Q≤2*N^52)
    (s : Finset ℕ) (hs : ∀ q ∈ s, q ∈ Icc 1 Q)
    {C W : ℝ} (hC : 0≤C) (hW : 1≤W)
    (ht : ∑ q ∈ s, windowMass row Y q ≤ C/(L:ℝ)^(15/16:ℝ))
    (hl : W ≤ (L:ℝ)^(15/16:ℝ))
    (hc : (Q:ℝ)^2*N ≤ 4*(N:ℝ)^64*W) :
    ∑ n ∈ range (N^64+1), ‖windowBand row Y s n‖^2 ≤ 1764*C*(N:ℝ)^64 := by
  have hN' : (1:ℝ)≤N := by exact_mod_cast hN
  have hWp : 0<W := by linarith
  have h64 : 1≤(N:ℝ)^64 := one_le_pow₀ hN'
  have hh := harmonic_scale hN hQ hQY
  have hR := window_sieve row Y (N^64+1) Q s hs
  push_cast at hR
  have hf : (N:ℝ)^64+1+2*(Q:ℝ)^2*(harmonic (Q^2):ℝ) ≤ 882*(N:ℝ)^64*W := by
    nlinarith only [hc,mul_le_mul_of_nonneg_left hh (sq_nonneg (Q:ℝ)),
      mul_nonneg (sub_nonneg.mpr hW) (pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) 64),h64]
  apply hR.trans
  have hE := ht.trans (div_le_div_of_nonneg_left hC hWp hl)
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hf (by norm_num : (0:ℝ)≤2)) hE
    (sum_nonneg fun q _ => sum_nonneg fun _ _ => sq_nonneg _) (by positivity)).trans
  apply le_of_eq; field_simp; ring

private lemma power_floor {N k l : ℕ} (hN : 1≤N) (hkl : (k:ℝ) ≤ l*(15/16:ℝ)) :
    (N:ℝ)^k ≤ (↑(N^l : ℕ):ℝ)^(15/16:ℝ) := by
  rw [Nat.cast_pow,← Real.rpow_natCast_mul (Nat.cast_nonneg _),← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hkl

/-- Uniform second moment for every fixed-width numerator window. The bound
may depend on the width and is independent of the common denominator cutoff. -/
theorem window_variance {row : ℕ → ℕ} {width : ℕ} (hrow : ∀ d, row d≤width*d) :
    ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ, 1≤N →
    ∑ n ∈ range (N^64+1), ‖windowExtension row (2*N^52) n‖^2 ≤ K*(N:ℝ)^64 := by
  obtain ⟨C,hC,ht⟩ := windowEnergy_tail hrow
  refine ⟨15876*C,by positivity,?_⟩
  intro N hN
  let Y := 2*N^52
  let A := Icc 1 (N^28)
  let B := Ioc (N^28) (N^44)
  let D := Ioc (N^44) Y
  have hN' : 1≤(N:ℝ) := by exact_mod_cast hN
  have hab : N^28≤N^44 := Nat.pow_le_pow_right hN (by decide)
  have hbd : N^44≤Y := (Nat.pow_le_pow_right hN (by decide : 44≤52)).trans (by dsimp [Y]; omega)
  have h28 := Nat.one_le_pow 28 N (by omega)
  have h44 := Nat.one_le_pow 44 N (by omega)
  have hA : ∑ n ∈ range (N^64+1), ‖windowBand row Y A n‖^2 ≤ 1764*C*(N:ℝ)^64 := by
    apply band_scale row (L:=1) hN h28 (by decide) (hab.trans hbd) A (by intros; assumption) hC (le_refl 1)
      (ht Y 1 (by decide) A (fun q hq => (mem_Icc.mp hq).1)) (by norm_num)
    have h := pow_le_pow_right₀ hN' (by decide : 57≤64)
    push_cast; nlinarith only [h,pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) 64]
  have hB : ∑ n ∈ range (N^64+1), ‖windowBand row Y B n‖^2 ≤ 1764*C*(N:ℝ)^64 := by
    apply band_scale row hN h44 h28 hbd B (by
      intro q h; exact mem_Icc.mpr ⟨h28.trans (mem_Ioc.mp h).1.le,(mem_Ioc.mp h).2⟩) hC (one_le_pow₀ hN' (n:=26))
      (ht Y (N^28) h28 B (fun q h => (mem_Ioc.mp h).1.le)) (power_floor hN (by norm_num))
    have hh := pow_le_pow_right₀ hN' (by decide : 89≤90)
    push_cast; nlinarith only [hh,pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) 90]
  have hD : ∑ n ∈ range (N^64+1), ‖windowBand row Y D n‖^2 ≤ 1764*C*(N:ℝ)^64 := by
    apply band_scale row hN (h44.trans hbd) h44 (le_refl _) D (by
      intro q h; exact mem_Icc.mpr ⟨h44.trans (mem_Ioc.mp h).1.le,(mem_Ioc.mp h).2⟩) hC (one_le_pow₀ hN' (n:=41))
      (ht Y (N^44) h44 D (fun q h => (mem_Ioc.mp h).1.le)) (power_floor hN (by norm_num))
    dsimp [Y]; push_cast; ring_nf; rfl
  have he (n : ℕ) : windowExtension row Y n = windowBand row Y A n+windowBand row Y B n+windowBand row Y D n := by
    change windowBand row Y (Icc 1 Y) n=_
    rw [band_cut row Y _ _ _ h44 hbd,band_cut row Y _ _ _ h28 hab]
  change ∑ n ∈ range (N^64+1), ‖windowExtension row Y n‖^2 ≤ _
  simp_rw [he]
  apply (sum_le_sum (fun n _ => sum_three_sq _ _ _)).trans
  rw [← mul_sum,sum_add_distrib,sum_add_distrib]
  linarith

/-- Uniform finite second moment for a common power-sized cutoff. The ambient average covers
all integers, and the normalized bound is independent of the scale. -/
theorem interval_variance : ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ, 1≤N →
    ∑ n ∈ range (N^64+1), ‖extension (2*N^52) n‖^2 ≤ K*(N:ℝ)^64 :=
  window_variance (row:=fun d => d-1) (width:=1) (fun d => by simp)

end Arxiv.«2501.03234».ThetaReciprocalVariance
#print axioms Arxiv.«2501.03234».ThetaReciprocalVariance.interval_variance
#print axioms Arxiv.«2501.03234».ThetaReciprocalVariance.window_variance
