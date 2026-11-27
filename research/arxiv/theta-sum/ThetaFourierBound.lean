import ThetaDiagonalModEight
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds

/-! An absolute bound for the canonical theta sum by additive Fourier inversion. -/

namespace Arxiv.«2501.03234».ThetaFourier

open Finset
open ThetaDiagonal (U rep sign oddReps)

variable {p : ℕ} [Fact p.Prime]

private def odds (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  univ.filter (fun a => a.val % 2 = 1)

private lemma sum_odds {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ a ∈ oddReps p, f (a : ZMod p) = ∑ a ∈ odds p, f a := by
  apply sum_bij (fun (a : U p) _ => (a : ZMod p))
  · intro a ha
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact Units.ext hab
  · intro b hb
    have ho := (mem_filter.mp hb).2
    have hn : b ≠ 0 := by rintro rfl; simp at ho
    exact ⟨Units.mk0 b hn, mem_filter.mpr ⟨mem_univ _, ho⟩, rfl⟩
  · intros; rfl

private lemma card_odds (hp : p % 2 = 1) : (odds p).card = p / 2 := by
  simpa [ThetaDiagonal.card_oddReps hp] using (sum_odds (p := p) (fun _ => (1 : ℕ))).symm

/-- The unnormalized additive Fourier coefficient, with positive exponent. -/
private noncomputable def amp (A : Finset (ZMod p)) (t : ZMod p) : ℂ :=
  ∑ x ∈ A, ZMod.stdAddChar (x * t)

/-- Number of ordered pairs in A whose product also belongs to A, viewed in ℂ. -/
private noncomputable def triples (A : Finset (ZMod p)) : ℂ :=
  ∑ a ∈ A, ∑ b ∈ A, if a * b ∈ A then 1 else 0

private lemma S_trip (hp : p % 2 = 1) :
    (S p : ℂ) = 4 * triples (odds p) - 2 * ((odds p).card : ℂ)^2 := by
  rw [ThetaDiagonal.S_eq_odd_square hp]
  push_cast
  have hs (a : U p) : (sign a : ℂ) = 2 * (if (a : ZMod p) ∈ odds p then 1 else 0) - 1 := by
    by_cases hh : (a : ZMod p).val % 2 = 1 <;> norm_num [sign, rep, odds, hh]
  simp_rw [hs, Units.val_mul]
  rw [show (∑ j ∈ oddReps p, ∑ h ∈ oddReps p,
      (2 * (if (h : ZMod p) * (j : ZMod p) ∈ odds p then 1 else 0) - 1 : ℂ)) =
      ∑ j ∈ odds p, ∑ h ∈ odds p, (2 * (if h * j ∈ odds p then 1 else 0) - 1 : ℂ) by
    rw [← sum_odds (fun (j : ZMod p) => ∑ h ∈ odds p,
      (2 * (if h * j ∈ odds p then 1 else 0) - 1 : ℂ))]
    apply sum_congr rfl
    intro j _
    exact sum_odds (fun (h : ZMod p) => 2 * (if h * (j : ZMod p) ∈ odds p then 1 else 0) - (1 : ℂ))]
  simp only [triples, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one]
  rw [sum_comm (f := fun a b : ZMod p => (if a * b ∈ odds p then (1 : ℂ) else 0))]
  ring

private lemma orthog (x : ZMod p) :
    ∑ t : ZMod p, ZMod.stdAddChar (x * t) = if x = 0 then (p : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p h)

private lemma inversion (A : Finset (ZMod p)) (z : ZMod p) :
    ∑ t : ZMod p, amp A (-t) * ZMod.stdAddChar (z * t) =
      (p : ℂ) * (if z ∈ A then 1 else 0) := by
  simp only [amp, sum_mul, ← AddChar.map_add_eq_mul]
  rw [sum_comm]
  simp_rw [show ∀ x t : ZMod p, x * -t + z * t = (z - x) * t by intros; ring]
  simp [orthog, sub_eq_zero, sum_ite_eq]

private lemma expand_triples (A : Finset (ZMod p)) :
    (p : ℂ) * triples A =
      ∑ t : ZMod p, amp A (-t) * ∑ a ∈ A, amp A (a * t) := by
  simp only [triples, mul_sum, ← inversion]
  rw [sum_comm]
  -- Move the frequency sum outside both spatial sums.
  calc
    _ = ∑ b ∈ A, ∑ t : ZMod p, ∑ a ∈ A,
        amp A (-t) * ZMod.stdAddChar (a * b * t) := by
          apply sum_congr rfl; intro b _; rw [sum_comm]
    _ = _ := by
      rw [sum_comm]
      simp only [amp, mul_sum]
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      rw [mul_assoc]

private noncomputable def mass (A : Finset (ZMod p)) : ℝ :=
  ∑ t ∈ univ.erase 0, ‖amp A t‖

private lemma mass_nonneg (A : Finset (ZMod p)) : 0 ≤ mass A := sum_nonneg fun _ _ => norm_nonneg _

/-- Scaling the odd representatives by a nonzero frequency samples distinct nonzero frequencies. -/
private lemma norm_slice (A : Finset (ZMod p)) (hA : 0 ∉ A) {t : ZMod p} (ht : t ≠ 0) :
    ‖∑ a ∈ A, amp A (a * t)‖ ≤ mass A := by
  apply (norm_sum_le _ _).trans
  have hi : Set.InjOn (fun a : ZMod p => a * t) A := (mul_left_injective₀ ht).injOn
  rw [← sum_image (f := fun z => ‖amp A z‖) hi]
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    exact mem_erase.mpr ⟨mul_ne_zero (fun h => hA (h ▸ ha)) ht, mem_univ _⟩
  · intros; positivity

/-- Removing the zero frequency leaves an error bounded by the square of the Fourier mass. -/
private lemma trip_error (A : Finset (ZMod p)) (hA : 0 ∉ A) :
    ‖(p : ℂ) * triples A - (A.card : ℂ)^3‖ ≤ (mass A)^2 := by
  classical
  rw [expand_triples, ← sum_erase_add _ _ (mem_univ (0 : ZMod p))]
  simp only [neg_zero, mul_zero, amp, AddChar.map_zero_eq_one, sum_const, nsmul_eq_mul, mul_one]
  change ‖(∑ t ∈ univ.erase 0, amp A (-t) * ∑ a ∈ A, amp A (a * t)) +
    (A.card : ℂ) * ((A.card : ℂ) * A.card) - (A.card : ℂ)^3‖ ≤ _
  rw [show (A.card : ℂ) * ((A.card : ℂ) * A.card) = (A.card : ℂ)^3 by ring, add_sub_cancel_right]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ t ∈ univ.erase 0, ‖amp A (-t)‖ * mass A := by
      apply sum_le_sum
      intro t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_slice A hA (mem_erase.mp ht).1) (norm_nonneg _)
    _ = _ := by
      rw [← sum_mul, sq]
      congr 1
      exact sum_nbij' (fun t => -t) (fun t => -t) (by simp) (by simp) (by simp)
        (by simp) (by simp)

private lemma sum_progression (hp : p % 2 = 1) {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ i ∈ range (p / 2), f ((2 * i + 1 : ℕ) : ZMod p) = ∑ x ∈ odds p, f x := by
  apply sum_bij (fun (i : ℕ) _ => ((2 * i + 1 : ℕ) : ZMod p))
  · intro i hi
    have := mem_range.mp hi
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [ZMod.val_natCast_of_lt (show 2 * i + 1 < p by omega)]
    omega
  · intro i hi j hj h
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have he := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at he
    omega
  · intro x hx
    have ho := (mem_filter.mp hx).2
    have hx' := x.val_lt
    refine ⟨x.val / 2, mem_range.mpr (by omega), ?_⟩
    rw [show 2 * (x.val / 2) + 1 = x.val by omega, ZMod.natCast_zmod_val]
  · intros; rfl

private lemma norm_char (t : ZMod p) : ‖ZMod.stdAddChar t‖ = 1 := Circle.norm_coe _

private noncomputable def weight (t : ZMod p) : ℝ := 2 / ‖ZMod.stdAddChar t - 1‖

private lemma char_ne_one (t : ZMod p) (ht : t ≠ 0) : ZMod.stdAddChar t ≠ 1 := by
  rw [← (ZMod.stdAddChar (N := p)).map_zero_eq_one]
  exact fun h => ht (ZMod.injective_stdAddChar h)

/-- The odd representatives form a progression with common difference two. -/
private lemma amp_le_weight (hp : p % 2 = 1) {t : ZMod p} (ht : 2 * t ≠ 0) :
    ‖amp (odds p) t‖ ≤ weight (2 * t) := by
  let z := ZMod.stdAddChar (2 * t)
  have hz : ‖z‖ = 1 := norm_char _
  have hgeom : amp (odds p) t = (∑ i ∈ range (p / 2), z^i) * ZMod.stdAddChar t := by
    unfold amp
    rw [← sum_progression hp, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
    push_cast
    congr 1
    simp [nsmul_eq_mul]
    ring
  unfold weight
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr (char_ne_one _ ht)))).mpr
  rw [hgeom, norm_mul, norm_char, mul_one, ← norm_mul, geom_sum_mul]
  exact (norm_sub_le _ _).trans (by norm_num [norm_pow, hz])

private lemma weight_neg (t : ZMod p) : weight (-t) = weight t := by
  unfold weight
  congr 1
  have h := norm_mul (ZMod.stdAddChar (-t) - 1) (ZMod.stdAddChar t)
  rw [norm_char, mul_one, sub_mul, one_mul, ← AddChar.map_add_eq_mul, neg_add_cancel,
    AddChar.map_zero_eq_one, norm_sub_rev] at h
  exact h.symm

/-- On the lower half of the circle Jordan’s sine bound gives a reciprocal-frequency bound. -/
private lemma weight_small {n : ℕ} (hn : 0 < n) (hle : n ≤ p / 2) :
    weight (n : ZMod p) ≤ (p : ℝ) / (2 * n) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : (2 : ℝ)*n ≤ p := by exact_mod_cast (show 2 * n ≤ p by omega)
  let x : ℝ := Real.pi * n / p
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxl : x ≤ Real.pi/2 := by
    dsimp [x]
    apply (div_le_iff₀ hp').mpr
    nlinarith [mul_le_mul_of_nonneg_left h2n Real.pi_pos.le]
  have hs := Real.mul_le_sin hx hxl
  have harg : (2 / Real.pi) * x = 2 * n / p := by
    dsimp [x]; field_simp
  rw [harg] at hs
  have he : ‖ZMod.stdAddChar (n : ZMod p) - 1‖ = 2 * Real.sin x := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp,
      ZMod.val_natCast_of_lt (show n < p by omega)]
    rw [show ((2 * Real.pi * ((n : ℝ) / p) : ℝ) : ℂ) * Complex.I =
        Complex.I * ((2 * x : ℝ) : ℂ) by dsimp [x]; push_cast; ring,
      Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show 2 * x/2 = x by ring, Real.norm_eq_abs, abs_of_nonneg]
    positivity [Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_pos])]
  have hspos : 0 < Real.sin x := lt_of_lt_of_le (by positivity) hs
  unfold weight
  rw [he]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := (div_le_iff₀ hp').mp hs
  linarith

private lemma sum_nonzero (f : ZMod p → ℝ) :
    ∑ t ∈ univ.erase 0, f t = ∑ n ∈ Ico 1 p, f (n : ZMod p) := by
  apply sum_bij (fun (t : ZMod p) _ => t.val)
  · intro t ht
    have hz := (mem_erase.mp ht).1
    have hn := mt (ZMod.val_eq_zero t).mp hz
    exact mem_Ico.mpr ⟨by omega, t.val_lt⟩
  · intros; apply ZMod.val_injective p; assumption
  · intro n hn
    obtain ⟨h₁,h₂⟩ := mem_Ico.mp hn
    have he := ZMod.val_natCast_of_lt h₂
    exact ⟨(n : ZMod p), mem_erase.mpr ⟨fun e => by rw [e, ZMod.val_zero] at he; omega,
      mem_univ _⟩, he⟩
  · intros; rw [ZMod.natCast_zmod_val]

/-- Reflect the upper frequencies and sum the reciprocal bound on the lower half. -/
private lemma weight_mass (hp : p % 2 = 1) :
    ∑ t ∈ univ.erase (0 : ZMod p), weight t ≤ (p : ℝ) * harmonic (p / 2) := by
  let m := p / 2
  have hsplit : p = 2 * m + 1 := by dsimp [m]; omega
  rw [sum_nonzero]
  have href := sum_Ico_reflect (fun n => weight (n : ZMod p)) 1 (m := m + 1) (n := p) (by omega)
  rw [show p + 1 - (m + 1) = m + 1 by omega, Nat.add_sub_cancel] at href
  have refl (n : ℕ) (hn : n ∈ Ico 1 (m + 1)) :
      weight ((p - n : ℕ) : ZMod p) = weight (n : ZMod p) := by
    have := (mem_Ico.mp hn).2
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, weight_neg]
  rw [← sum_Ico_consecutive (fun n => weight (n : ZMod p)) (m := 1) (n := m + 1)
    (k := p) (by omega) (by omega), ← href, sum_congr rfl refl, ← two_mul]
  calc
    _ ≤ 2 * ∑ n ∈ Ico 1 (m + 1), (p : ℝ) / (2 * n) := by
      gcongr with n hn
      exact weight_small (mem_Ico.mp hn).1 (by have := (mem_Ico.mp hn).2; dsimp [m] at *; omega)
    _ = _ := by
      rw [mul_sum]
      simp_rw [show ∀ n : ℕ, (2 : ℝ) * (p / (2 * n)) = p * (n : ℝ)⁻¹ by
        intro n; rw [div_eq_mul_inv, mul_inv_rev]; ring]
      rw [← mul_sum, Finset.Ico_add_one_right_eq_Icc, harmonic_eq_sum_Icc]
      push_cast
      rfl

private lemma mass_odds (hp : p % 2 = 1) :
    mass (odds p) ≤ (p : ℝ) * harmonic (p / 2) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hgt : 2 < p := by have := (Fact.out : p.Prime).two_le; omega
    have := ZMod.val_natCast_of_lt hgt
    intro he
    change (2 : ZMod p).val = 2 at this
    rw [he, ZMod.val_zero] at this
    omega
  apply le_trans _ (weight_mass hp)
  calc
    mass (odds p) ≤ ∑ t ∈ univ.erase (0 : ZMod p), weight (2 * t) := by
      apply sum_le_sum
      intro t ht
      exact amp_le_weight hp (mul_ne_zero h2 (mem_erase.mp ht).1)
    _ = _ := by
      apply sum_nbij' (fun t => 2 * t) (fun t => (2 : ZMod p)⁻¹*t)
      all_goals simp [h2]

/-- Centered, explicit harmonic bound for the canonical theta sum at an odd prime. -/
theorem S_centered_harmonic_bound (p : ℕ) (hprime : p.Prime) (hodd : Odd p) :
    |(p : ℝ) * S p + 2 * ((p / 2 : ℕ) : ℝ)^2| ≤ (4 : ℝ) * (p * harmonic (p / 2))^2 := by
  let : Fact p.Prime := ⟨hprime⟩
  have hp := Nat.odd_iff.mp hodd
  let m := p / 2
  have hA : 0 ∉ odds p := by simp [odds]
  have he := trip_error (odds p) hA
  have hm := mass_odds hp
  have hc : (odds p).card = m := card_odds hp
  rw [hc] at he
  have hpm : (p : ℂ) = 2 * (m : ℂ) + 1 := by exact_mod_cast (show p = 2 * m + 1 by dsimp [m]; omega)
  have hs := S_trip hp
  rw [hc] at hs
  have hi : (p : ℂ) * S p + 2 * (m : ℂ)^2 =
        4 * ((p : ℂ) * triples (odds p) - (m : ℂ)^3) := by rw [hs, hpm]; ring
  have hcplx := congrArg norm hi
  rw [norm_mul] at hcplx
  have hreal : ‖(p : ℂ) * S p + 2 * (m : ℂ)^2‖ = |(p : ℝ) * S p + 2 * (m : ℝ)^2| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast
    rfl
  rw [hreal] at hcplx
  change |(p : ℝ) * S p + 2 * (m : ℝ)^2| ≤ _
  rw [hcplx]
  norm_num
  exact he.trans (pow_le_pow_left₀ (mass_nonneg _) hm 2)

/-- A uniform two-sided logarithmic estimate, with all constants explicit. -/
theorem abs_S_le_log_sq (p : ℕ) (hprime : p.Prime) (hodd : Odd p) :
    |(S p : ℝ)| ≤ p * (1 + 4 * (1 + Real.log p)^2) := by
  have hs := S_centered_harmonic_bound p hprime hodd
  have hp : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hmp : ((p / 2 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.div_le_self p 2
  have hmp' : 0 < p / 2 := by have := hprime.two_le; omega
  have hh := (harmonic_le_one_add_log (p / 2)).trans (add_le_add_right
    (Real.log_le_log (by exact_mod_cast hmp') hmp) 1)
  have hh0 : 0 ≤ (harmonic (p / 2) : ℝ) := by
    exact_mod_cast (show 0 ≤ harmonic (p / 2) by unfold harmonic; positivity)
  have hsq := pow_le_pow_left₀ hh0 hh 2
  have hd : (2 : ℝ) * ((p / 2 : ℕ) : ℝ) ≤ p := by exact_mod_cast (show 2*(p / 2) ≤ p by omega)
  have hd2 : (2 : ℝ) * ((p / 2 : ℕ) : ℝ)^2 ≤ p^2 := by
    nlinarith [sq_nonneg ((p : ℝ) - 2*((p / 2 : ℕ) : ℝ)),
      mul_nonneg (sub_nonneg.mpr hd) (Nat.cast_nonneg (p / 2) : (0:ℝ) ≤ _)]
  rw [abs_le] at hs ⊢
  constructor <;> apply (le_of_mul_le_mul_left _ hp) <;>
    nlinarith [mul_nonneg (sq_nonneg (p : ℝ)) (sub_nonneg.mpr hsq)]

open Asymptotics Filter in
/-- Along the primes, the canonical sum grows at most on the scale p times log-squared p. -/
theorem S_isBigO_prime_log_sq :
    (fun p : ℕ => (S p : ℝ)) =O[atTop ⊓ principal {p : ℕ | p.Prime}]
      (fun p : ℕ => (p : ℝ) * (Real.log p)^2) := by
  apply IsBigO.of_bound 17
  rw [eventually_inf_principal]
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with p hp
  intro hprime
  change p.Prime at hprime
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 1 ≤ Real.log p := (Real.le_log_iff_exp_le (by linarith)).mpr
    (Real.exp_one_lt_three.le.trans hp')
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ (p : ℝ) * (Real.log p)^2 by positivity)]
  apply (abs_S_le_log_sq p hprime (hprime.odd_of_ne_two (by omega))).trans
  rw [show (17 : ℝ) * (p * (Real.log p)^2) = p * (17 * (Real.log p)^2) by ring]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg p)
  nlinarith [sq_nonneg (Real.log p - 1)]

open Asymptotics Filter in
/-- Along the primes, S(p) is little-o of every power p^(1+ε) with ε > 0. -/
theorem S_isLittleO_prime_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun p : ℕ => (S p : ℝ)) =o[atTop ⊓ principal {p : ℕ | p.Prime}]
      (fun p : ℕ => (p : ℝ) ^ (1 + ε)) := by
  let l := (atTop : Filter ℕ) ⊓ principal {p : ℕ | p.Prime}
  have hlog : (fun p : ℕ => (Real.log p)^2) =o[l] (fun p : ℕ => (p : ℝ)^ε) := by
    simpa [Real.rpow_two] using
      ((isLittleO_log_rpow_rpow_atTop 2 hε).natCast_atTop.mono
        (show l ≤ atTop from inf_le_left))
  apply S_isBigO_prime_log_sq.trans_isLittleO
  have h := (isBigO_refl (fun p : ℕ => (p : ℝ)) l).mul_isLittleO hlog
  refine h.congr_right (fun p => ?_)
  change (p : ℝ) * (p : ℝ)^ε = (p : ℝ)^(1+ε)
  by_cases hp : p = 0
  · subst p; simp [Real.zero_rpow (show 1 + ε ≠ 0 by linarith)]
  · rw [Real.rpow_add (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)), Real.rpow_one]

open Filter in
/-- The upper inequality of Berndt et al., v3 Conjecture 3.3, for every positive constant. -/
theorem conjecture_3_3_upper {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, p.Prime → (S p : ℝ) < C * (p : ℝ)^(1 + ε) := by
  have h := (S_isLittleO_prime_rpow hε).bound (show 0 < C/2 by positivity)
  rw [eventually_inf_principal] at h
  filter_upwards [h] with p hp
  intro hprime
  specialize hp hprime
  have hpos : 0 < (p : ℝ)^(1 + ε) := Real.rpow_pos_of_pos (by exact_mod_cast hprime.pos) _
  simp only [Real.norm_eq_abs, abs_of_pos hpos] at hp
  exact (le_abs_self _).trans_lt (hp.trans_lt (by nlinarith [mul_pos hC hpos]))

end Arxiv.«2501.03234».ThetaFourier

#print axioms Arxiv.«2501.03234».ThetaFourier.S_centered_harmonic_bound
#print axioms Arxiv.«2501.03234».ThetaFourier.abs_S_le_log_sq
#print axioms Arxiv.«2501.03234».ThetaFourier.S_isBigO_prime_log_sq
#print axioms Arxiv.«2501.03234».ThetaFourier.S_isLittleO_prime_rpow
#print axioms Arxiv.«2501.03234».ThetaFourier.conjecture_3_3_upper
