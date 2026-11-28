import ThetaFourierBound

/-! A Fourier bound for a cyclic interval smoothed by a shorter interval. -/

open Finset
namespace Arxiv.«2501.03234».ThetaIntervalKernel
open ThetaFourier
variable {p : ℕ} [NeZero p]

def initial (p m : ℕ) [NeZero p] : Finset (ZMod p) :=
  univ.filter fun x => x.val < m

lemma sum_initial {M : Type*} [AddCommMonoid M] {m : ℕ} (hm : m ≤ p) (f : ZMod p → M) :
    ∑ x ∈ initial p m, f x = ∑ i ∈ range m, f (i : ZMod p) := by
  symm
  apply sum_bij (fun (i : ℕ) _ => (i : ZMod p))
  · intro i hi
    have h := mem_range.mp hi
    exact mem_filter.mpr ⟨mem_univ _, by rw [ZMod.val_natCast_of_lt (by omega)]; exact h⟩
  · intro i hi j hj h
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have e := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at e
  · intro x hx
    exact ⟨x.val, mem_range.mpr (mem_filter.mp hx).2, ZMod.natCast_zmod_val _⟩
  · intros; rfl

noncomputable def series (m : ℕ) (t : ZMod p) : ℂ :=
  ∑ i ∈ range m, ZMod.stdAddChar ((i : ZMod p) * t)

lemma amp_initial {m : ℕ} (hm : m ≤ p) (t : ZMod p) :
    amp (initial p m) t = series m t := sum_initial hm _

lemma series_zero (m : ℕ) : series m (0 : ZMod p) = m := by simp [series]

lemma series_le_length (m : ℕ) (t : ZMod p) : ‖series m t‖ ≤ m := by
  exact (norm_sum_le _ _).trans (by simp)

lemma series_le_weight (m : ℕ) {t : ZMod p} (ht : t ≠ 0) : ‖series m t‖ ≤ weight t := by
  have geom : series m t = ∑ i ∈ range m, (ZMod.stdAddChar t)^i := by
    unfold series
    apply sum_congr rfl
    intro i _
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  unfold weight
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr (char_ne_one _ ht)))).mpr
  rw [geom, ← norm_mul, geom_sum_mul]
  exact (norm_sub_le _ _).trans (by norm_num [norm_pow, Circle.norm_coe])

private lemma inv_square_sum {H m : ℕ} (hH : 0 < H) (hm : H ≤ m) :
    ∑ n ∈ Ico (H+1) (m+1), (n : ℝ)⁻¹ ^ 2 ≤ (H : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ n ∈ Ico (H+1) (m+1), (((n-1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹) := by
      apply sum_le_sum
      intro n hn
      have h := (mem_Ico.mp hn).1
      have hn' : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      have hn₀ : 0 < (n : ℝ) := by linarith
      have hd : 0 < (n : ℝ) - 1 := by linarith
      field_simp [hd.ne', hn₀.ne']
      nlinarith
    _ = (H : ℝ)⁻¹ - (m : ℝ)⁻¹ := by
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        rw [sum_Ico_succ_top (by omega), ih]
        simp
    _ ≤ _ := sub_le_self _ (by positivity)

noncomputable def profile (L : ℕ) (t : ZMod p) : ℝ := weight t * min (L : ℝ) (weight t)

lemma profile_mass {L H : ℕ} (hp : p % 2 = 1) (hH : 0 < H) (hHm : H ≤ p/2) :
    ∑ t ∈ univ.erase (0 : ZMod p), profile L t ≤
      2 * ((p : ℝ) * L * harmonic H + (p : ℝ)^2 / H) := by
  let m := p/2
  have hsplit : p = 2*m+1 := by dsimp [m]; omega
  rw [sum_nonzero]
  have href := sum_Ico_reflect (fun n => profile L (n : ZMod p)) 1 (m := m+1) (n := p) (by omega)
  rw [show p+1-(m+1)=m+1 by omega, Nat.add_sub_cancel] at href
  have refl (n : ℕ) (hn : n ∈ Ico 1 (m+1)) :
      profile L ((p-n : ℕ) : ZMod p) = profile L (n : ZMod p) := by
    have := (mem_Ico.mp hn).2
    simp [Nat.cast_sub (show n ≤ p by omega), profile, weight_neg]
  rw [← sum_Ico_consecutive (fun n => profile L (n : ZMod p)) (m:=1) (n:=m+1)
    (k:=p) (by omega) (by omega), ← href, sum_congr rfl refl, ← two_mul]
  gcongr
  rw [← sum_Ico_consecutive (fun n => profile L (n : ZMod p)) (m:=1) (n:=H+1)
    (k:=m+1) (by omega) (by dsimp [m]; omega)]
  have small (n : ℕ) (hn : 0<n) (hnm : n ≤ m) : weight (n : ZMod p) ≤ (p : ℝ) * (n : ℝ)⁻¹ := by
    have h := weight_small (p:=p) hn hnm
    rw [← div_eq_mul_inv]
    exact h.trans (by gcongr; linarith)
  apply add_le_add
  · rw [harmonic_eq_sum_Icc]
    push_cast
    rw [mul_sum, ← Ico_add_one_right_eq_Icc]
    apply sum_le_sum
    intro n hn
    obtain ⟨hn₁,hn₂⟩ := mem_Ico.mp hn
    unfold profile
    calc
      _ ≤ ((p : ℝ) * (n : ℝ)⁻¹) * L := by
        apply mul_le_mul (small n hn₁ (by dsimp [m]; omega)) (min_le_left ..)
          (le_min (by positivity) (by unfold weight; positivity)) (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ ∑ n ∈ Ico (H+1) (m+1), (p : ℝ)^2 * (n : ℝ)⁻¹^2 := by
        apply sum_le_sum
        intro n hn
        obtain ⟨hn₁,hn₂⟩ := mem_Ico.mp hn
        have hs := small n (by omega) (by omega)
        unfold profile
        calc
          _ ≤ ((p : ℝ) * (n : ℝ)⁻¹) * ((p : ℝ) * (n : ℝ)⁻¹) :=
            mul_le_mul hs ((min_le_right ..).trans hs)
              (le_min (by positivity) (by unfold weight; positivity)) (by positivity)
          _ = _ := by ring
      _ ≤ _ := by
        rw [← mul_sum, div_eq_mul_inv]
        gcongr
        exact inv_square_sum hH hHm

#print axioms profile_mass
end Arxiv.«2501.03234».ThetaIntervalKernel
