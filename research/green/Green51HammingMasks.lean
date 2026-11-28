import Green51MissingMaskEdits
import Green51HammingCover
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-! # Exact realization of every Hamming missing-direction subset -/

namespace Green51MissingMasks
open Finset Green53ParityThreshold Green51Hyperplane Green51DeletionRadius
open scoped Classical Pointwise

private theorem catalan_double {s : ℕ} (pos : 0 < s) : 2*catalan s ≤ catalan (s+1) := by
  have h := Nat.succ_mul_centralBinom_succ s
  rw [←succ_mul_catalan_eq_centralBinom (s+1), ←succ_mul_catalan_eq_centralBinom s] at h
  have rel : (s+2)*catalan (s+1) = 2*(2*s+1)*catalan s := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < s+1 by omega)
    nlinarith only [h]
  have mul := Nat.mul_le_mul_right (catalan s) (show (s+2)*2 ≤ 2*(2*s+1) by omega)
  exact Nat.le_of_mul_le_mul_left (show (s+2)*(2*catalan s) ≤ (s+2)*catalan (s+1) by nlinarith only [rel,mul]) (by omega)

theorem catalan_margin {s : ℕ} (hs : 5 ≤ s) : 3*(2*s+3) < catalan s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num [catalan_eq_centralBinom_div,Nat.centralBinom,Nat.choose]
  | succ s hs h => have := catalan_double (show 0<s by omega); omega

private theorem choose_step (s : ℕ) :
    4*(2*s).choose s = (2*(s+1)).choose (s+1) + 2*catalan s := by
  change 4*s.centralBinom = (s+1).centralBinom + 2*catalan s
  have h := Nat.succ_mul_centralBinom_succ s
  have c := succ_mul_catalan_eq_centralBinom s
  apply Nat.eq_of_mul_eq_mul_left (show 0 < s+1 by omega)
  nlinarith only [h,c]

theorem small_edit_keeps_double {s r : ℕ} (hs : 5 ≤ s) {B : Finset (𝔽₂ (2*(s+1)+r))}
    (sub : B ⊆ ball (s+1) r) (loss : (ball (s+1) r \ B).card ≤ 3*(2*s+3)*2^r) :
    B+B = ball (s+1) r + ball (s+1) r := by
  by_contra ne
  have low := (cylinder_deletion_radius (s := s) (r := r) (by omega)).2 ⟨B,sub,ne,rfl⟩
  have room := Nat.mul_lt_mul_of_pos_right (catalan_margin hs) (show 0 < 2^r by positivity)
  have layers : 2 * catalan s ≤ (2*s).choose s := by
    rw [←Nat.centralBinom_eq_two_mul_choose, ←succ_mul_catalan_eq_centralBinom]
    exact Nat.mul_le_mul_right _ (by omega)
  have scaled := Nat.mul_le_mul_left (2^r) layers
  have twice : 2*(catalan s*2^r) ≤ 2^r * (2*s).choose s := by
    calc
      _ = 2^r * (2*catalan s) := by ring
      _ ≤ _ := scaled
  omega

theorem density_after_edit {s r : ℕ} (hs : 5 ≤ s) (A : Finset (𝔽₂ (2*(s+1)+r)))
    (bound : (ball (s+1) r).card ≤ A.card + 3*(2*s+3)*2^r) :
    threshold (2*s) < (A.dens : ℝ) := by
  obtain ⟨size, _, _⟩ := hamming_ball_data (s+1) r
  have room := Nat.mul_lt_mul_of_pos_right (catalan_margin hs) (show 0 < 2^r by positivity)
  have step := congrArg (fun x : ℕ => 2^r * x) (choose_step s)
  have num : (2:ℕ)^(2*(s+1)+r) < 2*A.card + (2^r*4)*(2*s).choose s := by
    nlinarith only [size,room,step,bound]
  have realNum : (2:ℝ)^(2*(s+1)+r) < 2*A.card + ((2:ℝ)^r*4)*((2*s).choose s:ℝ) := by exact_mod_cast num
  rw [threshold, Nat.mul_div_cancel_left _ (by decide : 0<2), nnratCast_dens]
  unfold halfLayer
  simp only [𝔽₂,𝔽,Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
  have split : (2:ℝ)^(2*(s+1)+r) = 4*(2:ℝ)^(2*s)*2^r := by rw [pow_add, Nat.mul_add, pow_add]; ring
  rw [split] at realNum ⊢
  apply (lt_div_iff₀ (by positivity)).mpr
  field_simp at *
  nlinarith only [realNum]

end Green51MissingMasks
#print axioms Green51MissingMasks.catalan_margin
#print axioms Green51MissingMasks.small_edit_keeps_double
#print axioms Green51MissingMasks.density_after_edit

namespace Green51MissingMasks
open Finset Green53ParityThreshold Green51Hyperplane Green51DeletionRadius
open scoped Classical Pointwise

theorem realize_cylinder_mask {s r : ℕ} (hs : 5 ≤ s) (J : Finset (𝔽₂ (2*(s+1)+r)))
    (sub : J ⊆ (ball (s+1) r + ball (s+1) r)ᶜ) :
    ∃ A : Finset (𝔽₂ (2*(s+1)+r)), (A+A)ᶜ = J ∧ threshold (2*s) < (A.dens : ℝ) ∧
      (ball (s+1) r \ A).card ≤ 3*J.card ∧ (A \ ball (s+1) r).card ≤ 3 := by
  classical
  let H := ball (s+1) r
  obtain ⟨T, sizes, last, allBits, dist⟩ := three_supports (ι := Fin (2*(s+1))) hs (by simp; omega)
  obtain ⟨X, three, within, cover, unique⟩ := centres_of_supports (r := r) T sizes last allBits dist
  have total := (hamming_ball_data (s+1) r).2.1
  have cap : X.card * J.card ≤ 3*(2*s+3)*2^r := by
    calc
      _ ≤ 3*((H+H)ᶜ.card) := Nat.mul_le_mul three (card_le_card sub)
      _ = _ := by change 3*((ball (s+1) r + ball (s+1) r)ᶜ.card) = _; rw [total]; ring
  obtain ⟨A, actual, count, cut, fresh⟩ := prescribe H X J sub
    (fun B b loss => small_edit_keeps_double hs b (loss.trans cap)) within cover unique
  exact ⟨A, actual, density_after_edit hs A (count.trans (Nat.add_le_add_left cap _)),
    cut.trans (Nat.mul_le_mul_right _ three), fresh.trans three⟩

end Green51MissingMasks
#print axioms Green51MissingMasks.realize_cylinder_mask
