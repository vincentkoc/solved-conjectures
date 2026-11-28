import ThetaExceptionalPrimeInput

/-! Enlarge the original modulus by the exceptional conductor exactly when it can affect a row. -/
namespace Arxiv.«2501.03234».ThetaExceptionalConductor
open Finset Real ThetaFiberDiscrepancy ThetaExceptionalPrimeInput ThetaSiegelWalfiszBand
noncomputable section
set_option exponentiation.threshold 1024

def lift (m f : ℕ) := if f ≤ m^769 then m*f else m

theorem bounds {m f : ℕ} (hm : 0 < m) (hf : 0 < f) :
    m∣lift m f ∧ m ≤ lift m f ∧ lift m f ≤ m^770 := by
  unfold lift;split_ifs with hh
  · refine ⟨dvd_mul_right ..,Nat.le_mul_of_pos_right _ hf,?_⟩
    calc m*f ≤ m*m^769 := Nat.mul_le_mul_left _ hh
         _ = _ := (pow_succ' m 769).symm
  · exact ⟨dvd_rfl,le_rfl,Nat.le_self_pow (by decide) m⟩

theorem stable {m f d b j : ℕ} (hm : 0 < m) (hf : 0 < f) (hd : 0 < d)
    (hdy : d ≤ (lift m f)^768) (hj : j%(lift m f)=b) (main : ℝ) (V : ℕ → ℝ) :
    center f ((lift m f)*d) j main V=center f (lift m f) b main V := by
  by_cases h : f ≤ m^769
  · have he : f∣lift m f := by simp [lift,h]
    have he' := he.trans (dvd_mul_right (lift m f) d)
    simp only [center,if_pos he,if_pos he']
    rw [←hj,Nat.mod_mod_of_dvd _ he]
  · have he : lift m f=m := if_neg h
    rw [he] at hdy ⊢
    have hh : m*d ≤ m^769 := calc
      _ ≤ m*m^768 := Nat.mul_le_mul_left _ hdy
      _ = _ := (pow_succ' m 768).symm
    have h₁ : ¬f∣m*d := fun h' => h ((Nat.le_of_dvd (Nat.mul_pos hm hd) h').trans hh)
    have h₂ : ¬f∣m := fun h' => h₁ (h'.trans (dvd_mul_right ..))
    simp [center,h₁,h₂]

theorem on_fiber {N m f b d : ℕ} {main : ℝ} {V : ℕ → ℝ} (hh : Data N f main V)
    (hm : 0 < m) (hf : 0 < f) (hd : 0 < d) (hdy : d ≤ (lift m f)^768)
    (hlim : (((lift m f)^769:ℕ):ℝ) ≤ radius N) :
    OnClass (band N) (weight N) (lift m f) b ((lift m f)*d) (center f (lift m f) b main V) (error N) := by
  intro j hj hmod
  let l := lift m f
  have hl : 0 < l := hm.trans_le (bounds hm hf).2.1
  have hq : l*d ≤ l^769 := calc
    _ ≤ l*l^768 := Nat.mul_le_mul_left l hdy
    _ = _ := (pow_succ' l 768).symm
  have hx := hh (l*d) j (Nat.mul_pos hl hd) ((Nat.cast_le.mpr hq).trans hlim) hj
  dsimp only [l] at hx
  simpa only [stable hm hf hd hdy hmod main V] using hx

theorem lower {N m f b : ℕ} {main κ : ℝ} {V : ℕ → ℝ} (hκ : 0<κ) (hN : 0<log (N:ℝ))
    (hm : 0 < m) (hf : 0 < f) (ha : κ*(N:ℝ)^64/log N ≤ main)
    (hV : ∀ b,κ*(N:ℝ)^64/(log N*(f:ℝ)^2) ≤ V b) :
    κ*(N:ℝ)^64/(log N*(lift m f:ℝ)^2) ≤ center f (lift m f) b main V := by
  have hl := hm.trans_le (bounds hm hf).2.1
  unfold center;split_ifs with h
  · apply le_trans _ (hV _)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr;exact_mod_cast Nat.le_of_dvd hl h
  · apply le_trans _ ha
    apply div_le_div_of_nonneg_left (by positivity) hN
    exact le_mul_of_one_le_right hN.le (one_le_pow₀ (by exact_mod_cast hl : (1:ℝ) ≤ lift m f))

#print axioms on_fiber
#print axioms lower
end
end Arxiv.«2501.03234».ThetaExceptionalConductor
