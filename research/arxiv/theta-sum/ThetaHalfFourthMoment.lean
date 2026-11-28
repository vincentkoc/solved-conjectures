import ThetaHalfSpectrum

/-! Uniform fourth moments for the nonprincipal half-character sums. -/
namespace Arxiv.«2501.03234».ThetaHalfFourthMoment
open Finset Filter Real DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCompletion
open ThetaPointwiseCutoff ThetaCharacterFourthMoment ThetaHalfSpectrum
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def momentConstant := 1+|freqConstant|^3

theorem constant_pos : 0 < momentConstant := by unfold momentConstant; positivity

theorem fourth_bound (hp : _root_.Odd p) :
    ∑ χ∈nonprincipal p,‖halfSum χ‖^4 ≤ momentConstant*(p:ℝ)^3 := by
  classical
  let u (x : U p) := ‖freq x‖^(1/3:ℝ)
  have hn (x : U p) : 0≤u x := rpow_nonneg (norm_nonneg _) _
  have hf (x : U p) : ‖freq x‖≤(u x)^3 := by
    dsimp [u]; rw [←rpow_mul_natCast (norm_nonneg _)]; norm_num
  have hu (x : U p) : (u x)^4=‖freq x‖^(4/3:ℝ) := by
    dsimp [u]; rw [←rpow_mul_natCast (norm_nonneg _)]; norm_num
  have H := fourth (p:=p) freq u hn hf
  simp_rw [hu] at H
  have hC : (∑ x : U p,‖freq x‖^(4/3:ℝ))^3 ≤ momentConstant := by
    apply (pow_le_pow_left₀ (sum_nonneg (fun _ _ => rpow_nonneg (norm_nonneg _) _))
      ((freq_sum hp).trans (le_abs_self _)) 3).trans
    unfold momentConstant; linarith
  have hperm : ∑ χ : DirichletCharacter ℂ p,‖transform freq χ⁻¹‖^4 =
      ∑ χ : DirichletCharacter ℂ p,‖transform freq χ‖^4 :=
    Equiv.sum_comp (Equiv.inv _) (fun χ => ‖transform freq χ‖^4)
  have hx : 0≤(p:ℝ) := Nat.cast_nonneg _
  have ht (χ : DirichletCharacter ℂ p) (hχ : χ∈nonprincipal p) :
      ‖halfSum χ‖^4=(p:ℝ)^2*‖transform freq χ⁻¹‖^4 := by
    have hne := (mem_filter.mp hχ).2
    rw [complete hne,norm_mul,mul_pow,ThetaConductorDecay.gauss_norm χ (primitive hne),
      show (Real.sqrt p)^4=((Real.sqrt p)^2)^2 by ring,Real.sq_sqrt hx]
  rw [sum_congr rfl ht,←mul_sum]
  have less := sum_le_sum_of_subset_of_nonneg (filter_subset (fun χ : DirichletCharacter ℂ p => χ≠1) univ)
    (fun χ _ _ => pow_nonneg (norm_nonneg (transform freq χ⁻¹)) 4)
  have hφ : (p.totient:ℝ)≤p := by exact_mod_cast Nat.totient_le p
  change (∑ χ∈nonprincipal p,‖transform freq χ⁻¹‖^4)≤_ at less
  rw [hperm] at less
  exact (mul_le_mul_of_nonneg_left (less.trans (H.trans (mul_le_mul hφ hC
    (pow_nonneg (sum_nonneg (fun _ _ => rpow_nonneg (norm_nonneg _) _)) _) hx))) (sq_nonneg _)).trans_eq (by ring)

#print axioms fourth_bound
end
end Arxiv.«2501.03234».ThetaHalfFourthMoment
