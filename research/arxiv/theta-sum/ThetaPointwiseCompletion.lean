import ThetaPointwiseCubic

/-! Square-root cancellation for each nonprincipal half-interval character
sum, with the harmonic factor from additive Fourier completion. -/
namespace Arxiv.«2501.03234».ThetaPointwiseCompletion
open Finset Complex DirichletCharacter AddChar ThetaFourier ThetaPointwiseCubic ThetaConductorDecay
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma primitive {χ : DirichletCharacter ℂ p} (hn : χ≠1) : χ.IsPrimitive := by
  have h := (Nat.dvd_prime (Fact.out : p.Prime)).mp χ.conductor_dvd_level
  exact h.resolve_left (mt (eq_one_iff_conductor_eq_one (χ:=χ)).mpr hn)

theorem completed_sum (χ : DirichletCharacter ℂ p) :
    (p:ℂ)*halfSum χ=∑ t : ZMod p,amp (odds p) (-t)*(∑ x : ZMod p,χ x*ZMod.stdAddChar (x*t)) := by
  classical
  let A := odds p
  let g (t : ZMod p) : ℂ := ∑ x : ZMod p,χ x*ZMod.stdAddChar (x*t)
  have H : (p:ℂ)*halfSum χ=∑ t : ZMod p,amp A (-t)*g t := by
    calc _ = ∑ x : ZMod p,χ x*((p:ℂ)*(if x∈A then 1 else 0)) := by
             simp only [A,halfSum,mul_ite,mul_one,mul_zero,←sum_filter,filter_mem_eq_inter,univ_inter,mul_sum]
             apply sum_congr rfl; intro _ _; ring
         _ = _ := by
             simp_rw [←inversion A,mul_sum]
             rw [sum_comm]
             apply sum_congr rfl; intro t _
             simp only [g,mul_sum]; apply sum_congr rfl; intro x _; ring
  exact H

theorem half_bound (hp : _root_.Odd p) (χ : DirichletCharacter ℂ p) (hn : χ≠1) :
    ‖halfSum χ‖ ≤ Real.sqrt p*(harmonic (p/2):ℝ) := by
  classical
  let A := odds p
  let g (t : ZMod p) : ℂ := ∑ x : ZMod p,χ x*ZMod.stdAddChar (x*t)
  have hz : g 0=0 := by simp [g,MulChar.sum_eq_zero_of_ne_one hn]
  have hg (t : ZMod p) (ht : t≠0) : ‖g t‖≤ Real.sqrt p := by
    let u := Units.mk0 t ht
    have he : g t=gaussSum χ (ZMod.stdAddChar.mulShift (u:ZMod p)) := by
      simp [g,gaussSum,AddChar.mulShift_apply,u,mul_comm]
    rw [he,gaussSum_mulShift_eq χ _ u,norm_mul,gauss_norm χ (primitive hn)]
    exact (mul_le_mul_of_nonneg_right ((χ⁻¹).norm_le_one _) (Real.sqrt_nonneg _)).trans_eq (one_mul _)
  have H : (p:ℂ)*halfSum χ=∑ t : ZMod p,amp A (-t)*g t := completed_sum χ
  let D := (univ : Finset (ZMod p)).erase 0
  have he : ∑ t : ZMod p,amp A (-t)*g t=∑ t∈D,amp A (-t)*g t := by
    simp [D,hz]
  have hneg : ∑ t∈D,‖amp A (-t)‖=mass A := by
    unfold mass; apply sum_nbij' (fun t => -t) (fun t => -t) <;> simp [D]
  have hB : ‖∑ t∈D,amp A (-t)*g t‖≤ mass A*Real.sqrt p := by
    apply (norm_sum_le _ _).trans
    rw [←hneg,sum_mul]
    apply sum_le_sum; intro t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hg t (mem_erase.mp ht).1) (norm_nonneg _)
  rw [he] at H
  rw [←H,norm_mul,Complex.norm_natCast] at hB
  have hm := mul_le_mul_of_nonneg_right (mass_odds (Nat.odd_iff.mp hp)) (Real.sqrt_nonneg (p:ℝ))
  have hpos : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  exact (mul_le_mul_iff_right₀ hpos).mp (hB.trans (hm.trans_eq (by ring)))

theorem cubic_bound (hp : _root_.Odd p) (χ : DirichletCharacter ℂ p) (hn : χ≠1) :
    ‖cubic χ‖≤ (Real.sqrt p*(harmonic (p/2):ℝ))^3 := by
  have h := half_bound hp χ hn
  have hi := half_bound hp χ⁻¹ (by simpa using hn)
  rw [cubic,norm_mul,norm_pow,show (Real.sqrt p*(harmonic (p/2):ℝ))^3=(Real.sqrt p*(harmonic (p/2):ℝ))^2*(Real.sqrt p*(harmonic (p/2):ℝ)) by ring]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h 2) hi (norm_nonneg _) (sq_nonneg _)

#print axioms cubic_bound
end
end Arxiv.«2501.03234».ThetaPointwiseCompletion
