import ThetaOddInverseCount
import ThetaPointwiseCutoff

/-! The real second moment of the character half-sums is an odd-inverse count. -/
namespace Arxiv.«2501.03234».ThetaRealCharacterMoment
open Finset Complex DirichletCharacter ThetaFourier ThetaPointwiseCubic ThetaPointwiseCutoff ThetaOddInverseCount
open scoped ComplexConjugate
noncomputable section
variable {p : ℕ} [Fact p.Prime]

private lemma expand (f : DirichletCharacter ℂ p → ZMod p → ℂ) :
    (∑ χ : DirichletCharacter ℂ p,halfSum χ*∑ b∈odds p,f χ b) =
      ∑ a∈odds p,∑ b∈odds p,∑ χ : DirichletCharacter ℂ p,χ a*f χ b := by
  simp only [halfSum,sum_mul,mul_sum]
  simp_rw [sum_comm (s:=univ) (t:=odds p)]
  exact sum_comm

theorem square_sum : (∑ χ : DirichletCharacter ℂ p,(halfSum χ)^2) =
    (p.totient:ℂ)*inverseCount p := by
  classical
  simp only [pow_two]
  rw [show (∑ χ : DirichletCharacter ℂ p,halfSum χ*halfSum χ)=_ from expand (fun χ x => χ x)]
  simp_rw [←map_mul,DirichletCharacter.sum_characters_eq]
  calc
    _ = ∑ a∈odds p,if a⁻¹∈odds p then (p.totient:ℂ) else 0 := by
      apply sum_congr rfl; intro a ha
      simp_rw [mul_eq_one_iff_inv_eq₀ (unit_odd ha).ne_zero]
      rw [sum_ite_eq]
    _ = _ := by rw [←sum_filter]; simp [inverseCount,mul_comm]

theorem norm_square_sum : (∑ χ : DirichletCharacter ℂ p,halfSum χ*halfSum χ⁻¹) =
    (p.totient:ℂ)*(odds p).card := by
  classical
  rw [show (∑ χ : DirichletCharacter ℂ p,halfSum χ*halfSum χ⁻¹)=_ from expand (fun χ x => χ⁻¹ x)]
  apply Eq.trans _ (show (∑ a∈odds p,(p.totient:ℂ))=_ by simp [mul_comm])
  apply sum_congr rfl; intro a ha
  calc
    _ = ∑ b∈odds p, if b=a then (p.totient:ℂ) else 0 := by
      apply sum_congr rfl; intro b hb
      simpa only [MulChar.inv_apply',mul_comm] using
        (sum_char_inv_mul_char_eq (R:=ℂ) (unit_odd hb) a)
    _ = _ := by simp [ha]

theorem inverse_half (χ : DirichletCharacter ℂ p) : halfSum χ⁻¹ = conj (halfSum χ) := by
  simp only [halfSum,map_sum]
  apply sum_congr rfl; intro a _; exact (MulChar.star_apply' χ a).symm

theorem cubic_real (χ : DirichletCharacter ℂ p) :
    (cubic χ).re = ‖halfSum χ‖^2*(halfSum χ).re := by
  rw [cubic,inverse_half,pow_two,mul_assoc,mul_conj,Complex.normSq_eq_norm_sq]
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,mul_comm]

theorem real_second_moment (hp : _root_.Odd p) :
    2*(∑ χ∈nonprincipal p,((halfSum χ).re)^2) = (p.totient:ℝ)*inverseCount p := by
  classical
  have point (χ : DirichletCharacter ℂ p) : 2*((halfSum χ).re)^2 =
      ((halfSum χ)^2).re+(halfSum χ*halfSum χ⁻¹).re := by
    simp only [inverse_half,pow_two,Complex.mul_re,conj_re,conj_im]; ring
  have hs := congrArg Complex.re (square_sum (p:=p))
  have hn := congrArg Complex.re (norm_square_sum (p:=p))
  have hR (x y : ℕ) : ((x:ℂ)*(y:ℂ)).re = (x:ℝ)*(y:ℝ) := by simp
  rw [Complex.re_sum,hR] at hs hn
  have h1 : halfSum (1 : DirichletCharacter ℂ p)=(odds p).card := by
    unfold halfSum
    exact (sum_congr rfl (fun a ha => MulChar.one_apply (unit_odd ha))).trans (by simp)
  have hcard : (p.totient:ℝ)=2*(odds p).card := by
    rw [Nat.totient_prime (Fact.out : p.Prime),card_odds (Nat.odd_iff.mp hp)]
    exact_mod_cast (by have := Nat.odd_iff.mp hp; omega : p-1=2*(p/2))
  have hf : nonprincipal p=univ.erase (1 : DirichletCharacter ℂ p) := by ext; simp [nonprincipal]
  have ht := sum_erase_add univ (fun χ : DirichletCharacter ℂ p => ((halfSum χ).re)^2) (mem_univ 1)
  have hall : 2*(∑ χ : DirichletCharacter ℂ p,((halfSum χ).re)^2) =
      (p.totient:ℝ)*inverseCount p+(p.totient:ℝ)*(odds p).card := by
    rw [mul_sum]; simp_rw [point,sum_add_distrib,hs,hn]
  rw [←ht,h1,Complex.natCast_re] at hall
  rw [hf]
  nlinarith only [hall,congrArg (fun z : ℝ => z*((odds p).card:ℝ)) hcard]

#print axioms real_second_moment
#print axioms cubic_real
end
end Arxiv.«2501.03234».ThetaRealCharacterMoment
