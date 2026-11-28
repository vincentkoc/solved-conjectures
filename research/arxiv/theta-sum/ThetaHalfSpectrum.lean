import ThetaCharacterFourthMoment

/-! The additive completion of the odd interval has a uniform 4/3 norm
when its frequencies are normalized by the prime. -/
namespace Arxiv.«2501.03234».ThetaHalfSpectrum
open Finset Complex Real DirichletCharacter ThetaFourier ThetaPointwiseCubic
open ThetaPointwiseCompletion ThetaCharacterFourthMoment
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def freq (u : U p) : ℂ := amp (odds p) (-(u:ZMod p))/(p:ℂ)

private theorem unit_sum {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ u : U p,f (u:ZMod p)=∑ t∈univ.erase 0,f t := by
  apply sum_bij (fun (u : U p) _ => (u:ZMod p))
  · intro u _; simp [u.ne_zero]
  · intro a _ b _ h; exact Units.ext h
  · intro t ht; exact ⟨Units.mk0 t (mem_erase.mp ht).1,mem_univ _,rfl⟩
  · intros; rfl

theorem complete {χ : DirichletCharacter ℂ p} (hn : χ≠1) :
    halfSum χ=gaussSum χ ZMod.stdAddChar*transform freq χ⁻¹ := by
  classical
  let g (t : ZMod p) : ℂ := ∑ x : ZMod p,χ x*ZMod.stdAddChar (x*t)
  have H := completed_sum χ
  change (p:ℂ)*halfSum χ=∑ t : ZMod p,amp (odds p) (-t)*g t at H
  have hz : g 0=0 := by simp [g,MulChar.sum_eq_zero_of_ne_one hn]
  have he : ∑ t : ZMod p,amp (odds p) (-t)*g t = ∑ u : U p,amp (odds p) (-(u:ZMod p))*g u := by
    rw [unit_sum (fun t => amp (odds p) (-t)*g t)]
    simp [hz]
  have hg (u : U p) : g u=χ⁻¹ (u:ZMod p)*gaussSum χ ZMod.stdAddChar := by
    rw [←gaussSum_mulShift_eq]
    simp [g,gaussSum,AddChar.mulShift_apply,mul_comm]
  rw [he] at H
  have hpc : (p:ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply (mul_left_cancel₀ hpc)
  rw [H]; unfold transform freq
  simp only [mul_sum,hg]; apply sum_congr rfl; intro u _
  field_simp

def freqConstant : ℝ := 2*∑' j : ℕ,(j:ℝ)^(-(4:ℝ)/3)

private lemma weight_sum (hp : _root_.Odd p) :
    ∑ t∈univ.erase (0:ZMod p),(weight t/(p:ℝ))^(4/3:ℝ)≤freqConstant := by
  let m := p/2
  let f (n : ℕ) := (weight (n:ZMod p)/(p:ℝ))^(4/3:ℝ)
  have ho := Nat.odd_iff.mp hp
  have hsplit : p=2*m+1 := by dsimp [m]; omega
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rw [sum_nonzero]; change ∑ n∈Ico 1 p,f n ≤ _
  have href := sum_Ico_reflect f 1 (m:=m+1) (n:=p) (by omega)
  rw [show p+1-(m+1)=m+1 by omega,Nat.add_sub_cancel] at href
  have refl (n : ℕ) (hn : n∈Ico 1 (m+1)) : f (p-n)=f n := by
    dsimp only [f]; have := (mem_Ico.mp hn).2
    rw [Nat.cast_sub (by omega),ZMod.natCast_self,zero_sub,weight_neg]
  rw [←sum_Ico_consecutive f (m:=1) (n:=m+1) (k:=p) (by omega) (by omega),
    ←href,sum_congr rfl refl,←two_mul]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hz : Summable (fun j : ℕ => (j:ℝ)^(-(4:ℝ)/3)) := Real.summable_nat_rpow.mpr (by norm_num)
  apply (sum_le_sum ?_).trans (hz.sum_le_tsum _ (by intros; positivity))
  intro n hn
  have hpos := (mem_Ico.mp hn).1
  have hn' : 0<(n:ℝ) := by exact_mod_cast hpos
  have hw := weight_small (p:=p) hpos (by have := (mem_Ico.mp hn).2;dsimp [m] at this; omega)
  have hnon : 0≤weight (n:ZMod p)/(p:ℝ) := by unfold weight; positivity
  have hb : weight (n:ZMod p)/(p:ℝ)≤(n:ℝ)⁻¹ := by
    apply (div_le_iff₀ hx).mpr
    exact hw.trans (by rw [mul_comm (n:ℝ)⁻¹,←div_eq_mul_inv]; apply div_le_div_of_nonneg_left hx.le hn'; linarith)
  dsimp [f]
  apply (rpow_le_rpow hnon hb (by norm_num : (0:ℝ)≤4/3)).trans_eq
  rw [inv_rpow (by positivity),←rpow_neg (by positivity)]; congr 1; ring

theorem freq_sum (hp : _root_.Odd p) : ∑ u : U p,‖freq u‖^(4/3:ℝ) ≤ freqConstant := by
  obtain ⟨v,hv⟩ := two_unit (p:=p) (Nat.odd_iff.mp hp)
  let a : U p := -v
  have hz (u : U p) : (↑(a*u):ZMod p)=2*(-(u:ZMod p)) := by simp [a,hv]
  calc _ ≤ ∑ u : U p,(weight (↑(a*u):ZMod p)/(p:ℝ))^(4/3:ℝ) := by
         apply sum_le_sum; intro u _
         rw [freq,norm_div,Complex.norm_natCast,hz]
         apply rpow_le_rpow (by positivity) _ (by norm_num)
         apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
         exact amp_le_weight (Nat.odd_iff.mp hp) (hz u ▸ (a*u).ne_zero)
       _ = ∑ u : U p,(weight (u:ZMod p)/(p:ℝ))^(4/3:ℝ) :=
         Equiv.sum_comp (Equiv.mulLeft a) (fun u : U p => (weight (u:ZMod p)/(p:ℝ))^(4/3:ℝ))
       _ = _ := unit_sum (fun t : ZMod p => (weight t/(p:ℝ))^(4/3:ℝ))
       _ ≤ _ := weight_sum hp

#print axioms complete
#print axioms freq_sum
end
end Arxiv.«2501.03234».ThetaHalfSpectrum
