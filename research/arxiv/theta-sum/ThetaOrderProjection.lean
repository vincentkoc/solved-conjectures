import ThetaPointwiseParity

/-! Character-order projections as exact integer counts on rotations of the odd representatives. -/
namespace Arxiv.«2501.03234».ThetaOrderProjection
open Finset Complex DirichletCharacter ThetaFourier ThetaPointwiseCubic
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def rotated (p : ℕ) [NeZero p] (t : ZMod p) : ℕ :=
  ∑ a∈odds p,∑ b∈odds p, if t*a*b∈odds p then 1 else 0

theorem rotated_fourier (t : ZMod p) :
    (p.totient:ℂ)*rotated p t=∑ χ : DirichletCharacter ℂ p,χ t*cubic χ := by
  classical
  simp only [rotated,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,mul_sum]
  simp_rw [count (odds p) (fun _ h => unit_odd h),sum_comm (s:=odds p) (t:=univ)]
  apply sum_congr rfl; intro χ _
  have hf (a b c : ZMod p) : χ (t*a)*χ b*χ⁻¹ c = χ t*(χ a*χ b*χ⁻¹ c) := by rw [map_mul]; ring
  simp only [hf,cubic,halfSum,pow_two,←mul_sum,←sum_mul]

private lemma eval_generator (g : (ZMod p)ˣ) (hg : orderOf g=Nat.card (ZMod p)ˣ)
    (χ : DirichletCharacter ℂ p) (d : ℕ) :
    χ (g:ZMod p)^d=1 ↔ orderOf χ ∣ d := by
  rw [orderOf_dvd_iff_pow_eq_one,←MulChar.pow_apply_coe]
  constructor
  · intro h
    apply MulChar.ext; intro a
    have ht : Subgroup.zpowers g=⊤ := (Subgroup.card_eq_iff_eq_top _).mp (by rw [Nat.card_zpowers,hg])
    have ha : a∈Subgroup.zpowers g := ht.symm ▸ Subgroup.mem_top a
    obtain ⟨j,hj⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr ha)
    rw [MulChar.one_apply_coe,←hj,Units.val_pow_eq_pow_val,map_pow,h,one_pow]
  · intro h; rw [h,MulChar.one_apply_coe]

theorem projection (g : (ZMod p)ˣ) (hg : orderOf g=Nat.card (ZMod p)ˣ) (d q : ℕ)
    (hdq : d*q=orderOf g) :
    (p.totient:ℂ)*∑ i∈range q,(rotated p ((g:ZMod p)^(d*i)):ℂ) =
      (q:ℂ)*∑ χ : DirichletCharacter ℂ p with orderOf χ∣d,cubic χ := by
  classical
  rw [mul_sum]
  simp_rw [rotated_fourier,map_pow,pow_mul]
  rw [sum_comm]
  simp only [sum_filter,mul_sum]
  apply sum_congr rfl; intro χ _
  rw [←sum_mul]
  by_cases h : orderOf χ ∣ d
  · simp [(eval_generator g hg χ d).mpr h,h]
  · have hn := mt (eval_generator g hg χ d).mp h
    have hpow : (χ (g:ZMod p)^d)^q=1 := by
      rw [←pow_mul,hdq,←map_pow,←Units.val_pow_eq_pow_val,pow_orderOf_eq_one,Units.val_one,map_one]
    have hz : (∑ i∈range q, (χ (g:ZMod p)^d)^i)=0 :=
      (mul_eq_zero.mp ((geom_sum_mul _ _).trans (by rw [hpow,sub_self]))).resolve_right (sub_ne_zero.mpr hn)
    simp [h,hz]

#print axioms rotated_fourier
#print axioms projection
end
end Arxiv.«2501.03234».ThetaOrderProjection
