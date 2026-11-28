import ThetaFourierBound
import ThetaConductorDecay
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! Exact multiplicative-character cubic expansion at the prime being evaluated. -/
namespace Arxiv.«2501.03234».ThetaPointwiseCubic
open Finset Complex DirichletCharacter ThetaFourier
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def halfSum (χ : DirichletCharacter ℂ p) := ∑ a∈odds p,χ a

def cubic (χ : DirichletCharacter ℂ p) := (halfSum χ)^2*halfSum χ⁻¹

lemma unit_odd {c : ZMod p} (hc : c∈odds p) : IsUnit c := by
  apply isUnit_iff_ne_zero.mpr
  intro h; subst c; simp [odds] at hc

lemma count (A : Finset (ZMod p)) (hA : ∀ c∈A,IsUnit c) (a b : ZMod p) :
    (p.totient:ℂ)*(if a*b∈A then 1 else 0)=
      ∑ c∈A,∑ χ : DirichletCharacter ℂ p,χ a*χ b*χ⁻¹ c := by
  classical
  have h (c : ZMod p) (hc : c∈A) : (∑ χ : DirichletCharacter ℂ p,χ a*χ b*χ⁻¹ c)=
      if c=a*b then (p.totient:ℂ) else 0 := by
    have hh := sum_char_inv_mul_char_eq (R:=ℂ) (hA c hc) (a*b)
    apply Eq.trans _ hh
    apply sum_congr rfl; intro χ _
    rw [map_mul,MulChar.inv_apply']; ring
  rw [sum_congr rfl h,sum_ite_eq']
  split_ifs <;> simp

theorem expansion (hp : _root_.Odd p) :
    (p.totient:ℂ)*(S p:ℂ)=4*∑ χ : DirichletCharacter ℂ p with χ≠1,cubic χ := by
  classical
  let A := odds p
  have hN : (p.totient:ℂ)*triples A=∑ χ : DirichletCharacter ℂ p,cubic χ := by
    simp only [triples,mul_sum]
    simp_rw [count A (fun _ h => unit_odd h),sum_comm (s:=A) (t:=univ)]
    apply sum_congr rfl; intro χ _
    simp only [cubic,halfSum,pow_two,←mul_sum,←sum_mul,A]
  have h1 : halfSum (1:DirichletCharacter ℂ p)=A.card := by
    unfold halfSum
    exact (sum_congr rfl (fun a ha => MulChar.one_apply (unit_odd ha))).trans (by simp [A])
  have hc : cubic (1:DirichletCharacter ℂ p)=(A.card:ℂ)^3 := by simp [cubic,h1]; ring
  have ht : (p.totient:ℂ)=2*(A.card:ℂ) := by
    rw [Nat.totient_prime (Fact.out : p.Prime),show A.card=p/2 from card_odds (Nat.odd_iff.mp hp)]
    exact_mod_cast (by have := Nat.odd_iff.mp hp;omega : p-1=2*(p/2))
  have hev := sum_erase_add (univ : Finset (DirichletCharacter ℂ p)) cubic (mem_univ 1)
  have hf : (univ : Finset (DirichletCharacter ℂ p)).filter (·≠1)=univ.erase 1 := by ext; simp
  rw [hf,S_trip (Nat.odd_iff.mp hp)]
  change (p.totient:ℂ)*(4*triples A-2*(A.card:ℂ)^2)=_
  rw [hc] at hev
  linear_combination 4*hN-4*hev-2*(A.card:ℂ)^2*ht

#print axioms expansion
end
end Arxiv.«2501.03234».ThetaPointwiseCubic
