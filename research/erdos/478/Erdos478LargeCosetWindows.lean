import Erdos478CosetMassLimit
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.FieldTheory.Finite.Basic

/-! # Prime windows with cosets larger than the square root of the window length -/

namespace Erdos478.QuotientSpacing
open Finset
open scoped Classical
noncomputable section

/-- Realize the requested subgroup order inside the actual residue field. -/
theorem subgroup_of_order (p : ℕ) [hp : Fact p.Prime] (h : ℕ) (div : h∣p-1) :
    ∃ H : Subgroup (ZMod p)ˣ, Nat.card H=h := by
  obtain ⟨v,order⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α:=(ZMod p)ˣ)).mp inferInstance
  rw [Nat.card_eq_fintype_card,ZMod.card_units] at order
  refine ⟨Subgroup.zpowers (v^(orderOf v/h)),?_⟩
  rw [Nat.card_zpowers]
  exact orderOf_pow_orderOf_div (by rw [order]; have := hp.out.two_le; omega) (order ▸ div)

/-- For every scale and prime cutoff there is a genuine subgroup of order
t^6. Every coset meets at most 1+2t^8 factorial positions in each admissible
window of length t^9, wherever the window starts. -/
theorem large_coset_windows (t L : ℕ) (ht : 2≤t) :
    ∃ (p : ℕ) (prime : Fact p.Prime), max L (t^9)<p ∧ p ≡ 1 [MOD t^6] ∧
      ∃ H : Subgroup (ZMod p)ˣ, Nat.card H=t^6 ∧
        ∀ (g : (ZMod p)ˣ) (a : ℕ), 1≤a → a+(t^9-1)<p →
          (hits p a (a+(t^9-1)) (@unitCoset p prime H g)).card≤1+2*t^8 := by
  obtain ⟨p,hp,large,cong⟩ := Nat.exists_prime_gt_modEq_one (max L (t^9)) (by positivity : t^6≠0)
  let prime : Fact p.Prime := ⟨hp⟩
  obtain ⟨H,card⟩ := subgroup_of_order p _ cong.symm.dvd'
  refine ⟨p,prime,large,cong,H,card,?_⟩
  intro g a lo hi
  let M := (hits p a (a+(t^9-1)) (unitCoset p H g)).card
  have b := coset_bound p a _ lo hi H g
  rw [card,Nat.add_sub_cancel_left] at b
  change 8*(M-1)^3≤9*t^6*(t^9-1)^2 at b
  change M≤1+2*t^8
  by_contra! many
  have lower := Nat.pow_le_pow_left (by omega : 2*t^8≤M-1) 3
  have upper := Nat.pow_le_pow_left (Nat.sub_le (t^9) 1) 2
  have b' := b.trans (Nat.mul_le_mul_left (9*t^6) upper)
  have pos : 0<t^24 := by positivity
  nlinarith [Nat.mul_le_mul_left 8 lower]

#print axioms subgroup_of_order
#print axioms large_coset_windows
end
end Erdos478.QuotientSpacing
