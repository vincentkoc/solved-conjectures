import ThetaHighOrderGrowth

/-! Exact excluded orders at the prime where S is evaluated. -/
namespace Arxiv.«2501.03234».ThetaPointwiseParity
open Finset Complex DirichletCharacter ThetaFourier ThetaPointwiseCubic
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem half_zero (hp : _root_.Odd p) {χ : DirichletCharacter ℂ p} (hn : χ ≠ 1)
    (he : χ.Even) : halfSum χ = 0 := by
  classical
  let f (x : ZMod p) := if x ∈ odds p then χ x else 0
  have point (x : ZMod p) : f x + f (-x) = χ x := by
    by_cases hx : x = 0
    · subst x; simp [f,odds,MulChar.map_zero]
    let : NeZero x := ⟨hx⟩
    have hv := ZMod.val_neg_of_ne_zero x
    have hl := x.val_lt
    have hpo := Nat.odd_iff.mp hp
    by_cases h : x.val % 2 = 1
    · have h' : (-x).val % 2 ≠ 1 := by omega
      simp [f,odds,h,h']
    · have h' : (-x).val % 2 = 1 := by omega
      simp [f,odds,h,h',he.eval_neg]
  have hs := sum_congr (s₁:=univ) rfl (fun x _ => point x)
  have perm : ∑ x : ZMod p, f (-x) = ∑ x, f x := by
    exact Fintype.sum_equiv (Equiv.neg _) _ _ (by simp)
  rw [sum_add_distrib,perm,MulChar.sum_eq_zero_of_ne_one hn] at hs
  have hh : halfSum χ = ∑ x, f x := by
    unfold halfSum f
    rw [←sum_filter]; simp
  rw [hh]; linear_combination hs/2

theorem even_of_order_dvd_half (hp : _root_.Odd p) {χ : DirichletCharacter ℂ p}
    (hd : orderOf χ ∣ (p-1)/2) : χ.Even := by
  have hprime : p.Prime := Fact.out
  obtain ⟨g,hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α:=(ZMod p)ˣ)).mp inferInstance
  have hc : orderOf g = p-1 := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,Nat.totient_prime hprime] using hg
  let n := (p-1)/2
  have hp2 := hprime.two_le
  have ho := Nat.odd_iff.mp hp
  have h2 : n+n=p-1 := by dsimp [n]; omega
  have hn : 0<n := by dsimp [n]; omega
  have hg2 : (g^n : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hc] at this
    have := Nat.le_of_dvd hn this
    omega
  have hsq : ((g:ZMod p)^n)^2 = 1 := by
    rw [pow_two,←pow_add,h2,←hc,←Units.val_pow_eq_pow_val,pow_orderOf_eq_one,Units.val_one]
  have hneg : (g:ZMod p)^n = -1 := (sq_eq_one_iff.mp hsq).resolve_left (by
    intro h; apply hg2; apply Units.ext; simpa using h)
  change χ (-1) = 1
  rw [←hneg,map_pow,←MulChar.pow_apply_coe,orderOf_dvd_iff_pow_eq_one.mp hd,MulChar.one_apply_coe]

theorem cubic_zero (hp : _root_.Odd p) {χ : DirichletCharacter ℂ p} (hn : χ ≠ 1)
    (hd : orderOf χ ∣ (p-1)/2) : cubic χ = 0 := by
  simp [cubic,half_zero hp hn (even_of_order_dvd_half hp hd)]

/-- Every contributing order contains the whole two-part of p−1. -/
theorem two_power_dvd_order (hp : _root_.Odd p) {χ : DirichletCharacter ℂ p} (hn : χ ≠ 1)
    (hc : cubic χ ≠ 0) {a : ℕ} (ha : 2^a ∣ p-1) : 2^a ∣ orderOf χ := by
  have hprime : p.Prime := Fact.out
  have hcard : Fintype.card (DirichletCharacter ℂ p) = p-1 := by
    simpa only [Nat.card_eq_fintype_card] using
      (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p).trans (Nat.totient_prime hprime)
  obtain ⟨k,hk⟩ := (show orderOf χ ∣ p-1 from hcard ▸ orderOf_dvd_card)
  rcases Nat.even_or_odd k with ⟨j,hj⟩ | hj
  · exfalso
    apply hc (cubic_zero hp hn ?_)
    exact ⟨j,by rw [hk,hj,Nat.mul_add]; omega⟩
  · exact (hj.coprime_two_left.pow_left a).dvd_of_dvd_mul_right (hk ▸ ha)

theorem order_eight (h : p % 8 = 1) {χ : DirichletCharacter ℂ p} (hn : χ ≠ 1)
    (hc : cubic χ ≠ 0) : 8 ∣ orderOf χ := by
  exact two_power_dvd_order (Nat.odd_iff.mpr (by omega)) hn hc (a:=3) (by norm_num; omega)

#print axioms order_eight
#print axioms two_power_dvd_order

#print axioms cubic_zero
#print axioms half_zero
end
end Arxiv.«2501.03234».ThetaPointwiseParity
