import HosoyaSevenSquareClass
import HosoyaNeighborPrimeSupport

/-! Integral quartics and prime support on the neighboring Hosoya diagonals. -/

namespace Arxiv.«2211.10788»

/-- Complete nonnegative solutions for both signs of the quartic of norm 44
with coefficient 245. Both pairs solve the plus-sign equation. -/
theorem quartic_245_norm_forty_four_iff (x y : ℕ) :
    (x^2=245*y^4+44 ∨ x^2+44=245*y^4) ↔ (x=17 ∧ y=1) ∨ (x=767 ∧ y=7) := by
  constructor
  · intro h
    have norm : 5*(7*y^2)^2=245*y^4 := by ring
    have on_diagonal := (either_diagonal_iff_pell (7*y^2)).mpr
      ⟨x,by simpa only [norm] using h⟩
    have roots : y=1 ∨ y=7 := by
      rcases on_diagonal with ⟨n,hn⟩ | (hn | ⟨m,hm⟩)
      · exact False.elim (upper_ne_seven_mul_square n y hn.symm)
      · omega
      · rcases (lower_eq_seven_mul_square_iff m y).mp hm.symm with h|h
        exacts [Or.inl h.2, Or.inr h.2]
    rcases h with hpos | hneg
    · rcases roots with rfl|rfl
      · exact Or.inl ⟨by nlinarith,rfl⟩
      · exact Or.inr ⟨by nlinarith,rfl⟩
    · have hh := congrArg (Nat.castRingHom (ZMod 7)) hneg
      simp only [map_add,map_pow,map_mul,map_ofNat,Nat.coe_castRingHom] at hh
      exact False.elim ((by decide : ∀ a b : ZMod 7, a^2+44 ≠ 245*b^4) _ _ hh)
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> decide

/-- The only powers of seven on the lower diagonal at indices at least two
are seven and 343, at physical indices four and twelve. -/
theorem lower_eq_seven_pow_iff (m k : ℕ) :
    lowerNeighborAtAddTwo m=7^k ↔ (m=2 ∧ k=1) ∨ (m=10 ∧ k=3) := by
  constructor
  · intro he
    have hf : 0 < Nat.fib (m+2) := Nat.fib_pos.mpr (by omega)
    have hl : 1 < lowerNeighborAtAddTwo m := by simp only [lowerNeighborAtAddTwo]; omega
    by_cases hk : k=0
    · simp [hk] at he; omega
    have inj : Function.Injective (fun i : ℕ => (7:ℕ)^i) :=
      (pow_right_strictMono₀ (by decide : 1 < (7:ℕ))).injective
    rcases Nat.even_or_odd k with ⟨s,hs⟩|⟨s,hs⟩
    · have sq : IsSquare (lowerNeighborAtAddTwo m) := ⟨7^s,by rw [he,hs,pow_add]⟩
      obtain rfl := (lowerNeighbor_isSquare_iff m).mp sq
      have hd : 7 ∣ lowerNeighborAtAddTwo 7 := he ▸ dvd_pow_self 7 hk
      exact False.elim ((by decide : ¬ 7 ∣ lowerNeighborAtAddTwo 7) hd)
    · have sq : lowerNeighborAtAddTwo m=7*(7^s)^2 := by
        rw [he,hs,pow_succ,Nat.mul_comm 2 s,pow_mul,mul_comm]
      rcases (lower_eq_seven_mul_square_iff m _).mp sq with ⟨rfl,_⟩|⟨rfl,_⟩
      · exact Or.inl ⟨rfl,inj (he.symm.trans (by decide : lowerNeighborAtAddTwo 2=7^1))⟩
      · exact Or.inr ⟨rfl,inj (he.symm.trans (by decide : lowerNeighborAtAddTwo 10=7^3))⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> decide

/-- Allowing exponent zero, only 1, 7, and 343 occur on either diagonal. -/
theorem seven_power_on_hosoya_unconditional_iff (k : ℕ) :
    ((∃ n, 7^k=lucasFibonacciSum n) ∨ IsLowerNeighborValue (7^k)) ↔
      k=0 ∨ k=1 ∨ k=3 := by
  constructor
  · intro on_diag
    cases k with
    | zero => exact Or.inl rfl
    | succ k =>
      rcases on_diag with ⟨n,h⟩ | (h | ⟨m,h⟩)
      · exact False.elim (upper_ne_positive_seven_power n k h.symm)
      · have hd : 7 ∣ 3 := h ▸ dvd_pow_self 7 (Nat.succ_ne_zero k)
        exact False.elim ((by decide : ¬ 7 ∣ 3) hd)
      · rcases (lower_eq_seven_pow_iff m _).mp h.symm with h|h
        exacts [Or.inr (Or.inl h.2),Or.inr (Or.inr h.2)]
  · rintro (rfl|rfl|rfl)
    · exact Or.inl ⟨0,by decide⟩
    · exact Or.inr (Or.inr ⟨2,by decide⟩)
    · exact Or.inr (Or.inr ⟨10,by decide⟩)

/-- The lower entry has a prime divisor absent from its upper neighbor
exactly outside physical indices four and twelve, without a table input. -/
theorem lower_has_private_neighbor_prime_unconditional_iff (m : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ lowerNeighborAtAddTwo m ∧ ¬p ∣ lucasFibonacciSum (m+2)) ↔
      m≠2 ∧ m≠10 := by
  constructor
  · rintro ⟨p,hp,hd,hn⟩
    constructor
    · rintro rfl
      exact hn (hd.trans (by decide))
    · rintro rfl
      change p ∣ 7^3 at hd
      have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp (hp.dvd_of_dvd_pow hd)
      subst p
      exact hn (by decide)
  · rintro ⟨h₂,h₁₀⟩
    by_contra! hn
    have hf : 0 < Nat.fib (m+2) := Nat.fib_pos.mpr (by omega)
    have hl : lowerNeighborAtAddTwo m ≠ 0 := by simp only [lowerNeighborAtAddTwo]; omega
    have he := Nat.eq_prime_pow_of_unique_prime_dvd hl fun {p} hp hd =>
      shared_neighbor_prime hp (hn p hp hd) hd
    rcases (lower_eq_seven_pow_iff m _).mp he with h|h
    exacts [h₂ h.1,h₁₀ h.1]

#print axioms quartic_245_norm_forty_four_iff
#print axioms lower_eq_seven_pow_iff
#print axioms seven_power_on_hosoya_unconditional_iff
#print axioms lower_has_private_neighbor_prime_unconditional_iff

end Arxiv.«2211.10788»
