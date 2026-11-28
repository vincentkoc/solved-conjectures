import Erdos722SteinerWeights
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Prime.Factorial

/-! # Exact arithmetic for Steiner systems with one-point block excess

For S(r,r+1,v), the binomial tests say that v-r has no prime divisor at
most r+1. In particular, at v=2(r+1) they say exactly that r+2 is prime.
-/

namespace Erdos722.UnitExcess
open Finset IntegralDesign

private theorem lucas_one {p m : ℕ} (hp : p.Prime) (hm : p∣m) :
    (m+(p-1)).choose (p-1) ≡ 1 [MOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  have lt : p-1<p := by have := hp.two_le; omega
  have rem : (m+(p-1))%p=p-1 := by simp [Nat.add_mod,Nat.mod_eq_zero_of_dvd hm,Nat.mod_eq_of_lt lt]
  simpa only [rem,Nat.mod_eq_of_lt lt,Nat.div_eq_of_lt lt,Nat.choose_self,Nat.choose_zero_right,mul_one] using
    (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n:=m+(p-1)) (k:=p-1) (p:=p))

/-- The canonical divisibility tests at block size r+1 for all v≥r. -/
theorem tests_iff {r v : ℕ} (hv : r≤v) :
    (∀ i<r, (r+1-i).choose (r-i) ∣ (v-i).choose (r-i)) ↔ (v-r).Coprime (r+1).factorial := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨p,hp,hdiv,hfact⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have small := hp.dvd_factorial.mp hfact
    have two := hp.two_le
    let i := r-(p-1)
    have hi : i<r := by dsimp [i]; omega
    have htest := h i hi
    have j : r-i=p-1 := by dsimp [i]; omega
    have d : r+1-i=(p-1)+1 := by omega
    have n : v-i=(v-r)+(p-1) := by omega
    rw [j,d,Nat.choose_succ_self_right,show p-1+1=p by omega,n] at htest
    have one := (lucas_one hp hdiv).symm.trans (Nat.modEq_zero_iff_dvd.mpr htest)
    exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp one)
  · intro hc i hi
    let j := r-i
    have d : r+1-i=j+1 := by dsimp [j]; omega
    rw [d,Nat.choose_succ_self_right]
    have cd : (j+1).Coprime (v-r) := (hc.of_dvd_right (Nat.dvd_factorial (by omega) (by dsimp [j]; omega))).symm
    have step := Nat.choose_succ_right_eq (v-i) j
    have eq : v-i-j=v-r := by dsimp [j]; omega
    rw [eq] at step
    apply cd.dvd_mul_right.mp
    rw [← step]
    exact dvd_mul_left _ _

theorem signed_iff {r v : ℕ} (hv : r+1≤v) :
    (∃ w, Represents (univ : Finset (Fin v)) r (r+1) (fun _ => 1) w) ↔
      (v-r).Coprime (r+1).factorial :=
  (signed_steiner_iff v r (r+1) (by omega) hv).trans (tests_iff (by omega))

theorem central_tests (r : ℕ) :
    (∀ i<r, (r+1-i).choose (r-i) ∣ (2*(r+1)-i).choose (r-i)) ↔ (r+2).Prime := by
  rw [tests_iff (by omega),show 2*(r+1)-r=r+2 by omega]
  constructor
  · intro h
    have hm := (Nat.coprime_factorial_iff (m:=r+2) (n:=r+1) (by omega)).mp h
    have eq := Nat.minFac_le (show 0<r+2 by omega)
    exact (Nat.minFac_prime (show r+2≠1 by omega)) |> fun hp => by rwa [show (r+2).minFac=r+2 by omega] at hp
  · exact fun h => h.coprime_factorial_of_lt (by omega)

#print axioms tests_iff
#print axioms signed_iff
#print axioms central_tests
end Erdos722.UnitExcess
