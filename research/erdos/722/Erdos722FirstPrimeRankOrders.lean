import Erdos722TitsRankOrder
import Erdos722SmallWittExtension

/-! # The first admissible unit-excess order and the small-rank spectrum -/

namespace Erdos722.UnitExcess
open Finset IntegralDesign

private theorem exists_prime_after (r : ℕ) : ∃ p : ℕ, r+1<p ∧ p.Prime := by
  obtain ⟨p,h,hp⟩ := Nat.exists_infinite_primes (r+2)
  exact ⟨p,by omega,hp⟩

noncomputable def nextPrime (r : ℕ) := Nat.find (exists_prime_after r)

theorem next_prime_spec (r : ℕ) : r+1<nextPrime r ∧ (nextPrime r).Prime :=
  Nat.find_spec (exists_prime_after r)

theorem next_le {r p : ℕ} (h : r+1<p) (hp : p.Prime) : nextPrime r≤p :=
  Nat.find_min' (exists_prime_after r) ⟨h,hp⟩

private theorem rough_lower {r n : ℕ} (h : r+1<n) (rough : (n-r).Coprime (r+1).factorial) :
    r+nextPrime r≤n := by
  have hn : n-r≠1 := by omega
  have hit := next_le ((Nat.coprime_factorial_iff hn).mp rough) (Nat.minFac_prime hn)
  have le := Nat.minFac_le (show 0<n-r by omega)
  omega

/-- At block size r+1 the first nontrivial signed order at every rank
is r plus the least prime strictly greater than r+1. -/
theorem first_signed_order (r : ℕ) :
    IsLeast {n : ℕ | r+1<n ∧ ∃ w, Represents (univ : Finset (Fin n)) r (r+1) (fun _ => 1) w}
      (r+nextPrime r) := by
  obtain ⟨high,prime⟩ := next_prime_spec r
  constructor
  · refine ⟨by omega,(signed_iff (by omega)).mpr ?_⟩
    simpa only [Nat.add_sub_cancel_left] using prime.coprime_factorial_of_lt high
  · rintro n ⟨hn,h⟩
    exact rough_lower hn ((signed_iff hn.le).mp h)

/-- The same order bounds every nontrivial ordinary design at this rank,
even if its block size is free. -/
theorem rank_floor {r k n : ℕ} (hr : 0<r) (hrk : r<k) (hkn : k<n)
    {H : Finset (Finset (Fin n))} (hH : H.IsBlockDesign r k) : r+nextPrime r≤n := by
  by_cases e : k=r+1
  · subst k
    exact rough_lower hkn ((signed_iff hkn.le).mp ⟨_,design_weights hH⟩)
  · obtain ⟨p,prime,high,le⟩ := Nat.exists_prime_lt_and_le_two_mul (r+1) (by omega)
    have np := next_le high prime
    have h := (Nat.mul_le_mul_left (r+1) (show 3≤k-r+1 by omega)).trans (tits_bound hr hrk.le hkn hH)
    omega

/-- Exactly two nontrivial systems of rank at least four occur by order
twelve, up to parameter triples. The theorem does not count isomorphism types. -/
theorem spectrum_through_twelve {r k n : ℕ} (hr : 4≤r) (hrk : r<k) (hkn : k<n) (hn : n≤12) :
    (∃ H : Finset (Finset (Fin n)), H.IsBlockDesign r k) ↔
      (r=4 ∧ k=5 ∧ n=11) ∨ (r=5 ∧ k=6 ∧ n=12) := by
  constructor
  · rintro ⟨H,hH⟩
    have bound := tits_bound (by omega) hrk.le hkn hH
    have rr := (Nat.mul_le_mul_left (r+1) (show 2≤k-r+1 by omega)).trans bound
    have e : k=r+1 := by
      by_contra ne
      have wrong := (Nat.mul_le_mul (show 5≤r+1 by omega) (show 3≤k-r+1 by omega)).trans bound
      omega
    subst k
    have rough := (signed_iff hkn.le).mp ⟨_,design_weights hH⟩
    have rh : r≤5 := by omega
    interval_cases r <;> interval_cases n <;> first | decide | exact False.elim ((by decide : ¬_) rough)
  · rintro (⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
    · exact ⟨_,SmallWitt.design_eleven⟩
    · exact SmallWitt.design_twelve

/-- Least ordinary orders among all nontrivial block sizes, at ranks four and five. -/
theorem minimum_at_four_five :
    IsLeast {n : ℕ | ∃ k, 4<k ∧ k<n ∧ ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 4 k} 11 ∧
    IsLeast {n : ℕ | ∃ k, 5<k ∧ k<n ∧ ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 5 k} 12 := by
  refine ⟨⟨⟨5,by decide,by decide,_,SmallWitt.design_eleven⟩,?_⟩,
    ⟨⟨6,by decide,by decide,SmallWitt.design_twelve⟩,?_⟩⟩
  all_goals
    rintro n ⟨k,hrk,hkn,h⟩
    by_contra! hn
    obtain h|h := (spectrum_through_twelve (by decide) hrk hkn (by omega)).mp h <;> omega

#print axioms nextPrime
#print axioms next_prime_spec
#print axioms next_le
#print axioms first_signed_order
#print axioms rank_floor
#print axioms spectrum_through_twelve
#print axioms minimum_at_four_five
end Erdos722.UnitExcess
