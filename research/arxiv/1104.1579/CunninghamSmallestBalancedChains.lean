import CunninghamBalancedTwoSearchSound
import CunninghamEventualBalancedIrreducibility
import CunninghamPrimePowerRationalRoots

/-! Full irreducibility classification for both Jones chains from 2(X−1). -/

namespace CunninghamChain.BalancedTwo
open Polynomial LinearRoots LargeGap

private lemma oriented (k : Bool) {N : ℕ} (hN : 5≤N) (exc : k=true ∨ N≠5)
    (g : ℤ[X]) (dg : g.natDegree≤N) (unit : (g.coeff 0).natAbs=1)
    (hg : g*reflect N g=sparse k N*reflect N (sparse k N)) :
    ∃ s : ℤ, s^2=1 ∧ g=C s*sparse k N := by
  have ep : g.coeff 0*g.coeff N=leading k := by
    have h := congrArg (fun P : ℤ[X] => P.coeff 0) hg
    simpa [mul_coeff_zero,coeff_reflect,(at_ends k (by omega : 3≤N)).1,
      (at_ends k (by omega : 3≤N)).2] using h
  rcases (show g.coeff 0=1 ∨ g.coeff 0= -1 by omega) with plus|minus
  · rw [plus,one_mul] at ep
    exact ⟨1,by decide,by simpa using normalized_unique k hN exc g dg plus ep hg⟩
  · rw [minus,neg_one_mul] at ep
    have hn : (-g)*reflect N (-g)=sparse k N*reflect N (sparse k N) := by simpa using hg
    have eq := normalized_unique k hN exc (-g) (by simpa using dg) (by simp [minus])
      (by simpa using ep) hn
    exact ⟨-1,by decide,by simpa using congrArg Neg.neg eq⟩

/-- Every integral polynomial with the same reflected product is the
four-term normalized iterate or its reflection up to sign. -/
theorem balanced_two_rigidity (k : Bool) {N : ℕ} (hN : 5≤N) (exc : k=true ∨ N≠5)
    (g : ℤ[X]) (dg : g.natDegree≤N) (hg : g*reflect N g=sparse k N*reflect N (sparse k N)) :
    ∃ s : ℤ, s^2=1 ∧ (g=C s*sparse k N ∨ reflect N g=C s*sparse k N) := by
  have ep : g.coeff 0*g.coeff N=leading k := by
    have h := congrArg (fun P : ℤ[X] => P.coeff 0) hg
    simpa [mul_coeff_zero,coeff_reflect,(at_ends k (by omega : 3≤N)).1,
      (at_ends k (by omega : 3≤N)).2] using h
  have absval : (g.coeff 0).natAbs*(g.coeff N).natAbs=2 := by
    rw [←Int.natAbs_mul,ep]; cases k <;> decide
  have split : (g.coeff 0).natAbs=1 ∨ (g.coeff N).natAbs=1 := by
    have pos := Nat.pos_of_ne_zero (by omega : (g.coeff 0).natAbs*(g.coeff N).natAbs≠0)
    have a := Nat.pos_of_mul_pos_right pos
    have b := Nat.pos_of_mul_pos_left pos
    by_contra! h
    have := Nat.mul_le_mul (by omega : 2≤(g.coeff 0).natAbs) (by omega : 2≤(g.coeff N).natAbs)
    omega
  rcases split with u|u
  · obtain ⟨s,hs,eq⟩ := oriented k hN exc g dg u hg
    exact ⟨s,hs,Or.inl eq⟩
  · obtain ⟨s,hs,eq⟩ := oriented k hN exc (reflect N g)
      (natDegree_reflect_le.trans (max_le le_rfl dg)) (by simpa using u)
      (by simpa [mul_comm (reflect N g) g] using hg)
    exact ⟨s,hs,Or.inr eq⟩

/-- Starting from the smallest admissible positive balanced coefficient,
all plus iterates are irreducible and the sole reducible minus iterate has index three. -/
theorem irreducible_balanced_two_iff (k : Bool) (n : ℕ) :
    Irreducible (term k 2 (-2) n) ↔ k=true ∨ n≠3 := by
  constructor
  · intro h
    cases k
    · exact Or.inr (fun e => reducible_second_at_two_three (e ▸ h))
    · exact Or.inl rfl
  intro good
  by_cases big : 3≤n
  · exact balanced_iterate_of_rigidity (a:=2) (by decide) k (by omega)
      (balanced_two_rigidity k (by omega) (good.imp_right (by omega)))
  have deg : (term k 2 (-2) n).natDegree=1+n := by
    have d : (C (2:ℤ)*X+C (-2)).natDegree=1 := natDegree_linear (by decide)
    rw [term,natDegree_map_eq_of_injective Int.cast_injective,
      (polynomialTerm_shape k _ (by omega) n).1,d]
  by_cases hn : n=0
  · apply irreducible_of_degree_eq_one
    rw [← Nat.cast_one, degree_eq_iff_natDegree_eq_of_pos (by decide : 0<1),deg,hn]
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, deg]; constructor <;> omega
  intro x root
  have impossible := ((prime_power_rational_roots (p:=2) (e:=1) (by decide) (by omega : 0<n) k x).mp
    (by simpa using root)).1
  omega

/-- The minus chain has exact stopping length three in Jones's polynomial convention. -/
theorem minus_two_exact_three :
    IsPolynomialChainOfLength false (C (2:ℤ)*X+C (-2)) 3 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [leadingCoeff_linear (by decide : (2:ℤ) ≠ 0)]
    decide
  · intro i hi
    exact (irreducible_balanced_two_iff false i).2 (Or.inr (by omega))
  · intro h
    simpa using (irreducible_balanced_two_iff false 3).1 h

#print axioms minus_two_exact_three
#print axioms balanced_two_rigidity
#print axioms irreducible_balanced_two_iff

end CunninghamChain.BalancedTwo
