import Erdos722AdjacentPrimePowers
import Erdos722MinimumTripleOrder
import Erdos722DerivedAffine

/-!
# The second ordinary order and the first order at rank four

Witt's projective sublines bound the second ordinary rank-three order from above.
At rank four, the divisibility restriction in Penttila's one-point extension
lemma excludes the square order for q>58, so the same lower bound applies
to every nontrivial design.
-/

namespace Erdos722.SecondOrder
open Finset IntegralDesign MinimumOrder

/-- Nontrivial rank-three orders strictly beyond the inversive plane. -/
def aboveSquare (q : ℕ) : Set ℕ :=
  {v | q^2+1<v ∧ ∃ H : Finset (Finset (Fin v)), H.IsBlockDesign 3 (q+1)}

private theorem tests_of_design {q v : ℕ} (hq : 2≤q) (hv : q+1≤v)
    {H : Finset (Finset (Fin v))} (hH : H.IsBlockDesign 3 (q+1)) : Tests q v :=
  (signed_steiner_iff v 3 (q+1) (by omega) hv).mp ⟨_,design_weights hH⟩

/-- The minimum is q²+1. The next ordinary order exists and lies in the
given closed interval. The lower endpoint is the exact signed minimum. -/
theorem second_ordinary_bounds {q : ℕ} (hp : IsPrimePow q) (hq : 11<q) :
    IsLeast (orders 3 (q+1)) (q^2+1) ∧
    ∃ v, IsLeast (aboveSquare q) v ∧ nextAdmissible q≤v ∧ v≤q^3+1 := by
  classical
  refine ⟨prime_power_minimum hp (by omega) (by omega) (by omega),?_⟩
  have large : q^2+1<q^3+1 := Nat.add_lt_add_right (Nat.pow_lt_pow_right (by omega) (by decide : 2<3)) _
  have wit : q^3+1∈aboveSquare q := by
    refine ⟨large,?_⟩
    obtain ⟨p,a,pp,ha,rfl⟩ := (isPrimePow_nat_iff _).mp hp
    let : Fact p.Prime := ⟨pp⟩
    exact Sublines.exists_prime_power_subline_design p a 3 ha (by decide)
  have ex : ∃ v, v∈aboveSquare q := ⟨_,wit⟩
  let v := Nat.find ex
  have first : IsLeast (aboveSquare q) v := ⟨Nat.find_spec ex,fun _ h => Nat.find_min' ex h⟩
  obtain ⟨hv,H,hH⟩ := first.1
  have hv' : q+1≤v := by nlinarith [Nat.mul_le_mul_left q (show 1≤q by omega)]
  exact ⟨v,first,(least_admissible hp (by omega)).2 ⟨hv,tests_of_design (by omega) hv' hH⟩,first.2 wit⟩

/-- Penttila's arithmetic restriction at the order of a one-point extension
of an inversive plane. It uses only the fourth replication test. -/
theorem fourth_square_divides_sixty {q : ℕ} (hq : 2≤q)
    (h : (q+2).choose 4 ∣ (q^2+2).choose 4) : q+2∣60 := by
  have hd := Nat.mul_dvd_mul_left (Nat.factorial 4) h
  simp only [← Nat.descFactorial_eq_factorial_mul_choose] at hd
  have hq' : q-1+1=q := Nat.sub_add_cancel (by omega)
  have h₁ : q^2+2-3=(q-1)*(q+1) := by
    have eq : (q-1)*(q+1)+3=q^2+2 := by nlinarith only [hq',congrArg (q*·) hq']
    omega
  simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero,mul_one,
    h₁,show q+2-3=q-1 by omega,show q+2-1=q+1 by omega,show q^2+2-1=q^2+1 by omega,
    Nat.add_sub_cancel] at hd
  let c := (q-1)*q*(q+1)
  have d : c*(q+2)∣c*(q*(q^2+1)*(q^2+2)) := by convert hd using 1 <;> dsimp [c] <;> ring
  have hc : 0<c := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have dz := (ZMod.natCast_eq_zero_iff _ _).mpr ((Nat.mul_dvd_mul_iff_left hc).mp d)
  have eq : (q : ZMod (q+2))= -2 := by
    have hh := ZMod.natCast_self (q+2)
    push_cast at hh
    linear_combination hh
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast at dz ⊢
  rw [eq] at dz
  linear_combination -dz

private theorem rank_four_above {q v : ℕ} (hp : IsPrimePow q) (hq : 58<q) (hv : q+2<v+1)
    {H : Finset (Finset (Fin (v+1)))} (hH : H.IsBlockDesign 4 (q+2)) : v∈aboveSquare q := by
  obtain ⟨G,hG⟩ := Cyclotomy.derive_design hH
  refine ⟨?_,G,hG⟩
  have hl := (prime_power_minimum hp (by omega) (by omega) (by omega)).2 (show v∈orders 3 (q+1) from
    ⟨by omega,G,hG⟩)
  apply lt_of_le_of_ne hl
  rintro rfl
  have hf := (signed_steiner_iff _ 4 (q+2) (by omega) hv.le).mp ⟨_,design_weights hH⟩ 0 (by decide)
  have d := fourth_square_divides_sixty (by omega : 2≤q) (by simpa using hf)
  have := Nat.le_of_dvd (by decide : 0<60) d
  omega

/-- For prime-power q>58 every nontrivial S(4,q+2,v+1) already lies
above the signed second-order threshold of its rank-three link. -/
theorem rank_four_separation {q v : ℕ} (hp : IsPrimePow q) (hq : 58<q) (hv : q+2<v+1)
    {H : Finset (Finset (Fin (v+1)))} (hH : H.IsBlockDesign 4 (q+2)) :
    nextAdmissible q≤v ∧ (q*(q-1))^3*(q+1)≤12*(v-2)^3 := by
  obtain ⟨hl,G,hG⟩ := rank_four_above hp hq hv hH
  have ht := tests_of_design (by omega : 2≤q) (by omega) hG
  exact ⟨(least_admissible hp (by omega)).2 ⟨hl,ht⟩,cubic_separation hp (by omega) hl ht⟩

/-- Deriving s times extends the rank-four obstruction to every higher rank. -/
theorem higher_rank_separation (s : ℕ) {q v : ℕ} (hp : IsPrimePow q) (hq : 58<q)
    (hv : q+2<v+1) {H : Finset (Finset (Fin (v+1+s)))} (hH : H.IsBlockDesign (4+s) (q+2+s)) :
    nextAdmissible q≤v ∧ (q*(q-1))^3*(q+1)≤12*(v-2)^3 := by
  induction s with
  | zero => exact rank_four_separation hp hq hv hH
  | succ s ih =>
    obtain ⟨G,hG⟩ := Cyclotomy.derive_design hH
    exact ih hG

/-- At block size 258, the rank-four lower bound exceeds eight million points. -/
theorem rank_four_258 {n : ℕ} (hn : 258<n) {H : Finset (Finset (Fin n))}
    (hH : H.IsBlockDesign 4 258) : 8355843≤n := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  have hp : IsPrimePow 256 := (isPrimePow_nat_iff _).mpr ⟨2,8,Nat.prime_two,by decide,rfl⟩
  have hs : IsPrimePow (256+1) := (isPrimePow_nat_iff _).mpr ⟨257,1,by norm_num,by decide,by decide⟩
  have h := (rank_four_separation hp (by decide) hn hH).1
  rw [nextAdmissible,firstIndex_eq_half (by decide : 4≤256) hs] at h
  norm_num at h
  omega

#print axioms rank_four_258

#print axioms second_ordinary_bounds
#print axioms fourth_square_divides_sixty
#print axioms rank_four_separation
#print axioms higher_rank_separation
end Erdos722.SecondOrder
