import CunninghamEvenPowerResidues

/-! Which positive leading coefficients can three plus-chain coefficients certify? -/

namespace CunninghamChain
open Polynomial

/-- The coefficients a, −a, 1 alone force a factor with unit constant. -/
def plusTripleForcesUnit (a : ℕ) : Prop :=
  ∀ A B : ℤ[X], (A*B).coeff 0=(a:ℤ) → (A*B).coeff 1= -(a:ℤ) →
    (A*B).coeff 2=1 → IsUnit (A.coeff 0) ∨ IsUnit (B.coeff 0)

private lemma even_triple_iff {p r : ℕ} (hp : p.Prime) (hr : 0<r) :
    plusTripleForcesUnit (p^(2*r)) ↔ ¬(p%4=1 ∨ (p=2 ∧ r=1)) := by
  rw [←neg_one_at_prime_power_iff hp hr,←split_three_coefficients_iff hp hr 1
    (Nat.prime_iff_prime_int.mp hp).not_dvd_one]
  have c : ((p^(2*r):ℕ):ℤ)=((p^r:ℕ):ℤ)^2 := by rw [two_mul,pow_add]; push_cast; ring
  simp only [plusTripleForcesUnit,c]
  constructor
  · rintro h ⟨A,B,z,l,b,ha,hb⟩
    exact (h A B z l b).elim ha hb
  · intro h A B z l b
    by_contra! bad
    exact h ⟨A,B,z,l,b,bad.1,bad.2⟩

theorem prime_power_plus_triple_iff {p e : ℕ} (hp : p.Prime) (size : 28≤p^e) :
    plusTripleForcesUnit (p^e) ↔ Odd e ∨ p=2 ∨ p%4=3 := by
  rcases Nat.even_or_odd e with ⟨r,h⟩|odd
  · have he : e=2*r := by omega
    rw [he] at size ⊢
    have hr : 0<r := by
      by_contra! z
      obtain rfl : r=0 := by omega
      norm_num at size
    rw [even_triple_iff hp hr]
    have even : ¬Odd (2*r) := by rintro ⟨j,hj⟩; omega
    by_cases two : p=2
    · subst p
      have ne : r≠1 := by rintro rfl; norm_num at size
      simp [ne]
    · obtain ⟨j,hj⟩ := hp.odd_of_ne_two two
      simp only [two,even,false_and,or_false,false_or]
      omega
  · refine ⟨fun _ => Or.inl odd,fun _ => ?_⟩
    obtain ⟨r,rfl⟩ := odd
    intro A B z l b
    exact unit_constant_of_odd_power (r:=r) hp A B (by simp [z]) (by simp [z,l])
      (by rw [b]; exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one)

private lemma not_forced_of_coprime {a b : ℕ} (ha : 1<a) (hb : 1<b) (cop : a.Coprime b) :
    ¬plusTripleForcesUnit (a*b) := by
  intro force
  obtain ⟨u,v,bez⟩ := cop.isCoprime
  let A : ℤ[X] := C (a:ℤ)+C (-(a:ℤ))*X+C v*X^2
  let B : ℤ[X] := C (b:ℤ)+C u*X^2
  have data : (A*B).coeff 0=((a*b:ℕ):ℤ) ∧
      (A*B).coeff 1= -((a*b:ℕ):ℤ) ∧ (A*B).coeff 2=1 := by
    simp only [A,B,mul_coeff_zero,mul_coeff_one,coeff_two_product,coeff_add,
      coeff_C_mul,coeff_C,coeff_X,coeff_X_pow]
    norm_num
    linear_combination bez
  have units := force A B data.1 data.2.1 data.2.2
  simp [A,B,Int.isUnit_iff_natAbs_eq] at units
  omega

/-- Exact arithmetic scope of the three-coefficient test at every a ≥ 28.
With two coprime nontrivial coefficient factors a Bézout identity builds a split. -/
theorem plus_triple_forces_unit_iff {a : ℕ} (size : 28≤a) :
    plusTripleForcesUnit a ↔
      ∃ p e : ℕ, p.Prime ∧ a=p^e ∧ (Odd e ∨ p=2 ∨ p%4=3) := by
  constructor
  · intro force
    induction a using Nat.recOnPosPrimePosCoprime with
    | zero => omega
    | one => omega
    | prime_pow p e hp he => exact ⟨p,e,hp,rfl,(prime_power_plus_triple_iff hp size).mp force⟩
    | coprime a b ha hb cop _ _ => exact (not_forced_of_coprime ha hb cop force).elim
  · rintro ⟨p,e,hp,rfl,h⟩
    exact (prime_power_plus_triple_iff hp size).mpr h

#print axioms prime_power_plus_triple_iff
#print axioms plus_triple_forces_unit_iff

end CunninghamChain
