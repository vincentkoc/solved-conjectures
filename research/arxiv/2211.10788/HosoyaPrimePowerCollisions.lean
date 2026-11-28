import LucasFibonacciPrimePowerLifts
import HosoyaEvenDiagonalSeparation
import HosoyaLocalSquareRoots

/-! Recovery of an index residue from the value and its Pell coordinate at one prime power. -/

namespace Arxiv.«2211.10788».LocalPower

private abbrev U (n : ℕ) : ℤ := lucasFibonacciSum n

def coordinate (n : ℕ) : ℤ := 2*U (n+1)-U n

private lemma upper_rec (n : ℕ) : U (n+2)=U (n+1)+U n := by
  unfold U
  rw [lucas_fibonacci_sum_recurrence,Nat.cast_add]

theorem coordinate_rec (n : ℕ) : coordinate (n+2)=coordinate (n+1)+coordinate n := by
  unfold coordinate
  rw [show n+2+1=(n+1)+2 by omega,upper_rec (n+1)]
  have := upper_rec n
  linarith

theorem cross_coordinate (n j : ℕ) :
    U n * coordinate (n+j) - coordinate n * U (n+j) = -22*(-1:ℤ)^n * Nat.fib j := by
  induction j using Nat.twoStepInduction with
  | zero => simp; ring
  | one =>
    simp only [Nat.fib_one,Nat.cast_one,mul_one]
    unfold coordinate
    rw [show n+1+1=n+2 by omega,upper_rec]
    nlinarith only [PrimeObstruction.upper_signed_pell n]
  | more j h₀ h₁ =>
    rw [←Nat.add_assoc,coordinate_rec,upper_rec,Nat.fib_add_two,Nat.cast_add]
    simp only [Nat.add_assoc] at h₁ ⊢
    linear_combination h₀+h₁

/-- The base valuation absorbs exceptional Fibonacci ranks, including at 2 and 5. -/
theorem rank_offset {p d : ℕ} (hp : p.Prime) (hd : 0<d) :
    ∃ a : ℕ, ∀ b t : ℕ, p^(a+b)∣Nat.fib (d*t) → p^b∣t := by
  let : Fact p.Prime := ⟨hp⟩
  let e := fibonacciStepRank (p^2) d
  let j := d*e
  let a := (Nat.fib j).factorization p
  have base : 0<e ∧ p^2∣Nat.fib j := by
    unfold j e fibonacciStepRank
    exact Nat.find_spec (p := fun t => 0<t ∧ p^2∣Nat.fib (d*t)) _
  have non : Nat.fib j≠0 := (Nat.fib_pos.mpr (Nat.mul_pos hd base.1)).ne'
  have hm : 0<p^a := pow_pos hp.pos _
  have hf : p^a∣Nat.fib j := Nat.ordProj_dvd ..
  have hp2 : p*p∣p^a := by
    rw [←pow_two]
    exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization non).mp base.2)
  have sharp : ¬p*p^a∣Nat.fib j := by
    simpa [a,pow_succ'] using Nat.pow_succ_factorization_not_dvd non hp
  refine ⟨a,fun b t hit => ?_⟩
  have div : d*t∣j*t := by exact ⟨e,by dsimp [j]; ring⟩
  have lifted := hit.trans (Nat.fib_dvd _ _ div)
  rw [pow_add,mul_comm (p^a)] at lifted
  have ret := (fibonacciStepRank_dvd_iff (p^b*p^a) j t).mpr lifted
  rwa [sharp_step_rank hp2 hf sharp] at ret

private theorem congruent_gap {p d a b r n t : ℕ} (hp : p.Prime)
    (rank : ∀ b t : ℕ, p^(a+b)∣Nat.fib (d*t) → p^b∣t)
    (hu : U (r+d*n) ≡ U (r+d*(n+t)) [ZMOD (p:ℤ)^(a+b+1)])
    (hx : coordinate (r+d*n) ≡ coordinate (r+d*(n+t)) [ZMOD (p:ℤ)^(a+b+1)]) :
    p^b∣t := by
  let i := r+d*n
  have eq : r+d*(n+t)=i+d*t := by dsimp [i]; ring
  rw [eq] at hu hx
  change U i ≡ _ [ZMOD _] at hu
  change coordinate i ≡ _ [ZMOD _] at hx
  have det : (p:ℤ)^(a+b+1) ∣ U i * coordinate (i+d*t) - coordinate i * U (i+d*t) := by
    rw [show U i * coordinate (i+d*t) - coordinate i * U (i+d*t) =
      U i*(coordinate (i+d*t)-coordinate i)-coordinate i*(U (i+d*t)-U i) by ring]
    exact dvd_sub (dvd_mul_of_dvd_right (Int.modEq_iff_dvd.mp hx) (U i))
      (dvd_mul_of_dvd_right (Int.modEq_iff_dvd.mp hu) (coordinate i))
  rw [cross_coordinate] at det
  have abs := Int.natAbs_dvd_natAbs.mpr det
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,Int.natAbs_neg,
    Int.natAbs_one,one_pow,mul_one] at abs
  exact rank b t (cancel_twenty_two hp abs)

theorem state_recovery {p d a b r n m : ℕ} (hp : p.Prime)
    (rank : ∀ b t : ℕ, p^(a+b)∣Nat.fib (d*t) → p^b∣t)
    (hu : U (r+d*n) ≡ U (r+d*m) [ZMOD (p:ℤ)^(a+b+1)])
    (hx : coordinate (r+d*n) ≡ coordinate (r+d*m) [ZMOD (p:ℤ)^(a+b+1)]) :
    n ≡ m [MOD p^b] := by
  rcases le_total n m with le|le
  · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le le
    exact (Nat.modEq_iff_dvd' (Nat.le_add_right n t)).mpr (by simpa using congruent_gap hp rank hu hx)
  · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le le
    symm
    exact (Nat.modEq_iff_dvd' (Nat.le_add_right m t)).mpr (by simpa using congruent_gap hp rank hu.symm hx.symm)

#print axioms rank_offset
#print axioms state_recovery

end Arxiv.«2211.10788».LocalPower
