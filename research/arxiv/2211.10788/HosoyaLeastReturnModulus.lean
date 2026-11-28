import HosoyaEvenFactorialReturns

/-! The smallest Fibonacci self-dividing index divisible by a prescribed integer. -/

namespace Arxiv.«2211.10788».IndexDivisors

private lemma return_multiple_exists {b : ℕ} (hb : 0 < b) :
    ∃ j : ℕ, 0 < j ∧ b*j ∣ (Nat.fastFibAux (b*j)).1 := by
  let A := (2*(b+2)).factorial
  have ba : b ∣ A := Nat.dvd_factorial hb (by omega)
  have eq := Nat.mul_div_cancel' ba
  refine ⟨A/b,?_,?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) ba) hb
  · rw [eq,Nat.fastFibAux_eq]
    exact even_factorial_dvd_fib b

/-- Searching positive multiples of b terminates at its least Fibonacci self-dividing multiple. -/
def firstSelfMultiple (b : ℕ) (hb : 0 < b) : ℕ := b*Nat.find (return_multiple_exists hb)

theorem firstSelfMultiple_spec {b : ℕ} (hb : 0 < b) :
    0 < firstSelfMultiple b hb ∧ b ∣ firstSelfMultiple b hb ∧
      firstSelfMultiple b hb ∣ Nat.fib (firstSelfMultiple b hb) := by
  obtain ⟨pos,ret⟩ := Nat.find_spec (return_multiple_exists hb)
  exact ⟨Nat.mul_pos hb pos,dvd_mul_right ..,by simpa only [firstSelfMultiple,Nat.fastFibAux_eq] using ret⟩

private lemma firstSelfMultiple_le {b E : ℕ} (hb : 0 < b) (he : 0 < E) (dv : b ∣ E)
    (ret : E ∣ Nat.fib E) : firstSelfMultiple b hb ≤ E := by
  obtain ⟨j,rfl⟩ := dv
  unfold firstSelfMultiple
  apply Nat.mul_le_mul_left
  apply Nat.find_min'
  exact ⟨Nat.pos_of_mul_pos_left he,by simpa only [Nat.fastFibAux_eq] using ret⟩

/-- The least return multiple divides every return multiple. The gcd of two return
multiples is another one, by strong divisibility of Fibonacci numbers. -/
theorem firstSelfMultiple_dvd {b E : ℕ} (hb : 0 < b) (dv : b ∣ E) (ret : E ∣ Nat.fib E) :
    firstSelfMultiple b hb ∣ E := by
  let A := firstSelfMultiple b hb
  obtain ⟨pos,bA,self⟩ := firstSelfMultiple_spec hb
  have gA : A.gcd E ∣ A := Nat.gcd_dvd_left ..
  have gE : A.gcd E ∣ E := Nat.gcd_dvd_right ..
  have gF : A.gcd E ∣ Nat.fib (A.gcd E) := by
    rw [Nat.fib_gcd]
    exact Nat.dvd_gcd (gA.trans self) (gE.trans ret)
  have eq : A=A.gcd E := le_antisymm (firstSelfMultiple_le hb (Nat.gcd_pos_of_pos_left _ pos)
    (Nat.dvd_gcd bA dv) gF) (Nat.le_of_dvd pos gA)
  change A ∣ E
  rwa [←eq] at gE

#print axioms firstSelfMultiple_spec
#print axioms firstSelfMultiple_dvd

end Arxiv.«2211.10788».IndexDivisors
