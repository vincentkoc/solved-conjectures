import HosoyaTargetLiftIsometry
import LucasFibonacciProgressionClosure

/-! High powers dividing the companion coordinate create large fibres of the
upper Hosoya value on reduced prime-parameter classes. -/

namespace Arxiv.«2211.10788».LocalPower

open ProgressionClosure

theorem coordinate_pos (n : ℕ) : 0<coordinate n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n a b => rw [coordinate_rec]; omega

private lemma abs_recurrence (n : ℕ) :
    (coordinate (n+2)).natAbs=(coordinate (n+1)).natAbs+(coordinate n).natAbs := by
  have eq : ((coordinate (n+2)).natAbs:ℤ) =
      ((coordinate (n+1)).natAbs:ℤ)+((coordinate n).natAbs:ℤ) := by
    simp only [Int.natCast_natAbs,abs_of_pos (coordinate_pos _)]
    exact coordinate_rec n
  exact_mod_cast eq

private lemma primitive_companion (n : ℕ) : (coordinate n).natAbs.Coprime (coordinate (n+1)).natAbs := by
  induction n with
  | zero => decide
  | succ n ih => rw [show n+1+1=n+2 by omega,abs_recurrence]; simpa using ih.symm

/-- A finite companion root at a sharp even step supplies, at every higher
level, a reduced class on which the value is constant to double precision. -/
theorem flat_value_class {p r d E s a : ℕ} [Fact p.Prime]
    (eEven : Even E) (ep : p∣E) (unit : s.Coprime E) (small : s<2*E)
    (ha : 2≤a) (hf : p^a ∣ Nat.fib (d*E)) (sharp : ¬p^(a+1)∣Nat.fib (d*E))
    (root : p^a ∣ (coordinate (r+d*s)).natAbs) (b : ℕ) :
    ∃ c < 2*E*p^b, c.Coprime (2*E*p^b) ∧ ∀ t : ℕ,
      Hit d r (p^(2*(a+b))) (lucasFibonacciSum (r+d*c)) (c+2*E*p^b*t) := by
  have hp : p.Prime := Fact.out
  let J := d*E
  have pm : p*p ∣ p^a := by simpa [pow_two] using pow_dvd_pow p ha
  have hsharp : ¬p*p^a ∣ Nat.fib J := by simpa [pow_succ'] using sharp
  obtain ⟨z,hz,all⟩ := fibonacci_recurrence_root_progression
    (fun i => (coordinate i).natAbs) abs_recurrence primitive_companion
    (pow_pos hp.pos a) pm root hf hsharp b
  let c := s+E*z
  have co : c.Coprime E := (Nat.coprime_add_mul_left_left ..).mpr unit
  have co2 : c.Coprime 2 := co.of_dvd_right eEven.two_dvd
  have bound : c < 2*E*p^b := calc
    _ < E*(z+1)+E := by dsimp [c]; rw [Nat.mul_succ]; omega
    _ ≤ E*p^b+E*p^b := Nat.add_le_add (Nat.mul_le_mul_left E hz)
      (Nat.le_mul_of_pos_right _ (pow_pos hp.pos _))
    _ = _ := by ring
  refine ⟨c,bound,(co2.mul_right co).mul_right ((co.of_dvd_right ep).pow_right b),?_⟩
  intro t
  let j := J*p^b*t
  let n := r+d*c
  have eq : n+j=(r+d*s)+J*(z+p^b*t) := by dsimp [n,c,j,J]; ring
  have comp : p^(a+b) ∣ (coordinate (n+j)).natAbs := by
    rw [eq,pow_add,mul_comm]; exact all t
  let : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : NeZero (p^b*p^a) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero)⟩
  have rank := sharp_step_rank (p:=p) (m:=p^a) (j:=J) pm hf hsharp b
  have dv : p^b*p^a∣Nat.fib (J*(p^b*t)) := (fibonacciStepRank_dvd_iff ..).mp
    (by rw [rank]; exact dvd_mul_right _ _)
  have fib : p^(a+b)∣Nat.fib j := by simpa only [j,mul_assoc,←pow_add,Nat.add_comm b a] using dv
  have even : Even j := (((eEven.mul_left d).mul_right (p^b)).mul_right t)
  have delta := midpoint_difference n j
  rw [even.neg_one_pow,one_mul] at delta
  have div : p^(2*(a+b)) ∣ (Nat.fib j * coordinate (n+j):ℤ).natAbs := by
    rw [two_mul,pow_add,Int.natAbs_mul,Int.natAbs_natCast]
    exact Nat.mul_dvd_mul fib comp
  have shift : r+d*(c+2*E*p^b*t)=n+2*j := by dsimp [n,j,J]; ring
  unfold Hit
  rw [shift]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd,delta,← Int.natAbs_dvd_natAbs,Int.natAbs_natCast]
  exact div

/-- A Fibonacci return preserves every divisor shared by its step and a companion value. -/
theorem companion_return_dvd {m j : ℕ} (h : m ∣ Nat.fib j) (s : ℕ) :
    m ∣ (coordinate (s+j)).natAbs ↔ m ∣ (coordinate s).natAbs := by
  let X := fun n => (coordinate n).natAbs
  have transform (k : ℕ) : X (s+(k+1)) = Nat.fib k*X s + Nat.fib (k+1)*X (s+1) := by
    induction k using Nat.twoStepInduction with
    | zero => simp
    | one => simpa [X,Nat.fib,add_comm] using abs_recurrence s
    | more k h₀ h₁ =>
      rw [show s+(k+2+1)=(s+(k+1))+2 by omega,show ∀ n, X (n+2)=X (n+1)+X n from abs_recurrence]
      rw [show s+(k+1)+1=s+(k+1+1) by omega,h₁,h₀,Nat.fib_add_two (n:=k+1),Nat.fib_add_two (n:=k)]
      ring
  cases j with
  | zero => simp
  | succ k =>
    change m∣X (s+(k+1)) ↔ _
    rw [transform, Nat.dvd_add_left (dvd_mul_of_dvd_left h (X (s+1)))]
    exact (((Nat.fib_coprime_fib_succ k).symm).of_dvd_left h).dvd_mul_left

/-- Below the first critical depth, the companion valuation is constant
throughout the return progression. -/
theorem regular_companion_order {p s j a : ℕ} (hp : p.Prime) (hf : p^a ∣ Nat.fib j)
    (regular : ¬ p^a ∣ (coordinate s).natAbs) (u : ℕ) :
    (coordinate (s+j*u)).natAbs ≠ 0 ∧
      (coordinate (s+j*u)).natAbs.factorization p = (coordinate s).natAbs.factorization p := by
  have nz (n) : (coordinate n).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (coordinate_pos n).ne'
  let v := (coordinate s).natAbs.factorization p
  have small : v < a := lt_of_not_ge fun h => regular ((hp.pow_dvd_iff_le_factorization (nz s)).mpr h)
  have law (b) (hb : b≤a) := companion_return_dvd
    ((pow_dvd_pow p hb).trans (hf.trans (Nat.fib_dvd j (j*u) (dvd_mul_right ..)))) s
  have lo := (hp.pow_dvd_iff_le_factorization (nz _)).mp ((law v small.le).mpr (Nat.ordProj_dvd ..))
  have hi : ¬v+1≤(coordinate (s+j*u)).natAbs.factorization p := fun h =>
    Nat.pow_succ_factorization_not_dvd (nz s) hp ((law (v+1) small).mp
      ((hp.pow_dvd_iff_le_factorization (nz _)).mpr h))
  exact ⟨nz _,le_antisymm (by change _ ≤ v; omega) lo⟩

#print axioms companion_return_dvd
#print axioms regular_companion_order

#print axioms coordinate_pos
#print axioms flat_value_class

end Arxiv.«2211.10788».LocalPower
