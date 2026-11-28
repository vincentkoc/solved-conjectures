import CunninghamJonesPrimePatterns
import CunninghamJonesPrescribedPrimes

/-! Choosing prime divisors with prescribed residues to obtain squarefree
coefficients of arbitrary prescribed prime-factor count. -/

namespace CunninghamChain.JonesSplitParity
open Finset Polynomial

/-- Any specified positive number n+1 of distinct prime factors can be
chosen above B, subject to the irreducibility congruences. -/
theorem exists_prime_pattern (n B : ℕ) :
    ∃ (q : ℕ → ℕ) (k : ℕ), PrimePattern q n k ∧
    StrictMonoOn q (Set.Iio (n+1)) ∧ ∀ i ≤ n, B < q i := by
  let k := 3*n+2
  let D := 2^(k+1)
  let e (i : ℕ) := if i=n then 2^k-n else 1
  have hfour : 4 ∣ D := pow_dvd_pow 2 (by dsimp [k]; omega : 2≤k+1)
  obtain ⟨q,h⟩ := exists_prescribed_prefix D B (fun i => 5^(e i)) (fun _ => 1)
    (by dsimp [D]; positivity) (fun _ => by decide)
    (fun _ => ((by decide : Nat.Coprime 5 2).pow_right _).pow_left _)
    (fun _ => by simpa using hfour)
    (fun i => by simpa using (show 5 ≡ 1 [MOD 4] by decide).pow (e i)) (n+1)
  have hn : n≤2^k := by have hh : k<2^k := Nat.lt_two_pow_self; dsimp [k] at *; omega
  have hsize : 5^n<D := by
    have h1 : (5:ℕ)^n ≤ 8^n := Nat.pow_le_pow_left (by decide) _
    have h2 : (8:ℕ)^n = 2^(3*n) := by rw [pow_mul]; norm_num
    have h3 : 2^(3*n)<2^(k+1) := Nat.pow_lt_pow_right (by decide) (by dsimp [k]; omega)
    rw [h2] at h1
    exact h1.trans_lt h3
  have first (i : ℕ) (hi : i<n) : (q i : ZMod D)=5 := by
    simpa [e,hi.ne] using (ZMod.natCast_eq_natCast_iff ..).mpr (h.residues i (by omega))
  refine ⟨q,k,⟨fun i hi => h.prime i (by omega),fun i hi => by have := h.large i (by omega); omega,
    hsize,first,?_,fun i hi => by simpa using h.nextSquare i (by omega),fun i j hij hj => h.laterResidues i j hij (by omega)⟩,
    h.increasing,fun i hi => by have := h.large i (by omega); omega⟩
  change ((∏ i ∈ range (n+1),q i : ℕ):ZMod D)=1
  rw [prod_range_succ,Nat.cast_mul]
  push_cast
  have hp := prod_congr (s₁:=range n) (s₂:=range n) rfl (fun i hi => first i (mem_range.mp hi))
  rw [hp]
  simp only [prod_const,card_range]
  have last : (q n:ZMod D)=(5:ZMod D)^(2^k-n) := by
    simpa [e] using (ZMod.natCast_eq_natCast_iff ..).mpr (h.residues n (by omega))
  rw [last,←pow_add, Nat.add_sub_of_le hn]
  have he := Nat.ModEq.pow_totient ((by decide : Nat.Coprime 5 2).pow_right (k+1))
  rw [Nat.totient_prime_pow_succ Nat.prime_two] at he
  simpa [D] using (ZMod.natCast_eq_natCast_iff ..).mpr he

#print axioms exists_prime_pattern

end CunninghamChain.JonesSplitParity
