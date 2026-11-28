import CunninghamJonesPrimePatterns
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Choosing prime divisors with prescribed residues to obtain squarefree
coefficients of arbitrary prescribed prime-factor count. -/

namespace CunninghamChain.JonesSplitParity
open Finset Polynomial

private theorem prime_in_joint_classes (S : Finset ℕ) (r a : ℕ → ℕ) (D b B : ℕ)
    (hD : 0 < D) (hb : b.Coprime D) (hr : ∀ i ∈ S, 0 < r i)
    (hpair : Set.Pairwise S (fun i j => (r i).Coprime (r j)))
    (ha : ∀ i ∈ S, (a i).Coprime (r i)) (hsep : ∀ i ∈ S, D.Coprime (r i)) :
    ∃ p > B, p.Prime ∧ p ≡ b [MOD D] ∧ ∀ i ∈ S, p ≡ a i [MOD r i] := by
  classical
  let R := ∏ i ∈ S,r i
  have hR : 0 < R := prod_pos hr
  obtain ⟨c,hc⟩ := Nat.chineseRemainderOfFinset a r S (fun i hi => (hr i hi).ne') hpair
  obtain ⟨d,hd,hc'⟩ := Nat.chineseRemainder (Nat.Coprime.prod_right hsep) b c
  have hdD : d.Coprime D := hd.gcd_eq.trans hb
  have hdR : d.Coprime R := by
    apply Nat.Coprime.prod_right
    intro i hi
    exact ((hc'.of_dvd (dvd_prod_of_mem r hi)).trans (hc i hi)).gcd_eq.trans (ha i hi)
  obtain ⟨p,hp,hpr,h⟩ := Nat.forall_exists_prime_gt_and_modEq B (Nat.mul_pos hD hR).ne'
    (Nat.Coprime.mul_right hdD hdR)
  refine ⟨p,hp,hpr,(h.of_dvd (dvd_mul_right D R)).trans hd,?_⟩
  intro i hi
  exact (((h.of_dvd (dvd_mul_left R D)).trans hc').of_dvd (dvd_prod_of_mem r hi)).trans (hc i hi)

private structure Prefix (q e : ℕ → ℕ) (s D B : ℕ) : Prop where
  prime : ∀ i < s, (q i).Prime
  large : ∀ i < s, max 2 B < q i
  increasing : StrictMonoOn q (Set.Iio s)
  residues : ∀ i < s, q i ≡ 5^(e i) [MOD D]
  nextSquare : ∀ i, i+1 < s → (q (i+1) : ZMod (q i))^2 = -1
  laterResidues : ∀ i j, i+1 < j → j < s → (q j : ZMod (q i))=1

private theorem exists_prefix (k B : ℕ) (hk : 1 ≤ k) (e : ℕ → ℕ) (s : ℕ) :
    ∃ q : ℕ → ℕ, Prefix q e s (2^(k+1)) B := by
  classical
  let D := 2^(k+1)
  have hfour : 4 ∣ D := pow_dvd_pow 2 (by omega : 2≤k+1)
  induction s with
  | zero => exact ⟨fun _ => 0, by constructor <;> simp; intro i hi; exact False.elim hi⟩
  | succ s ih =>
    obtain ⟨q,h⟩ := ih
    have root (i : ℕ) (hi : i<s) : ∃ c : ℕ, (c:ZMod (q i))^2 = -1 := by
      let : Fact (q i).Prime := ⟨h.prime i hi⟩
      have hr := (h.residues i hi).of_dvd hfour
      have h1 := (show 5 ≡ 1 [MOD 4] by decide).pow (e i)
      have hh : q i ≡ 1 [MOD 4] := hr.trans (by simpa using h1)
      obtain ⟨a,ha⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=q i)).mpr (by change q i%4 = 1%4 at hh; omega)
      exact ⟨a.val,by simpa [pow_two] using ha.symm⟩
    choose c hc using root
    let a (i : ℕ) := if hi : i<s then (if i+1=s then c i hi else 1) else 1
    have hlocal (i : ℕ) (hi : i<s) : (a i).Coprime (q i) := by
      simp only [a,dif_pos hi]
      split_ifs with ht
      · apply Nat.Coprime.symm
        apply (h.prime i hi).coprime_iff_not_dvd.mpr
        intro hd
        have hz := hc i hi
        let : Fact (q i).Prime := ⟨h.prime i hi⟩
        rw [(ZMod.natCast_eq_zero_iff ..).mpr hd,zero_pow (by decide)] at hz
        simp at hz
      · simp
    have hsep (i : ℕ) (hi : i<s) : D.Coprime (q i) := by
      apply Nat.Coprime.pow_left
      exact Nat.coprime_two_left.mpr ((h.prime i hi).odd_of_ne_two (by have := h.large i hi; omega))
    have hpair : Set.Pairwise (range s : Finset ℕ) (fun i j => (q i).Coprime (q j)) := by
      intro i hi j hj hne
      exact (Nat.coprime_primes (h.prime i (mem_range.mp hi)) (h.prime j (mem_range.mp hj))).mpr
        (h.increasing.injOn.ne (mem_range.mp hi) (mem_range.mp hj) hne)
    obtain ⟨p,hp,hpr,hdy,hsmall⟩ := prime_in_joint_classes (range s) q a D (5^(e s))
      (max (max 2 B) ((range s).sup q)) (by dsimp [D]; positivity)
      (((by decide : Nat.Coprime 5 2).pow_right _).pow_left _) (fun i hi => (h.prime i (mem_range.mp hi)).pos)
      hpair (fun i hi => hlocal i (mem_range.mp hi)) (fun i hi => hsep i (mem_range.mp hi))
    let q' (i : ℕ) := if i=s then p else q i
    have old (i : ℕ) (hi : i<s) : q' i=q i := if_neg hi.ne
    have last : q' s=p := if_pos rfl
    have above (i : ℕ) (hi : i<s) : q i<p := lt_of_le_of_lt (le_sup (f:=q) (mem_range.mpr hi)) ((le_max_right ..).trans_lt hp)
    refine ⟨q',⟨?_,?_,?_,?_,?_,?_⟩⟩
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt|rfl
      · rw [old i hlt]; exact h.prime i hlt
      · rwa [last]
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt|rfl
      · rw [old i hlt]; exact h.large i hlt
      · rw [last]; exact (le_max_left ..).trans_lt hp
    · intro i hi j hj hij
      change j<s+1 at hj
      rw [old i (by omega)]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt|rfl
      · rw [old j hlt]; exact h.increasing (by change i<s; omega) hlt hij
      · rw [last]; exact above i hij
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt|rfl
      · rw [old i hlt]; exact h.residues i hlt
      · rwa [last]
    · intro i hi
      have hil : i<s := by omega
      rw [old i hil]
      by_cases hl : i+1=s
      · rw [hl,last,(ZMod.natCast_eq_natCast_iff ..).mpr (hsmall i (mem_range.mpr hil))]
        simpa [a,hil,hl] using hc i hil
      · rw [old (i+1) (by omega)]
        exact h.nextSquare i (by omega)
    · intro i j hij hj
      have hil : i<s := by omega
      rw [old i hil]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt|rfl
      · rw [old j hlt]; exact h.laterResidues i j hij hlt
      · rw [last,(ZMod.natCast_eq_natCast_iff ..).mpr (hsmall i (mem_range.mpr hil))]
        simp [a,hil,show i+1≠j by omega]

/-- Any specified positive number n+1 of distinct prime factors can be
chosen above B, subject to the irreducibility congruences. -/
theorem exists_prime_pattern (n B : ℕ) :
    ∃ (q : ℕ → ℕ) (k : ℕ), PrimePattern q n k ∧
    StrictMonoOn q (Set.Iio (n+1)) ∧ ∀ i ≤ n, B < q i := by
  let k := 3*n+2
  let D := 2^(k+1)
  let e (i : ℕ) := if i=n then 2^k-n else 1
  obtain ⟨q,h⟩ := exists_prefix k B (by dsimp [k]; omega) e (n+1)
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
    hsize,first,?_,fun i hi => h.nextSquare i (by omega),fun i j hij hj => h.laterResidues i j hij (by omega)⟩,
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
