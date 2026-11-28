import CunninghamJonesSplitCriterion

/-! Congruence conditions on a list of prime divisors guaranteeing irreducibility
in every degree. -/

namespace CunninghamChain.JonesSplitParity
open Finset Polynomial

/-- The indices are 0 through n. Every prime after the immediate successor of
q(i) is one modulo q(i), while the immediate successor squares to minus one. -/
structure PrimePattern (q : ℕ → ℕ) (n k : ℕ) : Prop where
  prime : ∀ i ≤ n, (q i).Prime
  large : ∀ i ≤ n, 2 < q i
  size : 5^n < 2^(k+1)
  firstResidues : ∀ i < n, (q i : ZMod (2^(k+1)))=5
  productResidue : ((∏ i ∈ range (n+1), q i : ℕ) : ZMod (2^(k+1)))=1
  nextSquare : ∀ i < n, (q (i+1) : ZMod (q i))^2 = -1
  laterResidues : ∀ i j, i+1 < j → j ≤ n → (q j : ZMod (q i))=1

private theorem split_prime_product (q : ℕ → ℕ) (R : Finset ℕ)
    (pr : ∀ i ∈ R, (q i).Prime) (u v : ℕ) (he : u*v=∏ i ∈ R, q i) :
    ∃ A B : Finset ℕ, A ∪ B = R ∧ Disjoint A B ∧
      (∏ i ∈ A, q i)=u ∧ (∏ i ∈ B, q i)=v := by
  classical
  induction R using Finset.induction_on generalizing u v with
  | empty =>
    simp at he
    obtain ⟨rfl,rfl⟩ := he
    exact ⟨∅,∅,by simp⟩
  | insert i R hi ih =>
    rw [prod_insert hi] at he
    have hq := pr i (mem_insert_self ..)
    have hdiv : q i ∣ u*v := he ▸ dvd_mul_right ..
    have pr' : ∀ j ∈ R, (q j).Prime := fun j hj => pr j (mem_insert_of_mem hj)
    rcases hq.dvd_mul.mp hdiv with ⟨a,ha⟩|⟨b,hb⟩
    · subst u
      have h := Nat.eq_of_mul_eq_mul_left hq.pos (by simpa [Nat.mul_assoc] using he)
      obtain ⟨A,B,hR,hd,hA,hB⟩ := ih pr' a v h
      have hn : i ∉ A ∧ i ∉ B := by simpa [←hR] using hi
      exact ⟨insert i A,B,by simp [hR],by simpa [hn.2] using hd,by rw [prod_insert hn.1,hA],hB⟩
    · subst v
      have h : u*b=∏ j ∈ R,q j := Nat.eq_of_mul_eq_mul_left hq.pos (by simpa only [Nat.mul_left_comm u (q i) b] using he)
      obtain ⟨A,B,hR,hd,hA,hB⟩ := ih pr' u b h
      have hn : i ∉ A ∧ i ∉ B := by simpa [←hR] using hi
      exact ⟨A,insert i B,by simp [hR],by simpa [hn.1] using hd,hA,by rw [prod_insert hn.2,hB]⟩

private theorem proper_residue {q : ℕ → ℕ} {n k : ℕ} (h : PrimePattern q n k)
    {A : Finset ℕ} (ha : A.Nonempty) (hsub : A ⊆ range n) :
    ((∏ i ∈ A, q i : ℕ) : ZMod (2^(k+1))) ≠ 1 := by
  have eq : ((∏ i ∈ A, q i : ℕ) : ZMod (2^(k+1)))=(5:ZMod (2^(k+1)))^A.card := by
    push_cast
    have hh := prod_congr (s₁ := A) (s₂ := A) rfl (fun i hi => h.firstResidues i (mem_range.mp (hsub hi)))
    simpa using hh
  rw [eq]
  intro he
  have hl : 5^A.card < 2^(k+1) := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by simpa using card_le_card hsub)) h.size
  have hb : 1 < 5^A.card := Nat.one_lt_pow (card_pos.mpr ha).ne' (by decide)
  have hm : 5^A.card ≡ 1 [MOD 2^(k+1)] := (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using he)
  change 5^A.card % _ = 1 % _ at hm
  rw [Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt (lt_trans hb hl)] at hm
  omega

private theorem pattern_split {q : ℕ → ℕ} {n k : ℕ} (h : PrimePattern q n k)
    {A B : Finset ℕ} (hR : A ∪ B=range (n+1)) (hd : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) (hz : 0 ∉ A) :
    SplitObstruction (∏ i ∈ range (n+1),q i) (∏ i ∈ A,q i) (∏ i ∈ B,q i) := by
  classical
  let m := ∏ i ∈ range (n+1),q i
  let M := 2^(k+1)
  have allA (i) (hi : i ∈ A) : i ≤ n := by have := hR ▸ mem_union_left B hi; exact Nat.lt_succ_iff.mp (mem_range.mp this)
  have allB (i) (hi : i ∈ B) : i ≤ n := by have := hR ▸ mem_union_right A hi; exact Nat.lt_succ_iff.mp (mem_range.mp this)
  have hmul : (∏ i ∈ A,q i)*(∏ i ∈ B,q i)=m := (prod_union hd).symm.trans (hR ▸ rfl)
  have hmt := h.productResidue
  have hneq : ((∏ i ∈ A,q i : ℕ):ZMod M) ≠ 1 := by
    by_cases hn : n ∈ A
    · have nb : n ∉ B := fun z => disjoint_left.mp hd hn z
      have hb := proper_residue h hB (show B ⊆ range n by
        intro i hi
        have hi' := allB i hi
        apply mem_range.mpr
        by_contra! hh
        exact nb ((show i=n by omega) ▸ hi))
      intro eq
      change (m:ZMod M)=1 at hmt
      rw [←hmul,Nat.cast_mul,eq,one_mul] at hmt
      exact hb hmt
    · apply proper_residue h hA
      intro i hi
      have := allA i hi
      apply mem_range.mpr
      by_contra! hh
      exact hn ((show i=n by omega) ▸ hi)
  let t := A.min' hA
  have ht : t ∈ A := A.min'_mem _
  have htpos : 0 < t := Nat.pos_of_ne_zero (fun e => hz (e ▸ ht))
  let i := t-1
  have hi : i+1=t := by dsimp [i]; omega
  have hil : i<n := by have := allA t ht; omega
  have hnot : i ∉ A := by intro z; have := A.min'_le i z; change t ≤ i at this; omega
  have hib : i ∈ B := by
    have hz' : i ∈ A ∪ B := hR ▸ mem_range.mpr (by omega)
    exact (mem_union.mp hz').resolve_left hnot
  have hval : ((∏ j ∈ A,q j : ℕ) : ZMod (q i)) = q t := by
    push_cast
    apply prod_eq_single_of_mem t ht
    intro j hj hne
    have hh := A.min'_le j hj
    change t≤j at hh
    exact h.laterResidues i j (by omega) (allA j hj)
  have hmod : 1 ≡ m [MOD M] := (ZMod.natCast_eq_natCast_iff ..).mp (by simpa [m,M] using hmt.symm)
  have hodd : Odd (∏ i ∈ A,q i) := by
    rw [←Nat.coprime_two_right]
    apply Nat.Coprime.prod_left
    intro i he
    exact Nat.coprime_two_right.mpr ((h.prime i (allA i he)).odd_of_ne_two (by have := h.large i (allA i he); omega))
  exact ⟨k,q i,hmod.dvd' ,h.large i hil.le,dvd_prod_of_mem _ hib,hodd,hneq,by rw [hval,←hi]; exact h.nextSquare i hil⟩

theorem irreducible_of_prime_pattern {q : ℕ → ℕ} {n k : ℕ} (h : PrimePattern q n k) {j : ℕ}
    (hj : 0<j) : Irreducible ((jonesSumPolynomial (∏ i ∈ range (n+1),q i) j).map (Int.castRingHom ℚ)) := by
  have pr (i) (hi : i ∈ range (n+1)) := h.prime i (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hm := Nat.le_of_dvd (prod_pos fun i hi => (pr i hi).pos)
    (dvd_prod_of_mem q (mem_range.mpr (show 0<n+1 by omega)))
  apply irreducible_all_degrees_of_splits (by have := h.large 0 (Nat.zero_le n); omega) _ hj
  intro u v hu hv he
  obtain ⟨A,B,hR,hd,ha,hb⟩ := split_prime_product q _ pr u v he
  subst u; subst v
  have na : A.Nonempty := nonempty_iff_ne_empty.mpr (fun e => by simp [e] at hu)
  have nb : B.Nonempty := nonempty_iff_ne_empty.mpr (fun e => by simp [e] at hv)
  by_cases h0 : 0 ∈ A
  · right
    exact pattern_split h (union_comm A B ▸ hR) hd.symm nb na (fun z => disjoint_left.mp hd h0 z)
  · exact Or.inl (pattern_split h hR hd na nb h0)

#print axioms irreducible_of_prime_pattern

end CunninghamChain.JonesSplitParity
