import CunninghamPrimeAffineRealization

/-! The terminal affine forms of opposite Cunningham chains have separate
roots modulo suitable primes for every even gap. -/

namespace CunninghamChain.PairedRough
open Finset BrunBlocks

/-- A root of the terminal form avoids all the listed forms at some prime
above any specified bound, provided their rational roots are distinct. -/
theorem separate_terminal {k : ℕ} (a c : Fin k → ℕ) (A C L : ℕ) (hA : 0 < A)
    (sep : ∀ i, a i*C ≠ A*c i) :
    ∃ q>L, q.Prime ∧ ∃ x : ZMod q, residue q A C x=0 ∧ ∀ i, residue q (a i) (c i) x≠0 := by
  classical
  let S := ∑ i, (a i*C+A*c i)
  obtain ⟨q,hq,hp⟩ := Nat.exists_infinite_primes (L+A+S+1)
  let : Fact q.Prime := ⟨hp⟩
  have unit : (A:ZMod q)≠0 := fun e => (Nat.not_dvd_of_pos_of_lt hA (by omega))
    ((ZMod.natCast_eq_zero_iff ..).mp e)
  let x : ZMod q := 2-(C:ZMod q)/(A:ZMod q)
  have hit : residue q A C x=0 := by dsimp [residue,x]; field_simp; ring
  refine ⟨q,by omega,hp,x,hit,?_⟩
  intro i bad
  have eq : ((a i*C:ℕ):ZMod q)=((A*c i:ℕ):ZMod q) := by
    push_cast
    unfold residue at hit bad
    linear_combination (a i:ZMod q)*hit-(A:ZMod q)*bad
  have le : a i*C+A*c i ≤ S := single_le_sum (fun j _ => Nat.zero_le (a j*C+A*c j)) (mem_univ i)
  have eqmod : (a i*C)%q=(A*c i)%q := (ZMod.natCast_eq_natCast_iff ..).mp eq
  exact sep i ((Nat.mod_eq_of_lt (show a i*C < q by omega)).symm.trans
    (eqmod.trans
      (show A*c i%q = A*c i from Nat.mod_eq_of_lt (by omega))))

#print axioms separate_terminal

/-- Value at seed two of the plus chain from n or the minus chain from n+h. -/
def base (h : ℕ) (b : Bool) (i : ℕ) := if b then firstKindTerm 2 i else secondKindTerm (2+h) i

private lemma base_plus (h i : ℕ) : base h true i+1=3*2^i := by
  induction i with
  | zero => simp [base,firstKindTerm]
  | succ i ih =>
    simp only [base, ↓reduceIte,firstKindTerm,pow_succ] at ih ⊢
    omega

private lemma base_minus (h i : ℕ) : base h false i=(h+1)*2^i+1 := by
  induction i with
  | zero => simp [base,secondKindTerm]; omega
  | succ i ih =>
    change 2*secondKindTerm (2+h) i-1=_
    change secondKindTerm (2+h) i=_ at ih
    rw [ih,pow_succ]
    have eq : (h+1)*(2^i*2)=2*((h+1)*2^i) := by ring
    omega

theorem base_pos (h : ℕ) (b : Bool) (i : ℕ) : 0 < base h b i := by
  cases b
  · rw [base_minus]; omega
  · have := base_plus h i
    have : 0 < 2^i := by positivity
    omega

lemma residue_site (q h : ℕ) (b : Bool) (i : ℕ) (x : ZMod q) :
    residue q (2^i) (base h b i) x =
      if b then (2:ZMod q)^i*(x+1)-1 else (2:ZMod q)^i*(x+h-1)+1 := by
  cases b
  · simp only [residue,base_minus,Bool.false_eq_true,if_false,Nat.cast_pow,Nat.cast_ofNat,
      Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    ring
  · have plus := congrArg (fun n : ℕ => (n:ZMod q)) (base_plus h i)
    push_cast at plus
    simp only [residue,if_true,Nat.cast_pow,Nat.cast_ofNat]
    linear_combination plus

/-- At a positive seed both signed orbit values are the prescribed affine
forms. Seed two serves as the reference for the natural subtractions. -/
theorem term_chain {n : ℕ} (hn : 2≤n) (h : ℕ) (b : Bool) (i : ℕ) :
    term (2^i) (base h b i) n = if b then firstKindTerm n i else secondKindTerm (n+h) i := by
  cases b
  · have eq := chain_shift false (n-2) (2+h) (by omega) i
    have id : n-2+(2+h)=n+h := by omega
    simpa [id,base,term,chain] using eq.symm
  · have eq := chain_shift true (n-2) 2 (by decide) i
    simpa [Nat.sub_add_cancel hn,base,term,chain] using eq.symm

#print axioms term_chain

private lemma cross_distinct {h i j : ℕ} (gap : h≠1) (positive : 0 < i ∨ 0 < j) :
    2^i * base h false j ≠ 2^j * base h true i := by
  let A := 2^i
  let D := 2^j
  have ha : 0 < A := pow_pos (by decide) _
  have hd : 0 < D := pow_pos (by decide) _
  have large : 1 < A ∨ 1 < D := positive.imp (fun z => Nat.one_lt_pow z.ne' (by decide)) (fun z => Nat.one_lt_pow z.ne' (by decide))
  intro both
  have plus : base h true i+1=3*A := base_plus h i
  have hp := congrArg (D*·) plus
  rw [base_minus] at both
  change A*((h+1)*D+1)=D*base h true i at both
  have key : h*(A*D)+A+D=2*(A*D) := by nlinarith only [hp,both]
  by_cases hz : h=0
  · simp only [hz,zero_mul,zero_add] at key
    have h1 := Nat.le_mul_of_pos_right A hd
    have h2 := Nat.le_mul_of_pos_left D ha
    rcases large with hh|hh
    · have := Nat.mul_lt_mul_of_pos_right hh hd
      omega
    · have := Nat.mul_lt_mul_of_pos_left hh ha
      omega
  · have hh : 2≤h := by omega
    have := Nat.mul_le_mul_right (A*D) hh
    omega

/-- No prescribed positive terminal position shares its rational root with
an earlier position on its side or any prefix position on the other side,
provided the seed gap is different from one. -/
theorem terminal_distinct {h i j : ℕ} (gap : h≠1) (b e : Bool) (hi : 0 < i)
    (before : b=e → j < i) : 2^j * base h b i ≠ 2^i * base h e j := by
  cases b <;> cases e
  · rw [base_minus,base_minus]
    intro eq
    have ne := Nat.pow_lt_pow_right (by decide : 1 < 2) (before rfl)
    nlinarith only [eq,ne]
  · exact (cross_distinct (i:=j) (j:=i) gap (Or.inr hi))
  · exact Ne.symm (cross_distinct (i:=i) (j:=j) gap (Or.inl hi))
  · intro eq
    have h₁ := congrArg (2^j*·) (base_plus h i)
    have h₂ := congrArg (2^i*·) (base_plus h j)
    have ne := Nat.pow_lt_pow_right (by decide : 1 < 2) (before rfl)
    nlinarith only [eq,h₁,h₂,ne]

#print axioms terminal_distinct

#print axioms base_pos
#print axioms residue_site

end CunninghamChain.PairedRough
