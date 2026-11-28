import research.arxiv.«1104.1579».CunninghamSquarefreeAtPrimes
import research.arxiv.«1104.1579».CunninghamReturnProgressions

/-! # Squarefree Cunningham prefixes at prime seeds -/

namespace CunninghamChain.SquarefreeSeeds

open Finset

/-- The canonical Cunningham term for the chosen recurrence. -/
abbrev term (first : Bool) := if first then firstKindTerm else secondKindTerm

/-- The affine fixed point, −1 for the first kind and 1 for the second. -/
def fixed (first : Bool) (A : Type*) [Ring A] : A := if first then -1 else 1

/-- The affine formula for the term at a given site. -/
def value {A : Type*} [Ring A] (first : Bool) (i : ℕ) (x : A) : A :=
  2^i * (x - fixed first A) + fixed first A

/-- Positivity and a uniform linear bound for all canonical terms at a positive seed. -/
theorem term_bounds (first : Bool) {p : ℕ} (hp : 0 < p) (i : ℕ) :
    0 < term first p i ∧ term first p i + 1 ≤ 2^i*(p+1) := by
  induction i with
  | zero => cases first <;> simpa [term, firstKindTerm, secondKindTerm] using hp
  | succ i ih =>
    rw [pow_succ, mul_right_comm _ 2]
    cases first <;>
      simp only [term, Bool.false_eq_true, if_false, if_true, firstKindTerm, secondKindTerm] at ih ⊢ <;>
      omega

/-- For a positive seed, the modular image agrees with the affine formula. -/
theorem cast_term (first : Bool) {p : ℕ} (hp : 0 < p) (i m : ℕ) :
    (term first p i : ZMod m) = value first i (p : ZMod m) := by
  induction i with
  | zero => cases first <;> simp [term, firstKindTerm, secondKindTerm, value]
  | succ i ih =>
    have hpos := (term_bounds first hp i).1
    cases first <;>
      simp only [term, Bool.false_eq_true, if_false, if_true, firstKindTerm, secondKindTerm] at ih hpos ⊢
    · rw [Nat.cast_sub (by omega : 1 ≤ 2*secondKindTerm p i)]
      push_cast
      rw [ih]
      simp [value, fixed, pow_succ]
      ring
    · push_cast
      rw [ih]
      simp [value, fixed, pow_succ]
      ring

/-- The least residue of the candidate root for an odd modulus. -/
def root (first : Bool) (m i : ℕ) : ℕ :=
  (fixed first (ZMod m) - ((2:ZMod m)^i)⁻¹ * fixed first (ZMod m)).val

/-- At odd modulus the candidate residue zeros the affine form. -/
theorem root_spec (first : Bool) {m : ℕ} [NeZero m] (hodd : Nat.Coprime 2 m) (i : ℕ) :
    value first i (root first m i : ZMod m) = 0 := by
  have hu : IsUnit ((2 : ZMod m)^i) := ((ZMod.isUnit_iff_coprime 2 m).mpr hodd).pow i
  simp only [value, root, ZMod.natCast_zmod_val]
  linear_combination -(fixed first (ZMod m)) * (ZMod.mul_inv_of_unit _ hu)

/-- Divisibility of the term is the single root congruence at odd modulus. -/
theorem root_iff (first : Bool) {p m : ℕ} [NeZero m] (hp : 0 < p)
    (hodd : Nat.Coprime 2 m) (i : ℕ) :
    m ∣ term first p i ↔ p ≡ root first m i [MOD m] := by
  rw [← ZMod.natCast_eq_zero_iff, cast_term first hp, ← ZMod.natCast_eq_natCast_iff]
  have hr := root_spec first hodd i
  refine ⟨fun h => ?_,fun h => h ▸ hr⟩
  have hu : IsUnit ((2:ZMod m)^i) := ((ZMod.isUnit_iff_coprime 2 m).mpr hodd).pow i
  apply (hu.mul_right_inj).mp
  dsimp only [value] at h hr
  linear_combination h - hr

private theorem square_odd {q : ℕ} (hq : q.Prime) (h2 : 2 < q) : Nat.Coprime 2 (q^2) :=
  ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_right 2

private theorem root_coprime (first : Bool) {q i : ℕ} (hq : q.Prime) (h2 : 2 < q)
    (hi : 0 < i) (hbig : 2^i < q) : (root first (q^2) i).Coprime q := by
  let : NeZero (q^2) := .of_pos (pow_pos hq.pos _)
  apply Nat.Coprime.symm
  apply hq.coprime_iff_not_dvd.mpr
  intro hd
  let f := ZMod.castHom (dvd_pow_self q (by decide : 2≠0)) (ZMod q)
  have hh := congrArg f (root_spec first (square_odd hq h2) i)
  have hz := (ZMod.natCast_eq_zero_iff ..).mpr hd
  have he : (2:ZMod q)^i = 1 := by
    cases first <;>
      simp only [value, fixed, Bool.false_eq_true, if_false, if_true, map_add, map_mul, map_pow,
        map_sub, map_neg, map_natCast, map_one, map_ofNat, map_zero, hz] at hh
    · linear_combination -hh
    · linear_combination hh
  have hm : 2^i ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using he)
  have := hm.eq_of_lt_of_lt hbig hq.one_lt
  have := Nat.one_lt_pow (by omega : i≠0) (by decide : 1 < 2)
  omega

private theorem unique_site (first : Bool) {p q i j k : ℕ} (hp : 3 ≤ p) (hq : q.Prime)
    (hbig : 2^k < q) (hi : i ≤ k) (hj : j ≤ k)
    (h₁ : q ∣ term first p i) (h₂ : q ∣ term first p j) : i=j := by
  let x := if first then p+1 else p-1
  have hx : 2 ≤ x := by cases first <;> simp [x] <;> omega
  have hseed : PrimeReturns.orbitValue first x 0 = p := by
    cases first <;> simp [PrimeReturns.orbitValue, x]; omega
  have he (d : ℕ) : term first p d = PrimeReturns.orbitValue first x d := by
    simpa only [hseed, Nat.zero_add] using PrimeReturns.orbit_restart first hx 0 d
  exact PrimeReturns.unique_zero_position first hq hbig (by omega) hi hj (he i ▸ h₁) (he j ▸ h₂)

private theorem base_progression (first : Bool) {k t R : ℕ} (hk : 0 < k) (ht : t.Prime)
    (h2 : 2 < t) (hbig : 2^k < t) (hR : t ≤ R) :
    ∃ m b : ℕ, 0 < m ∧ b.Coprime m ∧ (∀ q, q.Prime → R < q → m.Coprime q) ∧
      ∀ p, 3 ≤ p → p ≡ b [MOD m] →
        t^2 ∣ term first p k ∧ ∀ i < k, ∀ q, q.Prime → q ≤ R → ¬q ∣ term first p i := by
  classical
  let Q := R.primesLE
  let r (q : ℕ) := if q=t then root first (t^2) k else (fixed first (ZMod q)).val
  have prime_mem {q} (hq : q∈Q) := (Nat.mem_primesLE.mp hq).2
  let moduli (q : ℕ) := q^2
  let m := ∏ q ∈ Q, moduli q
  let b := Nat.chineseRemainderOfFinset r moduli Q
    (fun q hq => pow_ne_zero 2 (prime_mem hq).ne_zero)
    (fun q hq v hv hne => (((Nat.coprime_primes (prime_mem hq) (prime_mem hv)).mpr hne).pow_left 2).pow_right 2)
  have hsub {q} (hq : q∈Q) : q^2 ∣ m := dvd_prod_of_mem moduli hq
  have hred {q} (hq : q∈Q) : (r q).Coprime q := by
    by_cases he : q=t
    · subst q
      simpa [r] using root_coprime first ht h2 hk hbig
    · have hq' := prime_mem hq
      let : Fact q.Prime := ⟨hq'⟩
      apply Nat.Coprime.symm
      apply hq'.coprime_iff_not_dvd.mpr
      rw [← ZMod.natCast_eq_zero_iff]
      simp only [r, if_neg he, ZMod.natCast_zmod_val]
      cases first <;> simp [fixed]
  refine ⟨m,b.val,prod_pos (fun q hq => pow_pos (prime_mem hq).pos 2),
    Nat.Coprime.prod_right (fun q hq => ?_),fun q hq hlarge => ?_,?_⟩
  · exact (show b.val.Coprime q from ((b.property q hq).of_dvd
      (dvd_pow_self q (by decide : 2≠0))).gcd_eq.trans (hred hq)).pow_right 2
  · apply Nat.Coprime.symm
    exact Nat.Coprime.prod_right fun v hv => ((Nat.coprime_primes hq (prime_mem hv)).mpr
      (by have := (Nat.mem_primesLE.mp hv).1; omega)).pow_right 2
  intro p hp hpb
  have hr {q} (hq : q∈Q) : p ≡ r q [MOD q^2] :=
    (hpb.of_dvd (hsub hq)).trans (b.property q hq)
  let : NeZero (t^2) := .of_pos (pow_pos ht.pos _)
  have hterm : t^2 ∣ term first p k := (root_iff first (by omega) (square_odd ht h2) k).mpr
    (by simpa [r] using hr (Nat.mem_primesLE.mpr ⟨hR,ht⟩))
  refine ⟨hterm,?_⟩
  intro i hi q hq hsmall hdiv
  by_cases he : q=t
  · subst q
    have := unique_site first hp ht hbig hi.le le_rfl hdiv
      ((dvd_pow_self t (by decide : 2≠0)).trans hterm)
    omega
  · let : Fact q.Prime := ⟨hq⟩
    have hc := (ZMod.natCast_eq_natCast_iff ..).mpr
      ((hr (Nat.mem_primesLE.mpr ⟨hsmall,hq⟩)).of_dvd (dvd_pow_self q (by decide : 2≠0)))
    simp only [r, if_neg he, ZMod.natCast_zmod_val] at hc
    have hv := (ZMod.natCast_eq_zero_iff ..).mpr hdiv
    rw [cast_term first (by omega), value, hc, sub_self, mul_zero, zero_add] at hv
    cases first <;> simp [fixed] at hv

/-- For either canonical recurrence and any positive length, one terminal prime works
for every roughness cutoff. The product over the prefix is squarefree at infinitely
many prime seeds, and the square of the terminal prime divides the following term. -/
theorem infinitely_many_squarefree_prime_seeds (first : Bool) (k : ℕ) (hk : 0 < k) :
    ∃ t : ℕ, t.Prime ∧ ∀ B : ℕ,
      {p : ℕ | p.Prime ∧
        Squarefree (∏ i ∈ range k, (if first then firstKindTerm else secondKindTerm) p i) ∧
        (∀ q : ℕ, q.Prime → q ∣ ∏ i ∈ range k, (if first then firstKindTerm else secondKindTerm) p i →
          B < q) ∧ t^2 ∣ (if first then firstKindTerm else secondKindTerm) p k ∧
        ¬((if first then firstKindTerm else secondKindTerm) p k).Prime}.Infinite := by
  classical
  obtain ⟨t,ht',ht⟩ := Nat.exists_infinite_primes (2^k+3)
  have hpow : 0 < (2:ℕ)^k := by positivity
  have hbig : 2^k < t := by omega
  have ht2 : 2 < t := by omega
  refine ⟨t,ht,fun B => ?_⟩
  let R := B + 4*k + t + 2^k + 2
  have hR : t ≤ R := by dsimp [R]; omega
  obtain ⟨m,b,hm,hb,hcop,hbase⟩ := base_progression first hk ht ht2 hbig hR
  let : NeZero m := .of_pos hm
  let a (i : Fin k) (q : ℕ) := root first (q^2) (i.val+1)
  have hunit (i : Fin k) (q : ℕ) (hq : q.Prime) (hlarge : R < q) : (a i q).Coprime q := by
    have hl := Nat.pow_le_pow_right (by decide : 0 < 2) (show i.val+1≤k from i.isLt)
    exact root_coprime first hq (by omega) (by omega) (by omega)
  have hinf := SquarefreeAtPrimes.infinitely_many_avoiding_squares hb (by dsimp [R]; omega : 0 < R)
    (by dsimp [R]; omega : 4*k ≤ R) (2^(k+1)) a hcop hunit
  apply (hinf.sdiff (Set.finite_Iio (3:ℕ))).mono
  rintro p ⟨⟨hp,hpb,havoid⟩,hpl⟩
  have hp3 : 3 ≤ p := Nat.le_of_not_gt hpl
  obtain ⟨hend,hsmall⟩ := hbase p hp3 hpb
  have rough {i q : ℕ} (hi : i < k) (hq : q.Prime) (hd : q ∣ term first p i) : R < q :=
    lt_of_not_ge fun hle => hsmall i hi q hq hle hd
  have hsquare {i : ℕ} (hi : i < k) : Squarefree (term first p i) := by
    cases i with
    | zero => cases first <;> simpa [term, firstKindTerm, secondKindTerm] using hp.squarefree
    | succ j =>
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro q hq hd
      have hd' : q^2 ∣ term first p (j+1) := by simpa [pow_two] using hd
      have hlarge := rough hi hq ((dvd_pow_self q (by decide : 2≠0)).trans hd')
      let : NeZero (q^2) := .of_pos (pow_pos hq.pos _)
      have hl := term_bounds first hp.pos (j+1)
      have hsize : q^2 ≤ 2^(k+1)*p := calc
        q^2 ≤ term first p (j+1) := Nat.le_of_dvd hl.1 hd'
        _ ≤ 2^(j+1)*(p+1) := by omega
        _ ≤ 2^k*(2*p) := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hi.le) (by omega)
        _ = _ := by rw [pow_succ]; ring
      exact havoid ⟨j,by omega⟩ q hq hlarge hsize
        ((root_iff first hp.pos (square_odd hq (by omega)) (j+1)).mp hd')
  refine ⟨hp,Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun i hi => hsquare (mem_range.mp hi)),
    ?_,hend,fun hprime => Nat.squarefree_iff_prime_squarefree.mp hprime.squarefree t ht
      (by simpa [pow_two] using hend)⟩
  · intro i hi j hj hij
    apply Nat.coprime_iff_isRelPrime.mp
    apply Nat.coprime_of_dvd
    intro q hq hqi hqj
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have hlarge := rough hi' hq hqi
    exact hij (unique_site first hp3 hq (by omega) hi'.le hj'.le hqi hqj)
  · intro q hq hd
    obtain ⟨i,hi,hi'⟩ := (hq.prime.dvd_finsetProd_iff _).mp hd
    have := rough (mem_range.mp hi) hq hi'
    dsimp [R] at this
    omega

#print axioms infinitely_many_squarefree_prime_seeds

end CunninghamChain.SquarefreeSeeds
