import FormalConjectures.Arxiv.«1104.1579».CunninghamChain
import FormalConjectures.Paper.PrimeTuples
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ChineseRemainder

/-! Common divisors of the composite boundaries of a complete Cunningham chain. -/

namespace CunninghamChain
namespace CompleteBoundary

/-- The pinned recurrence, with the first kind selected by `true`. -/
abbrev term (first : Bool) := if first then firstKindTerm else secondKindTerm

/-- Starting just after a composite predecessor, the pinned chain terminates after k primes. -/
def CompleteAfter (first : Bool) (a k : ℕ) : Prop :=
  2 ≤ a ∧ ¬a.Prime ∧ (if first then IsFirstKindChainOfLength else IsSecondKindChainOfLength)
    (term first a 1) k

private theorem term_shift (b : Bool) (a i : ℕ) :
    term b (term b a 1) i = term b a (i+1) := by
  cases b
  · induction i with
    | zero => rfl
    | succ i ih => exact congrArg (fun x : ℕ => 2*x-1) ih
  · induction i with
    | zero => rfl
    | succ i ih => exact congrArg (fun x : ℕ => 2*x+1) ih

private theorem term_ge (b : Bool) {a : ℕ} (_ha : 2 ≤ a) (i : ℕ) : a ≤ term b a i := by
  cases b <;> induction i with
  | zero => exact le_rfl
  | succ i ih => simp only [term, Bool.false_eq_true, ↓reduceIte, firstKindTerm, secondKindTerm] at *; omega

private theorem lt_term_succ (b : Bool) {a : ℕ} (ha : 2 ≤ a) (i : ℕ) : a < term b a (i+1) := by
  have h := term_ge b ha i
  cases b <;> simp only [term, Bool.false_eq_true, ↓reduceIte, firstKindTerm, secondKindTerm] at * <;> omega

private theorem term_mod (b : Bool) {a : ℕ} (ha : 2 ≤ a) (i m : ℕ) :
    (term b a i : ZMod m) = 2^i * ((a : ZMod m) + (if b then 1 else -1)) -
      (if b then 1 else -1) := by
  induction i with
  | zero => cases b <;> simp [term,firstKindTerm,secondKindTerm]
  | succ i ih =>
    have hg := term_ge b ha i
    cases b <;> simp only [term, Bool.false_eq_true, ↓reduceIte] at *
    · rw [secondKindTerm, Nat.cast_sub (by omega : 1 ≤ 2*secondKindTerm a i)]
      push_cast
      rw [ih,pow_succ]
      ring
    · rw [firstKindTerm]
      push_cast
      rw [ih,pow_succ]
      ring

private theorem boundary_dvd_iff {b : Bool} {a q : ℕ} (ha : 2 ≤ a) (hq : q ∣ a) (i : ℕ) :
    q ∣ term b a i ↔ (2 : ZMod q)^i = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, term_mod b ha, (ZMod.natCast_eq_zero_iff ..).mpr hq, zero_add]
  cases b
  · simp
    constructor <;> intro h <;> linear_combination -h
  · simp [sub_eq_zero]

/-- The gcd of the two outer values depends on the length through the Mersenne number. -/
theorem boundary_gcd (b : Bool) {a : ℕ} (ha : 2 ≤ a) (k : ℕ) :
    a.gcd (term b a (k+1)) = a.gcd (2^(k+1)-1) := by
  have test (q : ℕ) (h : q ∣ a) : q ∣ term b a (k+1) ↔ q ∣ 2^(k+1)-1 := by
    rw [boundary_dvd_iff ha h, ← ZMod.natCast_eq_zero_iff,
      Nat.cast_sub Nat.one_le_two_pow]
    simp [sub_eq_zero]
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left ..) ((test _ (Nat.gcd_dvd_left ..)).mp (Nat.gcd_dvd_right ..))
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left ..) ((test _ (Nat.gcd_dvd_left ..)).mpr (Nat.gcd_dvd_right ..))

/-- A prime dividing both composite boundaries first divides a Mersenne number at exponent k+1. -/
theorem boundary_prime_order {b : Bool} {a k q : ℕ} (hc : CompleteAfter b a k) (hq : q.Prime)
    (hdiv : q ∣ a.gcd (term b a (k+1))) : orderOf (2 : ZMod q) = k+1 := by
  obtain ⟨ha,_,hc⟩ := hc
  have hp (i : ℕ) (hi : i < k) : (term b a (i+1)).Prime := by
    rw [← term_shift]
    cases b <;> exact hc.2.1 i hi
  have hqa := hdiv.trans (Nat.gcd_dvd_left ..)
  apply (orderOf_eq_iff (Nat.succ_pos k)).mpr
  refine ⟨(boundary_dvd_iff ha hqa _).mp (hdiv.trans (Nat.gcd_dvd_right ..)), ?_⟩
  rintro (_|i) hi hpos he
  · omega
  · have hd := (boundary_dvd_iff (b := b) ha hqa (i+1)).mpr he
    have eq := (Nat.dvd_prime_two_le (hp i (by omega)) hq.two_le).mp hd
    have hl := lt_term_succ b ha i
    have hle := Nat.le_of_dvd (by omega : 0 < a) hqa
    omega

/-- The two composites adjacent to five primes in a complete chain are always coprime. -/
theorem five_boundaries_coprime {b : Bool} {a : ℕ} (hc : CompleteAfter b a 5) :
    a.Coprime (term b a 6) := by
  apply Nat.coprime_of_dvd
  intro q hq ha hs
  have hd := Nat.dvd_gcd ha hs
  have ho := (orderOf_eq_iff (by decide : 0 < 6)).mp (boundary_prime_order hc hq hd)
  have hm := hd
  change q ∣ a.gcd (term b a (5+1)) at hm
  rw [boundary_gcd b hc.1] at hm
  have h63 : q ∣ 3^2*7 := hm.trans (Nat.gcd_dvd_right ..)
  rcases hq.dvd_mul.mp h63 with h|h
  · have e := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h)
    subst q
    exact ho.2 2 (by decide) (by decide) (by decide)
  · have e := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 7)).mp h
    subst q
    exact ho.2 3 (by decide) (by decide) (by decide)

private theorem term_affine (b : Bool) {r : ℕ} (hr : 2 ≤ r) (d n i : ℕ) :
    term b (d*n+r) i = 2^i*d*n + term b r i := by
  induction i with
  | zero => cases b <;> simp [term, firstKindTerm, secondKindTerm]
  | succ i ih =>
    have h := term_ge b hr i
    cases b <;> simp only [term, Bool.false_eq_true, ↓reduceIte] at *
    · rw [secondKindTerm, ih, secondKindTerm, pow_succ]
      have e : 2^i*2*d*n = 2*(2^i*d*n) := by ring
      omega
    · rw [firstKindTerm, ih, firstKindTerm, pow_succ]
      ring

/-- Prime interiors of arithmetic progressions of predecessors, for either sign. -/
private theorem prime_interiors
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture) (b : Bool) {r d k : ℕ}
    (hr : 2 ≤ r) (hd : 0 < d) (hk : 0 < k)
    (localTest : ∀ q, q.Prime → q ∣ d → ∀ i < k, ¬q ∣ term b r (i+1)) :
    {n : ℕ | ∀ i < k, (term b (d*n+r) (i+1)).Prime}.Infinite := by
  let idx (j : Fin (k+1)) := j.val % k
  let slope (j : Fin (k+1)) : ℕ+ := ⟨2^(idx j+1)*d, by positivity⟩
  let start (j : Fin (k+1)) := term b r (idx j+1)
  have affine (j : Fin (k+1)) (n : ℕ) :
      slope j * n + start j = term b (d*n+r) (idx j+1) := (term_affine b hr ..).symm
  have adm (q : ℕ) (hq : q.Prime) : ∃ n, ¬q ∣ ∏ j, (slope j * n + start j) := by
    by_cases hqd : q ∣ d
    · refine ⟨0, hq.prime.not_dvd_finsetProd fun j _ => ?_⟩
      simpa [start] using localTest q hq hqd (idx j) (Nat.mod_lt _ hk)
    · let : Fact q.Prime := ⟨hq⟩
      have hu := (ZMod.natCast_eq_zero_iff d q).not.mpr hqd
      let s : ZMod q := if b then 1 else -1
      obtain ⟨n,hn⟩ := ZMod.natCast_zmod_surjective ((-s-(r : ZMod q))/(d : ZMod q))
      have hz : (d : ZMod q)*n+r+s = 0 := by rw [hn]; field_simp; ring
      refine ⟨n,hq.prime.not_dvd_finsetProd fun j _ => ?_⟩
      rw [affine, ← ZMod.natCast_eq_zero_iff, term_mod b (by omega)]
      push_cast
      change ¬ 2^(idx j+1) * ((d : ZMod q)*n+r+s) - s = 0
      rw [hz]
      cases b <;> simp [s]
  have primes := hD (by omega : 2 ≤ k+1) slope start adm
  apply primes.mono
  intro n hn i hi
  let j : Fin (k+1) := ⟨i,by omega⟩
  simpa [affine, j, idx, Nat.mod_eq_of_lt hi] using hn j

private theorem exact_of_interior {b : Bool} {a k : ℕ} (ha : 2 ≤ a) (hcomp : ¬a.Prime)
    (hk : 0 < k) (h : ∀ i < k, (term b a (i+1)).Prime) (hlast : ¬(term b a (k+1)).Prime) :
    CompleteAfter b a k := by
  refine ⟨ha,hcomp,?_⟩
  have hp (i : ℕ) (hi : i < k) : (term b (term b a 1) i).Prime := by rw [term_shift]; exact h i hi
  rw [← term_shift] at hlast
  cases b <;> exact ⟨hk,hp,hlast⟩

private theorem stop_residue (b : Bool) {q k : ℕ} [Fact q.Prime] (hq : 2^(k+1) < q) :
    ∃ z : ZMod q, let s : ZMod q := if b then 1 else -1
      2^(k+1)*(z+s)-s = 0 ∧ ∀ i < k, 2^(i+1)*(z+s)-s ≠ 0 := by
  let s : ZMod q := if b then 1 else -1
  have hs : s ≠ 0 := by cases b <;> simp [s]
  have htwo : (2 : ZMod q) ≠ 0 := by
    have hle : 2 ≤ 2^(k+1) := by rw [pow_succ]; have := @Nat.one_le_two_pow k; omega
    exact (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  let z := s/(2 : ZMod q)^(k+1)-s
  have hlast : (2 : ZMod q)^(k+1)*(z+s) = s := by
    dsimp [z]
    field_simp
    ring
  have hnz : z+s ≠ 0 := fun h => hs (by simpa [h] using hlast.symm)
  refine ⟨z,sub_eq_zero.mpr hlast,?_⟩
  intro i hi h
  have he := mul_right_cancel₀ hnz ((sub_eq_zero.mp h).trans hlast.symm)
  have hlt : (2:ℕ)^(i+1) < 2^(k+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hm : (2:ℕ)^(i+1) ≡ 2^(k+1) [MOD q] :=
    (ZMod.natCast_eq_natCast_iff ..).mp (by push_cast; exact he)
  exact hlt.ne (hm.eq_of_lt_of_lt (hlt.trans hq) hq)

private theorem simultaneous_residues (S : Finset ℕ) (pr : ∀ q ∈ S, q.Prime)
    (P : (q : ℕ) → ZMod q → Prop) (localSol : ∀ q ∈ S, ∃ u : ℕ, P q u) :
    ∃ u : ℕ, ∀ q ∈ S, P q u := by
  classical
  choose v hv using localSol
  let a (q : ℕ) := if h : q ∈ S then v q h else 0
  obtain ⟨u,hu⟩ := Nat.chineseRemainderOfFinset a id S (fun q h => (pr q h).ne_zero)
    (fun q hq p hp h => (Nat.coprime_primes (pr q hq) (pr p hp)).mpr h)
  refine ⟨u, fun q h => ?_⟩
  rw [(ZMod.natCast_eq_natCast_iff ..).mpr (hu q h)]
  simpa only [a,dif_pos h] using hv q h

private theorem choose_boundary_residue (b : Bool) {g M Q : ℕ} (hM : 0 < M) (hodd : ¬2 ∣ M)
    (hg : g ∣ M) (hQ : Q.Prime) (hbig : M < Q) (h2Q : 2 < Q) (z : ZMod Q) :
    ∃ u : ℕ, (∀ p, p.Prime → p ∣ M →
      (u : ZMod p) ≠ 0 ∧ (¬p ∣ g → (2 : ZMod p)*g*u = -(if b then 1 else -1))) ∧
      (2 : ZMod Q)*g*u = z := by
  classical
  let P (p : ℕ) (x : ZMod p) : Prop :=
    x ≠ 0 ∧ (¬p ∣ g → 2*g*x = -(if b then 1 else -1))
  have localSol (p : ℕ) (hp : p ∈ M.primeFactors) : ∃ v : ℕ, P p v := by
    have pp := Nat.prime_of_mem_primeFactors hp
    let : Fact p.Prime := ⟨pp⟩
    by_cases hpg : p ∣ g
    · exact ⟨1,by simp [P,hpg]⟩
    have hp2 : ¬p ∣ 2 := fun h => hodd ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp h ▸
      Nat.dvd_of_mem_primeFactors hp)
    have ht : (2 : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff 2 p).not.mpr hp2
    have hg' := (ZMod.natCast_eq_zero_iff g p).not.mpr hpg
    let s : ZMod p := if b then 1 else -1
    have hs : s ≠ 0 := by cases b <;> simp [s]
    obtain ⟨v,hv⟩ := ZMod.natCast_zmod_surjective (-s / (2*(g : ZMod p)))
    refine ⟨v,?_,fun _ => ?_⟩
    · rw [hv]
      exact div_ne_zero (neg_ne_zero.mpr hs) (mul_ne_zero ht hg')
    · change (2 : ZMod p)*g*v = -s
      rw [hv]
      field_simp
  obtain ⟨v,hv⟩ := simultaneous_residues M.primeFactors (fun _ => Nat.prime_of_mem_primeFactors) P localSol
  let : Fact Q.Prime := ⟨hQ⟩
  have hQM := Nat.not_dvd_of_pos_of_lt hM hbig
  have hgQ := (ZMod.natCast_eq_zero_iff g Q).not.mpr (fun h => hQM (h.trans hg))
  have htQ : (2 : ZMod Q) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 Q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) h2Q)
  obtain ⟨vQ,hvQ⟩ := ZMod.natCast_zmod_surjective (z / (2*(g : ZMod Q)))
  obtain ⟨u,hu,hQ'⟩ := Nat.chineseRemainder (hQ.coprime_iff_not_dvd.mpr hQM).symm v vQ
  refine ⟨u,?_,?_⟩
  · intro p pp hp
    rw [(ZMod.natCast_eq_natCast_iff ..).mpr (hu.of_dvd hp)]
    exact hv p (Nat.mem_primeFactors.mpr ⟨pp,hp,hM.ne'⟩)
  · rw [(ZMod.natCast_eq_natCast_iff ..).mpr hQ',hvQ]
    field_simp

/-- The arithmetically possible gcds of the two composite boundaries. -/
def Allowed (k g : ℕ) : Prop :=
  g ∣ 2^(k+1)-1 ∧ ∀ q, q.Prime → q ∣ g → orderOf (2 : ZMod q) = k+1

/-- Every actual complete chain satisfies the common-divisor restrictions without Dickson. -/
theorem allowed_of_complete {b : Bool} {a k : ℕ} (hc : CompleteAfter b a k) :
    Allowed k (a.gcd (term b a (k+1))) := by
  refine ⟨?_,fun _ hq => boundary_prime_order hc hq⟩
  rw [boundary_gcd b hc.1]
  exact Nat.gcd_dvd_right ..

private theorem mersenne_odd (k : ℕ) : ¬2 ∣ 2^(k+1)-1 := by
  rw [pow_succ]
  have := @Nat.one_le_two_pow k
  omega

/-- Every allowed gcd occurs infinitely often for both signs under the pinned Dickson hypothesis. -/
theorem infinite_complete_gcd_of_allowed
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture)
    (b : Bool) {k g : ℕ} (hk : 0 < k) (h : Allowed k g) :
    {a : ℕ | CompleteAfter b a k ∧ a.gcd (term b a (k+1)) = g}.Infinite := by
  let M := 2^(k+1)-1
  have hM : 0 < M := by dsimp [M]; have := @Nat.one_le_two_pow k; rw [pow_succ]; omega
  have hg : g ∣ M := h.1
  have hgp := Nat.pos_of_dvd_of_pos hg hM
  obtain ⟨Q,hbig,hQ⟩ := Nat.exists_infinite_primes (2^(k+1)+3)
  let : Fact Q.Prime := ⟨hQ⟩
  have hQM : M < Q := by dsimp [M]; omega
  obtain ⟨z,hz,hzi⟩ := stop_residue b (k := k) (q := Q) (by omega)
  obtain ⟨u,hu,huQ⟩ := choose_boundary_residue b hM (mersenne_odd k) hg hQ hQM (by omega) z
  let T := M*Q
  let v (n : ℕ) := T*n+T+u
  let r := 2*g*(T+u)
  let d := 2*g*T
  have hT : 0 < T := Nat.mul_pos hM hQ.pos
  have hr : 2 ≤ r := by dsimp [r]; nlinarith
  have hd : 0 < d := by dsimp [d]; positivity
  have rep (n : ℕ) : d*n+r = 2*g*v n := by dsimp [d,r,v]; ring
  have vmod {p : ℕ} (hp : p ∣ T) (n : ℕ) : (v n : ZMod p) = u := by
    dsimp [v]
    push_cast
    rw [(ZMod.natCast_eq_zero_iff ..).mpr hp]
    simp
  have rmod {p : ℕ} (hp : p ∣ T) (n : ℕ) :
      ((d*n+r : ℕ) : ZMod p) = 2*g*u := by rw [rep]; push_cast; rw [vmod hp]
  have cop (n : ℕ) : (2*v n).Coprime M := by
    apply Nat.coprime_of_dvd
    intro p pp hp hpm
    rcases pp.dvd_mul.mp hp with htwo|hv
    · have he : p = 2 := (Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp htwo
      rw [he] at hpm
      exact mersenne_odd k hpm
    · exact (hu p pp hpm).1 ((vmod (hpm.trans (dvd_mul_right M Q)) n) ▸
        (ZMod.natCast_eq_zero_iff ..).mpr hv)
  have modQ (n : ℕ) : ((d*n+r : ℕ) : ZMod Q) = z := (rmod (dvd_mul_left Q M) n).trans huQ
  have locals (p : ℕ) (pp : p.Prime) (hpd : p ∣ d) (i : ℕ) (hi : i < k) :
      ¬p ∣ term b r (i+1) := by
    let : Fact p.Prime := ⟨pp⟩
    by_cases hpg : p ∣ g
    · have hpr : p ∣ r := (hpg.trans (dvd_mul_left g 2)).trans (dvd_mul_right (2*g) (T+u))
      exact (boundary_dvd_iff hr hpr _).not.mpr
        (((orderOf_eq_iff (Nat.succ_pos k)).mp (h.2 p pp hpg)).2 _ (by omega) (by omega))
    by_cases he : p = 2
    · subst p
      rw [← ZMod.natCast_eq_zero_iff,term_mod b hr,pow_succ,show (2 : ZMod 2)=0 from (ZMod.natCast_eq_zero_iff 2 2).mpr dvd_rfl]
      cases b <;> simp
    have hpt : p ∣ T := (pp.dvd_mul.mp hpd).resolve_left fun hh =>
      ((pp.dvd_mul.mp hh).elim (fun hp2 => he ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp hp2)) hpg)
    have hr' : (r : ZMod p) = 2*g*u := by simpa using rmod hpt 0
    rw [← ZMod.natCast_eq_zero_iff,term_mod b hr,hr']
    rcases pp.dvd_mul.mp hpt with hpm|hpQ
    · rw [(hu p pp hpm).2 hpg,neg_add_cancel]
      cases b <;> simp
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq pp hQ).mp hpQ
      rw [huQ]
      exact hzi i hi
  have inf := prime_interiors hD b hr hd hk locals
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨n,hn,hlarge⟩ := Set.infinite_iff_exists_gt.mp inf (B+Q+2)
  have hle := Nat.le_mul_of_pos_left n hd
  have ha : 2 ≤ d*n+r := by omega
  have hpre : ¬(d*n+r).Prime := by
    intro hp
    have hdv : 2 ∣ d*n+r := by rw [rep]; exact (dvd_mul_right 2 g).trans (dvd_mul_right _ _)
    have := (Nat.dvd_prime_two_le hp (by decide : 2 ≤ 2)).mp hdv
    omega
  have hstop : ¬(term b (d*n+r) (k+1)).Prime := by
    intro hp
    have dv : Q ∣ term b (d*n+r) (k+1) := by
      rw [← ZMod.natCast_eq_zero_iff,term_mod b ha,modQ]
      exact hz
    have := (Nat.dvd_prime_two_le hp hQ.two_le).mp dv
    have := term_ge b ha (k+1)
    omega
  refine ⟨d*n+r,⟨exact_of_interior ha hpre hk hn hstop,?_⟩,by omega⟩
  rw [boundary_gcd b ha,rep,show 2*g*v n = (2*v n)*g by ring]
  exact Nat.gcd_mul_of_coprime_of_dvd (cop n) hg

#print axioms allowed_of_complete
#print axioms infinite_complete_gcd_of_allowed

/-- The complete two-sided boundary gcd spectrum, including exact multiplicities. -/
theorem infinite_complete_gcd_iff
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture)
    (b : Bool) {k g : ℕ} (hk : 0 < k) :
    {a : ℕ | CompleteAfter b a k ∧ a.gcd (term b a (k+1)) = g}.Infinite ↔ Allowed k g := by
  refine ⟨?_,infinite_complete_gcd_of_allowed hD b hk⟩
  intro hi
  obtain ⟨a,ha,he⟩ := hi.nonempty
  exact he ▸ allowed_of_complete ha

set_option exponentiation.threshold 512 in
set_option maxRecDepth 4096 in
/-- A repeated prime factor can occur as the exact boundary gcd.
Here 1093 is a base-two Wieferich prime of order 364. -/
theorem squared_boundary_at_length_363
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture) (b : Bool) :
    {a : ℕ | CompleteAfter b a 363 ∧ a.gcd (term b a 364) = 1093^2}.Infinite := by
  apply infinite_complete_gcd_of_allowed hD b (by decide : 0 < 363)
  refine ⟨by decide, ?_⟩
  intro q hq h
  have eq := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1093)).mp (hq.dvd_of_dvd_pow h)
  subst q
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · decide
  · intro p hp hd
    change p ∣ 2^2*7*13 at hd
    rcases hp.dvd_mul.mp hd with h₁|h₁₃
    · rcases hp.dvd_mul.mp h₁ with h₂|h₇
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h₂)
        decide
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h₇
        decide
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)).mp h₁₃
      decide

#print axioms infinite_complete_gcd_iff
#print axioms squared_boundary_at_length_363

#print axioms five_boundaries_coprime
#print axioms boundary_gcd
#print axioms boundary_prime_order

end CompleteBoundary
end CunninghamChain
