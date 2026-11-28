import CunninghamUnboundedPrefixes
import FormalConjectures.Wikipedia.ArtinPrimitiveRootsConjecture
import FormalConjectures.Paper.PrimeTuples

/-! Simultaneous prime chains starting a fixed distance apart. -/

namespace CunninghamChain.PairedGaps

open ArtinPrimitiveRootsConjecture

/-- A safe prime congruent to three modulo eight has primitive root two. -/
theorem safe_prime_generator {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (he : q = 2*p+1) (h8 : q%8 = 3) (h3 : 3 < q) : q ∈ S 2 := by
  let : Fact q.Prime := ⟨hq⟩
  have htwo : (2:ZMod q) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  let d := orderOf (2:ZMod q)
  have hd : d ∣ 2*p := by
    rw [show 2*p=q-1 by omega]
    exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one htwo)
  have hn : ¬ d ∣ p := by
    intro h
    have hpow : (2:ZMod q)^p = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    have hodd := hp.odd_of_ne_two (by intro hh; subst p; omega)
    obtain ⟨c,hc⟩ := hodd
    have hs : IsSquare (2:ZMod q) := ⟨2^(c+1),by
      rw [← pow_add,show c+1+(c+1)=p+1 by omega,pow_succ,hpow,one_mul]⟩
    have hh := (ZMod.exists_sq_eq_two_iff (by omega : q ≠ 2)).mp hs
    omega
  have hn2 : ¬ d ∣ 2 := by
    intro h
    have hh : (2:ZMod q)^2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    have hz : (3 : ZMod q) = 0 := by linear_combination hh
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0<3) h3)
      ((ZMod.natCast_eq_zero_iff ..).mp (by exact_mod_cast hz))
  obtain ⟨a,b,ha,hb,hab⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  rcases (Nat.dvd_prime Nat.prime_two).mp ha with rfl | rfl
  · exact False.elim (hn (by simpa [hab] using hb))
  · rcases (Nat.dvd_prime hp).mp hb with rfl | rfl
    · exact False.elim (hn2 (by simp [hab]))
    · exact ⟨hq,by simpa using (show d=q-1 by omega)⟩

/-- Dickson supplies safe primes in the congruence class 3 modulo 8. Each
such prime greater than three has base two as a primitive root. -/
theorem infinite_primitive_two_of_prime_tuples
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture) : (S 2).Infinite := by
  let a : Fin 2 → ℕ+ := ![4,8]
  let b : Fin 2 → ℕ := ![1,3]
  have hlocal (p : ℕ) (hp : p.Prime) : ∃ n : ℕ, ¬p ∣ ∏ i, (a i * n+b i) := by
    by_cases h : p=3
    · subst p; exact ⟨1,by decide⟩
    · refine ⟨0,?_⟩
      simp only [mul_zero,zero_add,Fin.prod_univ_two]
      change ¬p ∣ 1*3
      simpa only [one_mul,Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)] using h
  have hpr := hD (by decide : 2 ≤ 2) a b hlocal
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨n,hn,hB⟩ := Set.infinite_iff_exists_gt.mp hpr B
  have hp : (4*n+1).Prime := hn 0
  have hq : (8*n+3).Prime := hn 1
  exact ⟨8*n+3,safe_prime_generator hp hq (by omega) (by omega) (by omega),by omega⟩

#print axioms safe_prime_generator
#print axioms infinite_primitive_two_of_prime_tuples

/-- At gap h, the second-kind seed is p+h and the first-kind seed is p.
With center a=p+1 the two signed shifts are a and a+h−2. -/
def GapAdmissible (h : ℕ) : Prop := ∀ k q : ℕ, q.Prime → ∃ a : ZMod q,
  ∀ i < k, (2:ZMod q)^i*a ≠ 1 ∧ (2:ZMod q)^i*(a+h-2) ≠ -1

private theorem local_primitive {q : ℕ} (hq : q ∈ S 2) :
    2 < q ∧ ∀ a : ZMod q, a ≠ 0 → ∃ i < q-1, (2:ZMod q)^i*a = 1 := by
  have ho : orderOf (2:ZMod q) = q-1 := by simpa using hq.2
  have hodd : 2 < q := by
    have hp := hq.1.two_le
    by_contra! hh
    obtain rfl : q=2 := by omega
    rw [show (2:ZMod 2)=0 by decide,orderOf_zero] at ho
    omega
  let : Fact q.Prime := ⟨hq.1⟩
  let : NeZero (q-1) := ⟨by omega⟩
  have hr : IsPrimitiveRoot (2:ZMod q) (q-1) := ho ▸ IsPrimitiveRoot.orderOf _
  refine ⟨hodd,?_⟩
  intro a ha
  obtain ⟨i,hi,hh⟩ := hr.eq_pow_of_pow_eq_one (ξ:=a⁻¹)
    (ZMod.pow_card_sub_one_eq_one (inv_ne_zero ha))
  exact ⟨i,hi,by rw [hh,inv_mul_cancel₀ ha]⟩

private theorem local_nonprimitive (h q : ℕ) (hq : q.Prime) (hq2 : 2 < q) (hn : q ∉ S 2) :
    ∃ a : ZMod q, ∀ i : ℕ, (2:ZMod q)^i*a ≠ 1 ∧ (2:ZMod q)^i*(a+h-2) ≠ -1 := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  have htwo : (2:ZMod q) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq2)
  let d := orderOf (2:ZMod q)
  have hd : 0 < d := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨q-1,by omega,ZMod.pow_card_sub_one_eq_one htwo⟩)
  have hd' : d ≠ q-1 := fun he => hn ⟨hq,by simpa using he⟩
  have hb : 2*d < q := by
    obtain ⟨c,hc⟩ := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one htwo)
    change q-1 = d*c at hc
    have hc' : 2 ≤ c := by
      by_contra! hh
      interval_cases c <;> simp_all; omega
    have := Nat.mul_le_mul_left d hc'
    omega
  let r (i : ℕ) := ((2:ZMod q)^i)⁻¹
  let s (i : ℕ) := -r i - h + 2
  let A := (Finset.range d).image r
  let B := (Finset.range d).image s
  have ha : A.card ≤ d := (Finset.card_image_le).trans_eq (Finset.card_range d)
  have hb' : B.card ≤ d := (Finset.card_image_le).trans_eq (Finset.card_range d)
  have hcard := Finset.card_union_le A B
  obtain ⟨a,_,haz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (A ∪ B).card < (Finset.univ : Finset (ZMod q)).card by
      rw [Finset.card_univ,ZMod.card]; omega)
  refine ⟨a,fun i => ?_⟩
  have hm : i%d ∈ Finset.range d := Finset.mem_range.mpr (Nat.mod_lt _ hd)
  have hr : r (i%d) = r i := by dsimp [r,d]; rw [pow_mod_orderOf]
  have hh := pow_ne_zero i htwo
  constructor
  · intro he
    apply haz (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i%d,hm,?_⟩))
    rw [hr]; dsimp [r]; field_simp; linear_combination -he
  · intro he
    apply haz (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i%d,hm,?_⟩))
    dsimp only [s]; rw [hr]; dsimp [r]; field_simp; linear_combination -he

/-- A pair of chains avoids a local obstruction at every length exactly when
its gap is even and agrees with 2 modulo every base-two primitive-root prime. -/
theorem gap_admissible_iff (h : ℕ) :
    GapAdmissible h ↔ Even h ∧ ∀ q ∈ S 2, h ≡ 2 [MOD q] := by
  constructor
  · intro hl
    obtain ⟨x,hx⟩ := hl 1 2 Nat.prime_two
    have hh := hx 0 (by decide)
    simp only [pow_zero,one_mul] at hh
    have he := (by decide : ∀ a b : ZMod 2, a≠1 ∧ a+b-2≠-1 → b=0) x h hh
    refine ⟨even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff ..).mp he),?_⟩
    intro q hq
    have hq2 := (local_primitive hq).1
    obtain ⟨a,ha⟩ := hl (q-1) q hq.1
    have H := (local_primitive hq).2
    have hz : a=0 := by
      by_contra hh
      obtain ⟨i,hi,he⟩ := H a hh
      exact (ha i hi).1 he
    subst a
    have hz' : (h:ZMod q)-2=0 := by
      by_contra hh
      obtain ⟨i,hi,he⟩ := H (-((h:ZMod q)-2)) (neg_ne_zero.mpr hh)
      apply (ha i hi).2
      rw [zero_add]; linear_combination -he
    exact (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using sub_eq_zero.mp hz')
  · rintro ⟨he,hr⟩ k q hq
    by_cases ht : q=2
    · subst q
      have hh : (h:ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff ..).mpr (even_iff_two_dvd.mp he)
      exact ⟨0,fun i _ => by simp [hh,show (2:ZMod 2)=0 by decide]⟩
    · by_cases hprim : q ∈ S 2
      · let : Fact q.Prime := ⟨hq⟩
        have hh : (h:ZMod q)=2 := by simpa using (ZMod.natCast_eq_natCast_iff ..).mpr (hr q hprim)
        exact ⟨0,fun i _ => by simp [hh]⟩
      · obtain ⟨a,ha⟩ := local_nonprimitive h q hq (lt_of_le_of_ne hq.two_le (Ne.symm ht)) hprim
        exact ⟨a,fun i _ => ha i⟩

#print axioms gap_admissible_iff

/-- Even at the level of congruence obstructions alone, uniqueness of the
bi-twin gap is equivalent to the infinitude part of Artin's base-two problem. -/
theorem unique_admissible_gap_iff :
    (∀ h, GapAdmissible h ↔ h=2) ↔ (S 2).Infinite := by
  classical
  constructor
  · intro hu hf
    let Q := hf.toFinset
    let m := ∏ q ∈ Q, q
    have hp : 0 < m := Finset.prod_pos (fun q hq =>
      (show q ∈ S 2 from hf.mem_toFinset.mp hq).1.pos)
    have ha : GapAdmissible (2+2*m) := by
      rw [gap_admissible_iff]
      refine ⟨⟨1+m,by omega⟩,?_⟩
      intro q hq
      have hd : q ∣ m := Finset.dvd_prod_of_mem id (hf.mem_toFinset.mpr hq)
      have hm : (m:ZMod q)=0 := (ZMod.natCast_eq_zero_iff ..).mpr hd
      apply (ZMod.natCast_eq_natCast_iff ..).mp
      push_cast; rw [hm]; ring
    have := (hu _).mp ha
    omega
  · intro hinf h
    rw [gap_admissible_iff]
    constructor
    · rintro ⟨_,hc⟩
      obtain ⟨q,hq,hbig⟩ := Set.infinite_iff_exists_gt.mp hinf (h+2)
      have he := hc q hq
      change h%q = 2%q at he
      rwa [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at he
    · rintro rfl
      exact ⟨by decide,fun _ _ => Nat.ModEq.refl _⟩

#print axioms unique_admissible_gap_iff

private theorem first_center (p i : ℕ) : firstKindTerm p i + 1 = 2^i*(p+1) := by
  induction i with
  | zero => simp [firstKindTerm]
  | succ i ih => rw [firstKindTerm,pow_succ]; linarith [congrArg (2 * ·) ih]

private theorem second_center (p i : ℕ) (hp : 0 < p) :
    secondKindTerm p i = 2^i*(p-1)+1 := by
  induction i with
  | zero => simp [secondKindTerm]; omega
  | succ i ih => rw [secondKindTerm,ih,pow_succ,show 2^i*2*(p-1)=2*(2^i*(p-1)) by ring]; omega

/-- Actual prime pairs with unbounded seeds at every prefix length give local
admissibility, even when their stopping terms have not been specified. -/
theorem admissible_of_paired_prefixes {h : ℕ}
    (hs : ∀ k > 0, {p : ℕ | (∀ i < k, (firstKindTerm p i).Prime) ∧
      (∀ i < k, (secondKindTerm (p+h) i).Prime)}.Infinite) : GapAdmissible h := by
  intro k q hq
  obtain ⟨p,hp,hpq⟩ := Set.infinite_iff_exists_gt.mp (hs (k+1) (by omega)) q
  have hq2 := hq.two_le
  have he (i : ℕ) : 1 ≤ 2^i := Nat.one_le_two_pow
  refine ⟨(p:ZMod q)+1,?_⟩
  intro i hi
  obtain ⟨hu,hl⟩ := hp
  have h₁ := hu i (by omega)
  have h₂ := hl i (by omega)
  have hf := first_center p i
  have hg := second_center (p+h) i (by omega)
  have hdiv (v : ℕ) (hv : v.Prime) (hh : q < v) : (v:ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff,Nat.prime_dvd_prime_iff_eq hq hv]
    omega
  have h₁' := hdiv _ h₁ (by nlinarith [Nat.mul_le_mul_right (p+1) (he i)])
  have hh := Nat.mul_le_mul_right (p+h-1) (he i)
  have h₂' := hdiv _ h₂ (by rw [one_mul] at hh; omega)
  have hf' := congrArg (fun n : ℕ => (n:ZMod q)) hf
  have hg' := congrArg (fun n : ℕ => (n:ZMod q)) hg
  push_cast at hf' hg'
  rw [Nat.cast_sub (by omega : 1 ≤ p+h)] at hg'
  push_cast at hg'
  constructor
  · intro heq; exact h₁' (by linear_combination hf' + heq)
  · intro heq; exact h₂' (by linear_combination hg' + heq)

private def value (b : Bool) (i x : ℕ) := if b then 2^i*x-1 else 2^i*x+1

private def sign (b : Bool) {R : Type*} [Ring R] : R := if b then 1 else -1

private theorem cast_value {q x : ℕ} (hx : 0 < x) (b : Bool) (i : ℕ) :
    (value b i x : ZMod q) = 2^i*(x:ZMod q)-sign b := by
  have h₁ : 1 ≤ 2^i*x := Nat.mul_pos (by positivity) hx
  cases b <;> simp [value,sign,Nat.cast_sub h₁]

private theorem distinct_forms {q D x i j : ℕ} (hqD : 2^(D+1)+1 < q)
    (hx : 0 < x) (hi : i ≤ D) (hj : j ≤ D) {b c : Bool}
    (hb : q ∣ value b i x) (hc : q ∣ value c j x) : i=j ∧ b=c := by
  have H₁ := (ZMod.natCast_eq_zero_iff ..).mpr hb
  have H₂ := (ZMod.natCast_eq_zero_iff ..).mpr hc
  rw [cast_value hx] at H₁ H₂
  have he : (2:ZMod q)^j*sign b = (2:ZMod q)^i*sign c := by
    linear_combination (2:ZMod q)^i*H₂ - (2:ZMod q)^j*H₁
  have hi' : 2^i ≤ 2^D := Nat.pow_le_pow_right (by decide) hi
  have hj' : 2^j ≤ 2^D := Nat.pow_le_pow_right (by decide) hj
  rw [pow_succ] at hqD
  have same (h : (2:ZMod q)^j=2^i) : i=j := by
    have h' := (ZMod.natCast_eq_natCast_iff (2^j) (2^i) q).mp (by push_cast; exact h)
    change (2^j)%q=(2^i)%q at h'
    rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at h'
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) h'.symm
  have opp : (2:ZMod q)^i+(2:ZMod q)^j ≠ 0 := by
    intro hh
    have hv : q ∣ 2^i+2^j := (ZMod.natCast_eq_zero_iff ..).mp (by push_cast; exact hh)
    exact Nat.not_dvd_of_pos_of_lt (by positivity) (by omega) hv
  cases b <;> cases c <;> simp [sign] at he ⊢
  · exact same he
  · exact opp (by linear_combination -he)
  · exact opp (by linear_combination he)
  · exact same he

private theorem boundary_progression (k l : ℕ) :
    ∃ B M : ℕ, 2 < B ∧ 0 < M ∧ value true k B ∣ M ∧ value false l B ∣ M ∧
      ∀ q, q.Prime → q ∣ M → ∀ b i, i < (if b then k else l) → ¬ q ∣ value b i B := by
  let D := max k l
  let T := 2^(D+1)+1
  let B := 4*T.factorial
  let A := value true k B
  let C := value false l B
  have hB : 2 < B := by dsimp [B]; have := Nat.factorial_pos T; omega
  have hA : 0 < A := by
    change 0 < 2^k*B-1
    have := Nat.le_mul_of_pos_left B (by positivity : 0 < 2^k); omega
  have hC : 0 < C := by change 0 < _+1; omega
  refine ⟨B,A*C,hB,Nat.mul_pos hA hC,dvd_mul_right ..,dvd_mul_left ..,?_⟩
  intro q hq hqM b i hi hd
  have hT : T < q := by
    by_contra! hh
    have hz : (B:ZMod q)=0 := (ZMod.natCast_eq_zero_iff ..).mpr
      (dvd_mul_of_dvd_right (hq.dvd_factorial.mpr hh) 4)
    let : Fact q.Prime := ⟨hq⟩
    have hz' := (ZMod.natCast_eq_zero_iff ..).mpr hd
    rw [cast_value (by omega : 0<B),hz] at hz'
    cases b <;> simp [sign] at hz'
  have hi' : i ≤ D := by cases b <;> simp_all [D] <;> omega
  rcases hq.dvd_mul.mp hqM with ha | hc
  · obtain ⟨h₁,rfl⟩ := distinct_forms hT (by omega : 0<B) hi' (le_max_left k l) hd ha
    simp_all
  · obtain ⟨h₁,rfl⟩ := distinct_forms hT (by omega : 0<B) hi' (le_max_right k l) hd hc
    simp_all

private theorem affine_value (b : Bool) (i M n B : ℕ) (hB : 0 < B) :
    value b i (M*n+B) = 2^i*M*n + value b i B := by
  have hp := Nat.mul_pos (by positivity : 0 < 2^i) hB
  cases b <;> simp [value,Nat.mul_add,Nat.mul_assoc] <;> omega

/-- The two chains centered at p+1 can stop independently. Dickson supplies
infinitely many seeds for every ordered pair of positive exact lengths. -/
theorem infinite_paired_exact_of_prime_tuples
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture)
    {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    {p : ℕ | IsFirstKindChainOfLength p k ∧ IsSecondKindChainOfLength (p+2) l}.Infinite := by
  obtain ⟨B,M,hB,hM,hkM,hlM,avoid⟩ := boundary_progression k l
  let side (u : Fin (k+l)) : Bool := decide (u.val<k)
  let idx (u : Fin (k+l)) := if u.val<k then u.val else u.val-k
  have hi (u : Fin (k+l)) : idx u < (if side u then k else l) := by
    by_cases hh : u.val<k <;> simp [idx,side,hh]; omega
  let a (u : Fin (k+l)) : ℕ+ := ⟨2^idx u*M,Nat.mul_pos (by positivity) hM⟩
  let c (u : Fin (k+l)) := value (side u) (idx u) B
  have form (u : Fin (k+l)) (n : ℕ) :
      (a u:ℕ)*n+c u = value (side u) (idx u) (M*n+B) :=
    (affine_value _ _ _ _ _ (by omega : 0<B)).symm
  have admissible (q : ℕ) (hq : q.Prime) : ∃ n : ℕ, ¬q ∣ ∏ u, ((a u:ℕ)*n+c u) := by
    by_cases hm : q ∣ M
    · refine ⟨0,hq.prime.not_dvd_finsetProd fun u _ => ?_⟩
      simpa only [mul_zero,zero_add,c] using avoid q hq hm (side u) (idx u) (hi u)
    · let : Fact q.Prime := ⟨hq⟩
      have hm' : (M:ZMod q) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr hm
      obtain ⟨n,hn⟩ := ZMod.natCast_zmod_surjective (-(B:ZMod q)/(M:ZMod q))
      have hz : ((M*n+B:ℕ):ZMod q)=0 := by push_cast; rw [hn]; field_simp; ring
      refine ⟨n,hq.prime.not_dvd_finsetProd fun u _ => ?_⟩
      rw [form,← ZMod.natCast_eq_zero_iff,cast_value (by omega : 0<M*n+B),hz]
      cases side u <;> simp [sign]
  have hpr := hD (by omega : 2 ≤ k+l) a c admissible
  apply Set.infinite_of_forall_exists_gt
  intro H
  obtain ⟨n,hn,hnH⟩ := Set.infinite_iff_exists_gt.mp hpr H
  let x := M*n+B
  let p := x-1
  have hnx := Nat.le_mul_of_pos_left n hM
  have hx : 2 < x := by dsimp [x]; omega
  have h₁ (i : ℕ) : firstKindTerm p i = value true i x := by
    have hh := first_center p i
    change firstKindTerm p i = 2^i*x-1
    rw [show p+1=x by dsimp [p]; omega] at hh; omega
  have h₂ (i : ℕ) : secondKindTerm (p+2) i = value false i x := by
    rw [second_center (p+2) i (by omega),show p+2-1=x by dsimp [p]; omega]; rfl
  have hstop (b : Bool) (i : ℕ) (hd : value b i B ∣ M) : ¬ (value b i x).Prime := by
    let z := value b i B
    have hv : 1 < z := by
      have := Nat.le_mul_of_pos_left B (by positivity : 0<2^i)
      cases b <;> simp only [z,value,Bool.false_eq_true,↓reduceIte] <;> omega
    have hpos := Nat.mul_pos (Nat.mul_pos (by positivity : 0<2^i) hM) (by omega : 0<n)
    have he : value b i x = 2^i*M*n+z := affine_value _ _ _ _ _ (by omega : 0<B)
    have hd' : z ∣ value b i x := he ▸ dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _) dvd_rfl
    intro hp
    rcases (Nat.dvd_prime hp).mp hd' with h | h <;> omega
  refine ⟨p,⟨⟨hk,?_,h₁ k ▸ hstop true k hkM⟩,⟨hl,?_,h₂ l ▸ hstop false l hlM⟩⟩,?_⟩
  · intro i hik
    let u : Fin (k+l) := ⟨i,by omega⟩
    have hh := hn u
    rw [form] at hh
    simpa [h₁,side,idx,u,hik,x] using hh
  · intro i hil
    let u : Fin (k+l) := ⟨k+i,by omega⟩
    have hh := hn u
    rw [form] at hh
    simpa [h₂,side,idx,u,x] using hh
  · dsimp [p,x]; omega

#print axioms infinite_paired_exact_of_prime_tuples

/-- Under the canonical prime-tuples hypothesis, a fixed gap supports one
opposite-kind prime pair of arbitrarily long prefixes if and only if it is 2. -/
theorem unbounded_paired_prefixes_iff
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture) (h : ℕ) :
    (∀ L : ℕ, ∃ p : ℕ, ∀ i < L, (firstKindTerm p i).Prime ∧
      (secondKindTerm (p+h) i).Prime) ↔ h=2 := by
  constructor
  · intro hs
    apply ((unique_admissible_gap_iff.mpr (infinite_primitive_two_of_prime_tuples hD)) h).mp
    apply admissible_of_paired_prefixes
    intro k hk
    apply Set.infinite_of_forall_exists_gt
    intro B
    let L := B+k+6
    obtain ⟨p,hp⟩ := hs L
    have hp₀ : p.Prime := (hp 0 (by dsimp [L]; omega)).1
    have hbig : B < p := by
      by_contra! hbound
      by_cases h₂ : p=2
      · subst p
        exact (by decide : ¬(firstKindTerm 2 5).Prime) (hp 5 (by dsimp [L]; omega)).1
      · exact (both_nonprime_at_pred_of_odd_prime hp₀ h₂).1
          (hp (p-1) (by dsimp [L]; omega)).1
    exact ⟨p,⟨fun i hi => (hp i (by dsimp [L]; omega)).1,
      fun i hi => (hp i (by dsimp [L]; omega)).2⟩,hbig⟩
  · rintro rfl L
    obtain ⟨p,hp,hq⟩ := (infinite_paired_exact_of_prime_tuples hD
      (Nat.zero_lt_succ L) (Nat.zero_lt_succ L)).nonempty
    exact ⟨p,fun i hi => ⟨hp.2.1 i (by omega),hq.2.1 i (by omega)⟩⟩

#print axioms admissible_of_paired_prefixes
#print axioms unbounded_paired_prefixes_iff

end CunninghamChain.PairedGaps
