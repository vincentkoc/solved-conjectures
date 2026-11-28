import Mathlib
import FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes

/-! Binary forms on Fibonacci pairs for arithmetic index progressions. -/

namespace Arxiv.«2211.10788»
open Polynomial
open scoped Polynomial

/-- The homogeneous form with coefficients binom(d,i) U(r+i) in degrees (d-i,i). -/
def upperIndexForm {R : Type*} [CommSemiring R] (x y : R) : ℕ → ℕ → R
  | 0, r => lucasFibonacciSum r
  | d+1, r => x*upperIndexForm x y d r + y*upperIndexForm x y d (r+1)

/-- Dehomogenize by setting the second coordinate equal to one. -/
noncomputable def upperIndexPolynomial (r d : ℕ) : ℤ[X] := upperIndexForm X 1 d r

private lemma map_form {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (x y : R) (d r : ℕ) :
    f (upperIndexForm x y d r) = upperIndexForm (f x) (f y) d r := by
  induction d generalizing r with
  | zero => simp [upperIndexForm]
  | succ d ih => simp [upperIndexForm,map_add,map_mul,ih]

private lemma upper_add (r n : ℕ) : lucasFibonacciSum (r+n+1) =
    Nat.fib n*lucasFibonacciSum r + Nat.fib (n+1)*lucasFibonacciSum (r+1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [show r+1+1=r+2 by omega,lucas_fibonacci_sum_recurrence,add_comm]
  | more n h0 h1 =>
    rw [show r+(n+2)+1=r+n+1+2 by omega,lucas_fibonacci_sum_recurrence,h0,
      show r+n+1+1=r+(n+1)+1 by omega,h1,Nat.fib_add_two (n:=n),
      show n+2+1=(n+1)+2 by omega,Nat.fib_add_two (n:=n+1)]
    simp only [show n+1+1=n+2 by omega,Nat.fib_add_two (n:=n)]
    ring

/-- The form specializes exactly to the pinned upper term on each Fibonacci pair. -/
theorem upperIndexForm_fibonacci (r d n : ℕ) :
    upperIndexForm (Nat.fib n) (Nat.fib (n+1)) d r = lucasFibonacciSum (r+d*(n+1)) := by
  induction d generalizing r with
  | zero => simp [upperIndexForm]
  | succ d ih =>
    rw [upperIndexForm,ih,ih,show r+1+d*(n+1)=(r+d*(n+1))+1 by omega,←upper_add]
    congr 1
    ring

private lemma upper_mod_121 (r : ℕ) : (lucasFibonacciSum r : ZMod 121)
    = 100*37^r+22*85^r := by
  induction r using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h0 h1 =>
    rw [lucas_fibonacci_sum_recurrence,Nat.cast_add,h1,h0,pow_add,pow_add]
    rw [pow_succ (37:ZMod 121),pow_succ (85:ZMod 121)]
    ring_nf
    reduce_mod_char

private lemma binet_form {R : Type*} [CommRing R] (a b u v : R)
    (h : ∀ r : ℕ, (lucasFibonacciSum r:R)=a*u^r+b*v^r) (r d : ℕ) (x y : R) :
    upperIndexForm x y d r = a*u^r*(x+u*y)^d+b*v^r*(x+v*y)^d := by
  induction d generalizing r with
  | zero => simpa [upperIndexForm] using h r
  | succ d ih =>
    simp only [upperIndexForm,ih,pow_succ]
    ring

private lemma upper_mod_11 (r : ℕ) : (lucasFibonacciSum r:ZMod 11)=4^r := by
  induction r using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h0 h1 =>
    rw [lucas_fibonacci_sum_recurrence,Nat.cast_add,h1,h0,pow_add (4:ZMod 11) n 2,pow_succ (4:ZMod 11) n]
    linear_combination -(4:ZMod 11)^n * (by decide : (4:ZMod 11)^2 = 4+1)

private noncomputable def shifted (r d : ℕ) : ℤ[X] := upperIndexForm (X-4) 1 d r

private lemma mod_eleven_shift (r d : ℕ) :
    (shifted r d).map (Int.castRingHom (ZMod 11)) = C ((4:ZMod 11)^r)*X^d := by
  change (mapRingHom (Int.castRingHom (ZMod 11))) (upperIndexForm _ _ _ _) = _
  rw [map_form]
  simp only [map_sub,map_ofNat,map_one]
  have hC : C (4:ZMod 11) = (4:(ZMod 11)[X]) := map_ofNat C 4
  have h r : (lucasFibonacciSum r:(ZMod 11)[X]) = 1*(4:(ZMod 11)[X])^r+0*0^r := by
    simpa [hC] using congrArg (C : ZMod 11 → (ZMod 11)[X]) (upper_mod_11 r)
  rw [binet_form _ _ _ _ h]
  simp [map_pow,hC]

private lemma shifted_constant_exact (r d : ℕ) (hd : 2 ≤ d) :
    ¬(121:ℤ) ∣ (shifted r d).coeff 0 := by
  change ¬((121:ℕ):ℤ) ∣ _
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
  let f : ℤ[X] →+* ZMod 121 := eval₂RingHom (Int.castRingHom _) 0
  have he : ((shifted r d).coeff 0:ZMod 121) = f (shifted r d) := by
    simp [f,coeff_zero_eq_eval_zero,eval₂_at_zero]
  rw [he,shifted,map_form]
  have hx : f (X-4) = -4 := by simp [f]
  rw [hx,map_one,binet_form _ _ _ _ upper_mod_121]
  have hkill : (-4+37*1:ZMod 121)^d=0 := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hd
    rw [hk,pow_add,show (-4+37*1:ZMod 121)^2=0 by decide,zero_mul]
  rw [hkill,mul_zero,zero_add]
  have u : IsUnit (85:ZMod 121) := by apply (ZMod.isUnit_iff_coprime ..).mpr; decide
  have v : IsUnit (-4+85*1:ZMod 121) := by
    change IsUnit (81:ZMod 121)
    apply (ZMod.isUnit_iff_coprime ..).mpr
    decide
  exact fun hz => (by decide : (22:ZMod 121)≠0)
    ((u.pow r).mul_left_eq_zero.mp ((v.pow d).mul_left_eq_zero.mp hz))

private lemma rational_eisenstein_eleven {P : ℤ[X]} (hd : 0<P.natDegree)
    (hl : ¬(11:ℤ) ∣ P.leadingCoeff) (hcoeff : ∀ i < P.natDegree, (11:ℤ) ∣ P.coeff i)
    (hc : ¬(121:ℤ) ∣ P.coeff 0) : Irreducible (P.map (Int.castRingHom ℚ)) := by
  let Q := P.primPart
  have hp : Prime (11:ℤ) := by norm_num
  have he (i : ℕ) : P.coeff i=P.content*Q.coeff i := by
    calc P.coeff i = (C P.content*Q).coeff i := congrArg (fun p : ℤ[X] => p.coeff i) P.eq_C_content_mul_primPart
         _ = _ := coeff_C_mul _
  have hedeg : Q.natDegree=P.natDegree := P.natDegree_primPart
  have hlead : P.leadingCoeff=P.content*Q.leadingCoeff := by
    simpa only [leadingCoeff,hedeg] using he P.natDegree
  have hu : ¬(11:ℤ) ∣ P.content := fun h => hl (hlead ▸ dvd_mul_of_dvd_left h _)
  have hn : P.content ≠ 0 := by rintro h; exact hu (h ▸ dvd_zero _)
  have hI : (Ideal.span {(11:ℤ)}).IsPrime := (Ideal.span_singleton_prime (by norm_num)).mpr hp
  have ir : Irreducible Q := by
    apply irreducible_of_eisenstein_criterion hI
    · rw [Ideal.mem_span_singleton]
      exact fun h => hl (hlead ▸ dvd_mul_of_dvd_right h _)
    · intro n h
      rw [Ideal.mem_span_singleton]
      exact (hp.dvd_mul.mp (he n ▸ hcoeff n (hedeg ▸ WithBot.coe_lt_coe.mp (by simpa [degree_eq_natDegree P.primPart_ne_zero] using h)))).resolve_left hu
    · exact natDegree_pos_iff_degree_pos.mp (hedeg ▸ hd)
    · rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton]
      intro h
      exact hc ((he 0) ▸ dvd_mul_of_dvd_right h _)
    · exact P.isPrimitive_primPart
  have hq := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast P.isPrimitive_primPart).mp ir
  have hv : IsUnit (C (P.content:ℚ) : ℚ[X]) := (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hn)).map C
  have hassoc := associated_unit_mul_left (Q.map (Int.castRingHom ℚ)) (C (P.content:ℚ)) hv
  rw [show P.map (Int.castRingHom ℚ)=C (P.content:ℚ)*Q.map (Int.castRingHom ℚ) by
    conv_lhs => rw [P.eq_C_content_mul_primPart]
    simp [Q]]
  exact hassoc.irreducible_iff.mpr hq

private lemma form_degree_bound (l : ℤ[X]) (hl : l.natDegree ≤ 1) (r d : ℕ) :
    (upperIndexForm l 1 d r).natDegree ≤ d := by
  induction d generalizing r with
  | zero => simp [upperIndexForm]
  | succ d ih =>
    simp only [upperIndexForm,one_mul]
    exact (natDegree_add_le ..).trans (max_le
      ((natDegree_mul_le ..).trans (by have := ih r; omega)) ((ih (r+1)).trans (by omega)))

private lemma upper_positive (r : ℕ) : 0 < lucasFibonacciSum r := by
  unfold lucasFibonacciSum
  have := Nat.fib_pos.mpr (show 0<r+2 by omega)
  omega

private lemma absolute_form_leading (r d : ℕ) :
    (upperIndexPolynomial r d).coeff d=(lucasFibonacciSum r:ℤ) := by
  induction d generalizing r with
  | zero => simp [upperIndexPolynomial,upperIndexForm]
  | succ d ih =>
    change (X*(upperIndexPolynomial r d)+1*upperIndexPolynomial (r+1) d).coeff (d+1)=_
    have hdeg := form_degree_bound X (by simp) (r+1) d
    change (upperIndexPolynomial _ _).natDegree ≤ d at hdeg
    rw [one_mul,coeff_add,coeff_X_mul,coeff_eq_zero_of_natDegree_lt (by omega : (upperIndexPolynomial (r+1) d).natDegree < d+1),add_zero,ih]

private lemma absolute_form_degree (r d : ℕ) : (upperIndexPolynomial r d).natDegree=d := by
  refine (form_degree_bound X (by simp) r d).antisymm (le_natDegree_of_ne_zero ?_)
  change (upperIndexPolynomial r d).coeff d ≠ 0
  rw [absolute_form_leading]
  exact Int.natCast_ne_zero.mpr (upper_positive r).ne'

private lemma shifted_irreducible {r d : ℕ} (hd : 2≤d) :
    Irreducible ((shifted r d).map (Int.castRingHom ℚ)) := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let f := Int.castRingHom (ZMod 11)
  have hcoeff (i : ℕ) := congrArg (fun p : (ZMod 11)[X] => p.coeff i) (mod_eleven_shift r d)
  have htop : f ((shifted r d).coeff d)=(4:ZMod 11)^r := by
    simpa only [f,coeff_map,coeff_C_mul,coeff_X_pow,if_true,mul_one,Int.coe_castRingHom] using hcoeff d
  have htop' : f ((shifted r d).coeff d)≠0 := htop ▸ pow_ne_zero _ (by decide)
  have H : (shifted r d).natDegree=d := (form_degree_bound _ (by compute_degree) r d).antisymm
    (le_natDegree_of_ne_zero (fun h => htop' (h ▸ map_zero f)))
  apply rational_eisenstein_eleven (by omega : 0 < (shifted r d).natDegree)
  · rw [leadingCoeff,H]
    exact fun h => htop' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 11).mpr h)
  · intro i hi
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 11).mp
    simpa only [coeff_map,coeff_C_mul,coeff_X_pow,if_neg (show i≠d by omega),if_neg (show d≠i by omega),mul_zero,Int.coe_castRingHom] using hcoeff i
  · exact shifted_constant_exact r d hd

/-- On every positive-step index progression the dehomogenized binary form
is irreducible over the rationals. -/
theorem upperIndexPolynomial_irreducible (r d : ℕ) (hd : 0 < d) :
    Irreducible ((upperIndexPolynomial r d).map (Int.castRingHom ℚ)) := by
  by_cases h1 : d=1
  · apply irreducible_of_degree_eq_one
    rw [degree_eq_natDegree (by
      intro h
      have he := congrArg natDegree h
      rw [natDegree_map_eq_of_injective Int.cast_injective,absolute_form_degree,natDegree_zero] at he
      omega),natDegree_map_eq_of_injective Int.cast_injective,absolute_form_degree,h1]
    rfl
  let E := algEquivAevalXAddC (-4:ℚ)
  have he : E ((upperIndexPolynomial r d).map (Int.castRingHom ℚ)) =
      (shifted r d).map (Int.castRingHom ℚ) := by
    change E ((mapRingHom (Int.castRingHom ℚ)) (upperIndexForm X 1 d r)) =
      (mapRingHom (Int.castRingHom ℚ)) (upperIndexForm (X-4) 1 d r)
    rw [map_form,map_form]
    change E.toRingHom (upperIndexForm _ _ d r) = _
    rw [map_form]
    simp [E,algEquivAevalXAddC_apply,sub_eq_add_neg,show C (4:ℚ) = (4:ℚ[X]) from map_ofNat C 4]
  apply (MulEquiv.irreducible_iff (f := E)).mp
  rw [he]
  exact shifted_irreducible (by omega)

private lemma scaled_recurrence {K : Type*} [Field K] {a b : K}
    (ha : a*a=a+1) (hb : b*b=b+1) (n : ℕ) :
    (a-b)*(lucasFibonacciSum n:K)=(3+a)*a^n-(3+b)*b^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucas_fibonacci_sum_zero]
  | one =>
    rw [lucas_fibonacci_sum_one]
    push_cast
    linear_combination hb-ha
  | more n h0 h1 =>
    rw [lucas_fibonacci_sum_recurrence,Nat.cast_add,mul_add,h1,h0,pow_add a n 2,pow_add b n 2,
      pow_succ a n,pow_succ b n,pow_two,pow_two,ha,hb]
    ring

private lemma distinct_roots_nonvanishing {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) (r d : ℕ)
    (hd : 0 < d) : (upperIndexPolynomial r d).map (Int.castRingHom (ZMod p)) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_root (X^2-X-1 : K[X]) (by
    have h : (X^2-X-1 : K[X]).degree=2 := by compute_degree!
    rw [h]; decide)
  have ha' : a*a=a+1 := by
    simp only [IsRoot,eval_sub,eval_pow,eval_X,eval_one] at ha
    linear_combination ha
  let b := 1-a
  have hb : b*b=b+1 := by dsimp [b]; linear_combination ha'
  have hab : a-b ≠ 0 := by
    have h : (a-b)^2=(5:K) := by dsimp [b]; linear_combination 4*ha'
    intro he
    rw [he,zero_pow (by decide)] at h
    have hdvd := (CharP.cast_eq_zero_iff K p 5).mp h.symm
    exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hdvd)
  have hne (z : K) (h : z*z=z+1) : z ≠ 0 := by rintro rfl; simp at h
  let A := (3+a)/(a-b)
  let B := -(3+b)/(a-b)
  have hbin n : (lucasFibonacciSum n:K)=A*a^n+B*b^n := by
    change _ = ((3+a)/(a-b))*a^n+ (-(3+b)/(a-b))*b^n
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,←add_div]
    apply (eq_div_iff hab).mpr
    linear_combination scaled_recurrence ha' hb n
  intro hzero
  have vanish (x : K) : upperIndexForm x 1 d r = 0 := by
    let f := eval₂RingHom (algebraMap (ZMod p) K) x
    have h := congrArg f hzero
    change f ((mapRingHom _) (upperIndexForm X 1 d r)) = _ at h
    rw [map_form,map_form] at h
    simpa [f] using h
  have hA := vanish (-b)
  have hB := vanish (-a)
  rw [binet_form _ _ _ _ hbin] at hA hB
  have hane := hne a ha'
  have hbne := hne b hb
  have hba : b-a ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hab).symm
  have hn₁ : -b+a ≠ 0 := by rwa [add_comm,←sub_eq_add_neg]
  have hn₂ : -a+b ≠ 0 := by rwa [add_comm,←sub_eq_add_neg]
  simp [A,B,hd.ne',hane,hbne,hn₁,hn₂,hab] at hA hB
  exact hab (by linear_combination hA+hB)



private abbrev FormPair (R : Type*) [CommRing R] := QuadraticAlgebra R 1 1

private def formStart (R : Type*) [CommRing R] (r : ℕ) : FormPair R :=
  ⟨(lucasFibonacciSum (r+1):R)-lucasFibonacciSum r, lucasFibonacciSum r⟩

private lemma form_pair_value {R : Type*} [CommRing R] (x y : R) (d r : ℕ) :
    upperIndexForm x y d r = (formStart R r * (⟨x,y⟩:FormPair R)^d).im := by
  induction d generalizing r with
  | zero => simp [upperIndexForm,formStart]
  | succ d ih =>
    rw [upperIndexForm,ih,ih,pow_succ]
    let z := (⟨x,y⟩:FormPair R)^d
    change x*(formStart R r*z).im+y*(formStart R (r+1)*z).im =
      (formStart R r*(z*⟨x,y⟩)).im
    obtain ⟨u,v⟩ := z
    simp [formStart,QuadraticAlgebra.mk_mul_mk,lucas_fibonacci_sum_recurrence]
    ring

private lemma five_divides_imaginary (R : Type*) [CommRing R] (z : FormPair R) :
    (5:R)*z.im ∣ (z^5).im := by
  obtain ⟨u,v⟩ := z
  refine ⟨u^4+2*u^3*v+4*u^2*v^2+3*u*v^3+v^4,?_⟩
  simp only [pow_succ,pow_zero,one_mul,QuadraticAlgebra.mk_mul_mk]
  ring

private lemma five_power_imaginary {R : Type*} [CommRing R] (z : FormPair R) (k : ℕ) :
    (5:R)^k ∣ (z^(5^k)).im := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ (5:R),pow_succ (5:ℕ),pow_mul,mul_comm]
    exact (mul_dvd_mul_left (5:R) ih).trans (five_divides_imaginary R _)

private lemma five_content_lower {R : Type*} [CommRing R] (x y : R) (r d k : ℕ)
    (hu : (5:R)^k ∣ (lucasFibonacciSum r:R)) (hd : 5^k ∣ d) :
    (5:R)^k ∣ upperIndexForm x y d r := by
  obtain ⟨e,rfl⟩ := hd
  let z : FormPair R := ⟨x,y⟩
  have h := five_power_imaginary (z^e) k
  rw [←pow_mul,Nat.mul_comm] at h
  rw [form_pair_value,QuadraticAlgebra.im_mul]
  change (5:R)^k ∣ _*(z^(_*e)).im+(lucasFibonacciSum r:R)*(z^(_*e)).re+
    1*(lucasFibonacciSum r:R)*(z^(_*e)).im
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_left hu _))
    (dvd_mul_of_dvd_right h _)


private lemma absolute_form_second (r n : ℕ) :
    (upperIndexPolynomial r (n+1)).coeff n = (n+1:ℕ)*(lucasFibonacciSum (r+1):ℤ) := by
  induction n generalizing r with
  | zero => simp [upperIndexPolynomial,upperIndexForm]
  | succ n ih =>
    change (X*upperIndexPolynomial r (n+1)+1*upperIndexPolynomial (r+1) (n+1)).coeff (n+1)=_
    rw [one_mul,coeff_add,coeff_X_mul,ih,absolute_form_leading]
    push_cast
    ring

private lemma consecutive_upper_coprime (r : ℕ) :
    (lucasFibonacciSum r).Coprime (lucasFibonacciSum (r+1)) := by
  induction r with
  | zero => simp [lucas_fibonacci_sum_zero]
  | succ r ih =>
    rw [show r+1+1=r+2 by omega,lucas_fibonacci_sum_recurrence,Nat.coprime_self_add_right]
    exact ih.symm

/-- A nontrivial prime power divides every coefficient of the progression form exactly
when it is a power of five dividing both the step and the first upper value. -/
theorem upperIndexPolynomial_prime_power_content (r d : ℕ) (hd : 0<d) {p k : ℕ}
    (hp : p.Prime) (hk : 0<k) :
    ((p^k:ℕ):ℤ) ∣ (upperIndexPolynomial r d).content ↔
      p=5 ∧ p^k ∣ lucasFibonacciSum r ∧ p^k ∣ d := by
  let P := upperIndexPolynomial r d
  constructor
  · intro H
    have hall (i : ℕ) : ((p^k:ℕ):ℤ) ∣ P.coeff i := H.trans (content_dvd_coeff i)
    have hz : P.map (Int.castRingHom (ZMod p))=0 := by
      ext i
      rw [coeff_map,coeff_zero]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
      have hpp : (p:ℤ) ∣ ((p^k:ℕ):ℤ) := by exact_mod_cast dvd_pow_self p hk.ne'
      exact hpp.trans (hall i)
    have h5 : p=5 := by
      by_contra h
      exact distinct_roots_nonvanishing hp h r d hd hz
    have hu : p^k ∣ lucasFibonacciSum r := by
      have h := hall d
      rw [show P=upperIndexPolynomial r d from rfl,absolute_form_leading] at h
      exact_mod_cast h
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    have h' := hall n
    change ((p^k:ℕ):ℤ) ∣ (upperIndexPolynomial r (n+1)).coeff n at h'
    rw [absolute_form_second] at h'
    have hm : p^k ∣ (n+1)*lucasFibonacciSum (r+1) := by exact_mod_cast h'
    exact ⟨h5,hu,((consecutive_upper_coprime r).of_dvd_left hu).dvd_of_dvd_mul_right hm⟩
  · rintro ⟨rfl,hu,hdk⟩
    apply (dvd_content_iff_C_dvd).mpr
    have hc : (5:ℤ[X])^k ∣ (lucasFibonacciSum r:ℤ[X]) := by
      obtain ⟨n,hn⟩ := hu
      exact ⟨(n:ℤ[X]),by exact_mod_cast hn⟩
    simpa only [Nat.cast_pow,Nat.cast_ofNat,map_pow,show C (5:ℤ)=(5:ℤ[X]) from map_ofNat C 5,upperIndexPolynomial] using five_content_lower (X:ℤ[X]) 1 r d k hc hdk

/-- Distinct positive-step index forms have no common nonconstant rational factor. -/
theorem upperIndexPolynomial_coprime_iff (r d s e : ℕ) (hd : 0<d) (he : 0<e) :
    IsCoprime ((upperIndexPolynomial r d).map (Int.castRingHom ℚ))
      ((upperIndexPolynomial s e).map (Int.castRingHom ℚ)) ↔ (r,d) ≠ (s,e) := by
  have hr := upperIndexPolynomial_irreducible r d hd
  have hs := upperIndexPolynomial_irreducible s e he
  constructor
  · intro h hEq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hEq
    exact hr.not_isUnit (isCoprime_self.mp h)
  · intro hne
    apply hr.coprime_iff_not_dvd.mpr
    rintro ⟨w,hw⟩
    have hu := (hs.isUnit_or_isUnit hw).resolve_left hr.not_isUnit
    obtain ⟨c,hc,rfl⟩ := Polynomial.isUnit_iff.mp hu
    rw [mul_comm] at hw
    have hdeg := congrArg natDegree hw
    rw [natDegree_C_mul hc.ne_zero,natDegree_map_eq_of_injective Int.cast_injective,
      natDegree_map_eq_of_injective Int.cast_injective,absolute_form_degree,absolute_form_degree] at hdeg
    subst e
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    have hcoef (i : ℕ) := congrArg (fun P : ℚ[X] => P.coeff i) hw
    have h0 : (lucasFibonacciSum s:ℚ)=c*lucasFibonacciSum r := by
      simpa only [coeff_map,coeff_C_mul,absolute_form_leading,Int.coe_castRingHom,Int.cast_natCast]
        using hcoef (n+1)
    have h1 : (lucasFibonacciSum (s+1):ℚ)=c*lucasFibonacciSum (r+1) := by
      have h := hcoef n
      simp only [coeff_map,coeff_C_mul,absolute_form_second,Int.coe_castRingHom,Int.cast_mul,
        Int.cast_natCast] at h
      apply mul_left_cancel₀ (show ((n+1:ℕ):ℚ) ≠ 0 by positivity)
      linear_combination h
    have hx : lucasFibonacciSum s*lucasFibonacciSum (r+1)=
        lucasFibonacciSum r*lucasFibonacciSum (s+1) := by
      exact_mod_cast (show (lucasFibonacciSum s:ℚ)*lucasFibonacciSum (r+1)=
        lucasFibonacciSum r*lucasFibonacciSum (s+1) by rw [h0,h1]; ring)
    have hsr := (consecutive_upper_coprime s).dvd_of_dvd_mul_right
      (show lucasFibonacciSum s ∣ lucasFibonacciSum r*lucasFibonacciSum (s+1) from hx ▸ dvd_mul_right ..)
    have hrs := (consecutive_upper_coprime r).dvd_of_dvd_mul_right
      (show lucasFibonacciSum r ∣ lucasFibonacciSum s*lucasFibonacciSum (r+1) from hx ▸ dvd_mul_right ..)
    have hmono : StrictMono lucasFibonacciSum := fun _ _ h =>
      Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.fib_mono h.le)) (Nat.fib_add_two_strictMono h)
    exact hne (by rw [hmono.injective (Nat.dvd_antisymm hrs hsr)])

#print axioms upperIndexForm_fibonacci
#print axioms upperIndexPolynomial_irreducible
#print axioms upperIndexPolynomial_prime_power_content
#print axioms upperIndexPolynomial_coprime_iff

end Arxiv.«2211.10788»
