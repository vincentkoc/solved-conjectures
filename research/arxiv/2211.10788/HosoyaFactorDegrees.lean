import HosoyaFactorDegreeDescent
import Mathlib.FieldTheory.Finite.Extension

/-! # Frobenius degrees of factors of the upper Hosoya index forms -/

namespace Arxiv.«2211.10788»
open Polynomial
open scoped Polynomial

private def ratio {K : Type*} [Field K] (a b u v x : K) : K :=
  ((x+a)*(u+v*b))/((x+b)*(u+v*a))

private theorem ratio_inj {K : Type*} [Field K] {a b u v x y : K} (hab : a≠b)
    (hu : u+v*a≠0) (hv : u+v*b≠0) (hx : x+b≠0) (hy : y+b≠0) :
    ratio a b u v x = ratio a b u v y ↔ x=y := by
  refine ⟨fun h => ?_,fun h => h ▸ rfl⟩
  have he := (div_eq_div_iff (mul_ne_zero hx hu) (mul_ne_zero hy hu)).mp h
  have ht : (x-y)*(b-a)*(u+v*a)*(u+v*b)=0 := by linear_combination he
  exact sub_eq_zero.mp ((((mul_eq_zero.mp ht).resolve_right hv |> mul_eq_zero.mp).resolve_right hu
    |> mul_eq_zero.mp).resolve_right (sub_ne_zero.mpr hab.symm))

private theorem ratio_swap {K : Type*} [Field K] (a b u v x : K) :
    ratio b a u v x = (ratio a b u v x)⁻¹ := by simp [ratio]

private theorem frob_base {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]
    [CharP K p] (u : ZMod p) : frobenius K p (algebraMap (ZMod p) K u)=algebraMap (ZMod p) K u := by
  rw [frobenius_def,←map_pow,ZMod.pow_card]

/-- Frobenius exchanges the Fibonacci roots precisely at the two nonsplit residues modulo five. -/
theorem frobenius_fibonacci_root {p : ℕ} [Fact p.Prime] (h5 : p≠5) {K : Type*} [Field K]
    [Algebra (ZMod p) K] [CharP K p] {a b : K} (ha : a^2=a+1) (hb : b=1-a) :
    frobenius K p a = (if p%5=2 ∨ p%5=3 then b else a) := by
  let f := frobenius K p
  have hf : f a ^ 2=f a+1 := by simpa using congrArg f ha
  have split_root (c : K) (hc : c^2=c+1) : c=a ∨ c=b := by
    have hg : (c-a)*(c-b)=0 := by rw [hb]; linear_combination hc-ha
    simpa [sub_eq_zero] using mul_eq_zero.mp hg
  have hinj := (algebraMap (ZMod p) K).injective
  have crit := fibonacci_nonsplit_mod_five (Fact.out : p.Prime) h5
  split_ifs with hn
  · apply (split_root (f a) hf).resolve_left
    intro he
    have hmem := (Subfield.mem_bot_iff_pow_eq_self K p).mpr he
    obtain ⟨z,hz⟩ := (mem_bot_iff_intCast p K).mp hmem
    apply crit.mpr hn (z:ZMod p)
    apply hinj
    simpa [←hz,add_comm] using ha
  · have hex := crit.not.mpr hn
    push Not at hex
    obtain ⟨c,hc⟩ := hex
    let w := algebraMap (ZMod p) K c
    have hw : w^2=w+1 := by simpa [w,add_comm] using congrArg (algebraMap (ZMod p) K) hc
    have hfix : f w=w := frob_base c
    rcases split_root w hw with h|h
    · rwa [h] at hfix
    · rw [h,hb,map_sub,map_one] at hfix
      exact sub_right_injective hfix

private theorem frob_ratio_iterate {K : Type*} [Field K] {p ℓ : ℕ} [Fact p.Prime] [CharP K p]
    (swap : Bool) (hl : 0<ℓ) (a b u v x : K)
    (ha : frobenius K p a=if swap then b else a) (hb : frobenius K p b=if swap then a else b)
    (hu : frobenius K p u=u) (hv : frobenius K p v=v) (ht : ratio a b u v x ^ ℓ=1) (n : ℕ) :
    ratio a b u v (x^(p^n)) = ratio a b u v x ^ ((if swap then (ℓ-1)*p else p)^n) := by
  let w := ratio a b u v x
  have step (y : K) : ratio a b u v (y^p) =
      if swap then ((ratio a b u v y)^p)⁻¹ else (ratio a b u v y)^p := by
    have h : (ratio a b u v y)^p =
        ratio (frobenius K p a) (frobenius K p b) u v (y^p) := by
      change frobenius K p (ratio a b u v y) = _
      simp only [ratio,map_div₀,map_mul,map_add,hu,hv,frobenius_def]
    rw [ha,hb] at h
    cases swap <;> simp only [Bool.false_eq_true,if_false,if_true] at h ⊢
    · exact h.symm
    · exact (ratio_swap b a u v (y^p)).trans (congrArg Inv.inv h.symm)
  have hw : w≠0 := by
    change w^ℓ=1 at ht
    intro hz
    simp [hz,zero_pow hl.ne'] at ht
  have inv : w^(ℓ-1)=w⁻¹ := by
    apply (mul_left_inj' hw).mp
    rw [←pow_succ, Nat.sub_add_cancel hl, ht, inv_mul_cancel₀ hw]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ p n,pow_mul,step,ih]
    cases swap <;> simp only [Bool.false_eq_true,if_false,if_true]
    · rw [pow_succ, pow_mul]
    · change ((w^(((ℓ-1)*p)^n))^p)⁻¹=w^(((ℓ-1)*p)^(n+1))
      rw [←inv_pow,←inv_pow,←inv,←pow_mul,←pow_mul,pow_succ]
      congr 1; ring

/-- A marked fractional linear coordinate of finite order determines the
Frobenius degree of its point, without a restriction on that order. -/
theorem upper_ratio_frobenius_degree {p t : ℕ} [Fact p.Prime] (hp5 : p≠5)
    {K : Type*} [Field K] [Algebra (ZMod p) K] [CharP K p] {a b x : K}
    (ha : a^2=a+1) (hba : b=1-a) (hab : a≠b) (u v : ZMod p)
    {g : (ZMod p)[X]} (hg : Irreducible g) (hx : g.aeval x=0)
    (hUa : algebraMap (ZMod p) K u+algebraMap (ZMod p) K v*a≠0)
    (hUb : algebraMap (ZMod p) K u+algebraMap (ZMod p) K v*b≠0) (hxb : x+b≠0)
    (ht : 0<t) (hord : orderOf (((x+a)*(algebraMap (ZMod p) K u+algebraMap (ZMod p) K v*b)) /
      ((x+b)*(algebraMap (ZMod p) K u+algebraMap (ZMod p) K v*a)))=t)
    (hw : (x+a)≠0) :
    g.natDegree=orderOf (if p%5=2 ∨ p%5=3 then -(p:ZMod t) else (p:ZMod t)) := by
  let incl := algebraMap (ZMod p) K
  let w := ratio a b (incl u) (incl v) x
  change orderOf w=t at hord
  have hwl : w^t=1 := by rw [←hord,pow_orderOf_eq_one]
  have hnon : w≠0 := div_ne_zero (mul_ne_zero hw hUb) (mul_ne_zero hxb hUa)
  let W := Units.mk0 w hnon
  have ho : orderOf W=t := by rw [←orderOf_units]; exact hord
  let sw := decide (p%5=2 ∨ p%5=3)
  let M := if sw then (t-1)*p else p
  have hfa : frobenius K p a=if sw then b else a := by simpa [sw] using frobenius_fibonacci_root hp5 ha hba
  have hfb : frobenius K p b=if sw then a else b := by
    rw [hba,map_sub,map_one,hfa,hba]; cases sw <;> simp
  have hM : (M:ZMod t)=(if p%5=2 ∨ p%5=3 then -(p:ZMod t) else (p:ZMod t)) := by
    by_cases hn : p%5=2 ∨ p%5=3 <;> simp [M,sw,hn,Nat.cast_sub ht]
  rw [←hM]
  have fixed_iff (n : ℕ) : g.natDegree ∣ n ↔ orderOf (M:ZMod t) ∣ n := by
    have orbit := frob_ratio_iterate sw ht a b (incl u) (incl v) x hfa hfb
      (frob_base u) (frob_base v) hwl n
    change ratio a b (incl u) (incl v) (x^(p^n))=w^(M^n) at orbit
    have hxb' : x^(p^n)+b≠0 := by
      intro he
      exact (pow_ne_zero (M^n) hnon) (by simpa [ratio,he] using orbit.symm)
    calc
      g.natDegree ∣ n ↔ x^(p^n)=x := by
        rw [hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X,←hg.dvd_iff_aeval_eq_zero hx]
        simp [Nat.card_eq_fintype_card,sub_eq_zero]
      _ ↔ w^(M^n)=w := by rw [←orbit]; exact (ratio_inj hab hUa hUb hxb' hxb).symm
      _ ↔ M^n ≡ 1 [MOD t] := by
        change (W^(M^n):Kˣ).val=W.val ↔ _
        have we : W^(M^n)=W^1 ↔ M^n ≡ 1 [MOD t] := by rw [pow_eq_pow_iff_modEq,ho]
        simpa only [pow_one,Units.ext_iff] using we
      _ ↔ orderOf (M:ZMod t) ∣ n := by
        rw [orderOf_dvd_iff_pow_eq_one,←ZMod.natCast_eq_natCast_iff,Nat.cast_pow,Nat.cast_one]
  exact Nat.dvd_antisymm ((fixed_iff _).mpr dvd_rfl) ((fixed_iff _).mp dvd_rfl)

/-- After choosing one projective zero, every irreducible factor away from it
has degree equal to the order of the signed residue of the characteristic.
The chosen zero may be the point at infinity. -/
theorem upperIndexPolynomial_factor_degree {p ℓ r : ℕ} [Fact p.Prime]
    (hp5 : p≠5) (hp11 : p≠11) (hl : ℓ.Prime) (z : Option (ZMod p))
    (hpiv : upperIndexForm (upperIndexChart z).1 (upperIndexChart z).2 ℓ r=0)
    {g : (ZMod p)[X]} (hg : Irreducible g) (haway : ∀ y, z=some y → g.eval y≠0)
    (hdiv : g ∣ (upperIndexPolynomial r ℓ).map (Int.castRingHom (ZMod p))) :
    g.natDegree = orderOf (if p%5=2 ∨ p%5=3 then -(p:ZMod ℓ) else (p:ZMod ℓ)) := by
  classical
  let F := ZMod p
  let K := AlgebraicClosure F
  let incl := algebraMap F K
  let : Fact ℓ.Prime := ⟨hl⟩
  have nz (n : ℕ) (hn : n.Prime) (hne : p≠n) : (n:K)≠0 := fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq Fact.out hn).mp ((CharP.cast_eq_zero_iff K p n).mp h))
  obtain ⟨a,b,ha,hb,hba,hab,hA,hB⟩ := upperIndexForm_conjugate_data K
    (nz 5 (by decide) hp5) (nz 11 (by decide) hp11) r
  let A := (3+a)*a^r
  let B := (3+b)*b^r
  change A≠0 at hA
  change B≠0 at hB
  have powers {s t : K} (h : upperIndexForm s t ℓ r=0) :
      A*(s+t*a)^ℓ=B*(s+t*b)^ℓ := by
    have he := upper_form_conjugates ha hb s t r ℓ
    rw [h,mul_zero] at he
    exact sub_eq_zero.mp (by simpa only [mul_comm a t,mul_comm b t] using he.symm)
  let u := (upperIndexChart z).1
  let v := (upperIndexChart z).2
  change upperIndexForm u v ℓ r=0 at hpiv
  have hUV := powers (by rw [←upperIndexForm_map incl, hpiv, map_zero] : upperIndexForm (incl u) (incl v) ℓ r=0)
  have hnon (c e : K) (h : A*c^ℓ=B*e^ℓ) (hn : ¬(c=0 ∧ e=0)) : c≠0 ∧ e≠0 := by
    constructor
    · intro hc
      apply hn ⟨hc,?_⟩
      exact (pow_eq_zero_iff hl.ne_zero).mp ((mul_eq_zero.mp (by simpa [hc,zero_pow hl.ne_zero] using h.symm)).resolve_left hB)
    · intro he
      apply hn ⟨?_,he⟩
      exact (pow_eq_zero_iff hl.ne_zero).mp ((mul_eq_zero.mp (by simpa [he,zero_pow hl.ne_zero] using h)).resolve_left hA)
  obtain ⟨hUa,hUb⟩ := hnon _ _ hUV (by
    cases z with
    | none => simp [u,v,upperIndexChart]
    | some z =>
      simp only [u,v,upperIndexChart,map_one,one_mul]
      rintro ⟨ha',hb'⟩
      exact hab (add_left_cancel (ha'.trans hb'.symm)))
  have hgpos : 0 < (g.map incl).degree := by
    rw [degree_eq_natDegree (map_ne_zero hg.ne_zero),natDegree_map]
    exact_mod_cast hg.natDegree_pos
  obtain ⟨x,hx₀⟩ := IsAlgClosed.exists_root (g.map incl) hgpos.ne'
  have hx : g.aeval x=0 := by simpa [IsRoot,incl,eval_map_algebraMap] using hx₀
  have hform := ((hg.dvd_iff_aeval_eq_zero hx).mpr hdiv)
  rw [upperIndexPolynomial_aeval] at hform
  have hX := powers hform
  simp only [one_mul] at hX
  obtain ⟨hxa,hxb⟩ := hnon _ _ hX (by rintro ⟨h₁,h₂⟩; exact hab (add_left_cancel (h₁.trans h₂.symm)))
  let w := ratio a b (incl u) (incl v) x
  have hw : w≠0 := div_ne_zero (mul_ne_zero hxa hUb) (mul_ne_zero hxb hUa)
  have hwl : w^ℓ=1 := by
    rw [show w=((x+a)*(incl u+incl v*b))/((x+b)*(incl u+incl v*a)) from rfl, div_pow,
      div_eq_one_iff_eq (pow_ne_zero _ (mul_ne_zero hxb hUa)),mul_pow,mul_pow]
    apply mul_left_cancel₀ hA
    linear_combination (incl u+incl v*b)^ℓ * hX - (x+b)^ℓ * hUV
  have hwo : w≠1 := by
    intro he
    have h := (div_eq_one_iff_eq (mul_ne_zero hxb hUa)).mp he
    have h' : (a-b)*(incl u - incl v*x)=0 := by linear_combination h
    have eq := sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hab))
    have hv : v≠0 := by intro hv; rw [hv,map_zero,zero_mul] at eq hUa; simp [eq] at hUa
    have hx' : incl (u/v)=x := by
      rw [map_div₀,div_eq_iff (by simpa only [map_zero] using incl.injective.ne hv : incl v≠0)]
      simpa [mul_comm] using eq
    have heval : incl (g.eval (u/v))=0 := by rw [← aeval_algebraMap_apply_eq_algebraMap_eval, hx']; exact hx
    have hmatch : z=some (u/v) := by
      cases z with
      | none => simp [v,upperIndexChart] at hv
      | some y => simp [u,v,upperIndexChart]
    exact haway _ hmatch (incl.injective (heval.trans incl.map_zero.symm))
  let W := Units.mk0 w hw
  have hord : orderOf W=ℓ := orderOf_eq_prime (by apply Units.ext; exact hwl) (fun h => hwo (congrArg Units.val h))
  exact upper_ratio_frobenius_degree hp5 ha hba hab u v hg hx hUa hUb hxb hl.pos
    (orderOf_units.trans hord : orderOf (W:K)=ℓ) hxa

/-- With a projective zero, the degrees of all nonlinear factors agree. -/
theorem upperIndexPolynomial_nonlinear_factor_degree {p ℓ r : ℕ} [Fact p.Prime]
    (hp5 : p≠5) (hp11 : p≠11) (hl : ℓ.Prime) (hcount : 0 < upperProjectiveRootCount p r ℓ)
    {g : (ZMod p)[X]} (hg : Irreducible g) (hdeg : 1 < g.natDegree)
    (hdiv : g ∣ (upperIndexPolynomial r ℓ).map (Int.castRingHom (ZMod p))) :
    g.natDegree = orderOf (if p%5=2 ∨ p%5=3 then -(p:ZMod ℓ) else (p:ZMod ℓ)) := by
  obtain ⟨z,hz⟩ := Finset.card_pos.mp hcount
  exact upperIndexPolynomial_factor_degree hp5 hp11 hl z (Finset.mem_filter.mp hz).2 hg
    (fun y _ => hg.not_isRoot_of_natDegree_ne_one (by omega)) hdiv

private theorem index_derivative (r d : ℕ) :
    (upperIndexPolynomial r (d+1)).derivative = (d+1:ℕ)*upperIndexPolynomial r d := by
  have recurrence (r d : ℕ) : upperIndexPolynomial r (d+1) = X*upperIndexPolynomial r d +
      upperIndexPolynomial (r+1) d := by simp [upperIndexPolynomial,upperIndexForm]
  induction d generalizing r with
  | zero => simp [upperIndexPolynomial,upperIndexForm]
  | succ n ih =>
    rw [recurrence r (n+1),derivative_add,derivative_mul,derivative_X,one_mul,ih,ih,recurrence r n]
    push_cast
    ring

/-- Away from the two bad characteristics and the divisors of the step,
every affine root is simple, including when the form has a zero at infinity. -/
theorem upperIndexPolynomial_separable {F : Type*} [Field F] (h5 : (5:F)≠0) (h11 : (11:F)≠0)
    (r d : ℕ) (hd : ((d+1:ℕ):F)≠0) :
    ((upperIndexPolynomial r (d+1)).map (Int.castRingHom F)).Separable := by
  let K := AlgebraicClosure F
  let incl := algebraMap F K
  have lift {n : ℕ} (h : (n:F)≠0) : (n:K)≠0 := fun he => h (incl.injective (by simpa [incl] using he))
  obtain ⟨a,b,ha,hb,_,hab,hA,hB⟩ := upperIndexForm_conjugate_data K (lift h5) (lift h11) r
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K _ _).mpr
  intro x
  rw [upperIndexPolynomial_aeval,derivative_map,index_derivative,Polynomial.map_mul,map_mul,
    upperIndexPolynomial_aeval]
  apply or_iff_not_imp_left.mpr
  intro hz
  push Not at hz
  apply mul_ne_zero (by simpa using lift hd)
  intro hz'
  have eqn (n : ℕ) (he : upperIndexForm x 1 n r=0) :
      ((3+a)*a^r)*(x+a)^n=((3+b)*b^r)*(x+b)^n := by
    have hh := upper_form_conjugates ha hb x 1 r n
    rw [he,mul_zero] at hh
    exact sub_eq_zero.mp (by simpa only [mul_one] using hh.symm)
  have h₁ := eqn _ hz
  have h₀ := eqn _ hz'
  have hxa : x+a≠0 := by
    intro hx
    have hxb : x+b≠0 := fun he => hab (add_left_cancel (hx.trans he.symm))
    rw [hx,zero_pow (by omega : d+1≠0),mul_zero] at h₁
    exact mul_ne_zero hB (pow_ne_zero _ hxb) h₁.symm
  have hbad : ((3+a)*a^r)*(x+a)^d*(a-b)=0 := by
    rw [pow_succ,pow_succ] at h₁
    linear_combination h₁ - (x+b)*h₀
  exact mul_ne_zero (mul_ne_zero hA (pow_ne_zero _ hxa)) (sub_ne_zero.mpr hab) hbad

/-- If the leading coefficient vanishes in characteristic different from the
prime step, the affine degree drops by exactly one. -/
theorem upperIndexPolynomial_degree_at_infinity {p ℓ r : ℕ} [Fact p.Prime] (hl : ℓ.Prime)
    (hne : p≠ℓ) (hu : p ∣ lucasFibonacciSum r) :
    ((upperIndexPolynomial r ℓ).map (Int.castRingHom (ZMod p))).natDegree=ℓ-1 := by
  let P := (upperIndexPolynomial r ℓ).map (Int.castRingHom (ZMod p))
  have hq : ¬p ∣ lucasFibonacciSum (r+1) := fun hd => (Fact.out : p.Prime).not_dvd_one
    (by simpa [(upperIndex_consecutive_coprime r).gcd_eq_one] using Nat.dvd_gcd hu hd)
  have hl' := (ZMod.natCast_eq_zero_iff ..).not.mpr ((Nat.prime_dvd_prime_iff_eq Fact.out hl).not.mpr hne)
  have hq' := (ZMod.natCast_eq_zero_iff ..).not.mpr hq
  have top : P.coeff ℓ=0 := by simpa [P,coeff_map,upperIndexPolynomial_top_coeff] using (ZMod.natCast_eq_zero_iff ..).mpr hu
  have sub : P.coeff (ℓ-1)≠0 := by
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne_zero
    simpa [P,hn,coeff_map,upperIndexPolynomial_next_coeff] using mul_ne_zero hl' hq'
  have hpos : P≠0 := by intro he; rw [he,coeff_zero] at sub; contradiction
  have hle : P.natDegree ≤ ℓ := natDegree_map_le.trans (upperIndexPolynomial_natDegree r ℓ).le
  have hne' : P.natDegree≠ℓ := fun he => leadingCoeff_ne_zero.mpr hpos
    (by rwa [leadingCoeff,he])
  change P.natDegree=ℓ-1
  have := le_natDegree_of_ne_zero sub
  omega

/-- If the only distinguished root is chosen at infinity, the affine
polynomial is irreducible exactly when the signed residue has full order. -/
theorem upperIndexPolynomial_irreducible_at_infinity {p ℓ r : ℕ} [Fact p.Prime]
    (hp5 : p≠5) (hp11 : p≠11) (hl : ℓ.Prime) (hne : p≠ℓ) (hu : p ∣ lucasFibonacciSum r) :
    Irreducible ((upperIndexPolynomial r ℓ).map (Int.castRingHom (ZMod p))) ↔
      orderOf (if p%5=2 ∨ p%5=3 then -(p:ZMod ℓ) else (p:ZMod ℓ))=ℓ-1 := by
  let P := (upperIndexPolynomial r ℓ).map (Int.castRingHom (ZMod p))
  let m := orderOf (if p%5=2 ∨ p%5=3 then -(p:ZMod ℓ) else (p:ZMod ℓ))
  have hd : P.natDegree=ℓ-1 := upperIndexPolynomial_degree_at_infinity hl hne hu
  have factor {g : (ZMod p)[X]} (hg : Irreducible g) (hdiv : g ∣ P) : g.natDegree=m :=
    upperIndexPolynomial_factor_degree hp5 hp11 hl none (by simpa [upperIndexChart,upperIndexForm_at_infinity,ZMod.natCast_eq_zero_iff] using hu)
      hg (by simp) hdiv
  refine ⟨fun h => (factor h dvd_rfl).symm.trans hd,fun he => ?_⟩
  have hpos : 0 < P.natDegree := by rw [hd]; have := hl.one_lt; omega
  have hnu : ¬IsUnit P := fun h => hpos.ne' (natDegree_eq_zero_of_isUnit h)
  obtain ⟨g,hg,hdiv⟩ := WfDvdMonoid.exists_irreducible_factor hnu (by intro h; simp [h] at hpos)
  have heq : g.natDegree=P.natDegree := (factor hg hdiv).trans (he.trans hd.symm)
  exact ((associated_of_dvd_of_natDegree_le hdiv (by intro h; simp [h] at hpos) heq.ge).irreducible_iff).mp hg

private theorem step_characteristic_reducible {p : ℕ} [Fact p.Prime] (r : ℕ) :
    ¬Irreducible ((upperIndexPolynomial r p).map (Int.castRingHom (ZMod p))) := by
  intro h
  apply (separable_iff_derivative_ne_zero h).mp (PerfectField.separable_of_irreducible h)
  have hz : (p:(ZMod p)[X])=0 := CharP.cast_eq_zero _ _
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fact.out : p.Prime).ne_zero
  have der : (upperIndexPolynomial r p).derivative=(p:ℤ[X])*upperIndexPolynomial r n := by
    simpa only [hn] using index_derivative r n
  rw [derivative_map,der,Polynomial.map_mul,Polynomial.map_natCast,hz,zero_mul]

/-- Complete irreducibility test for affine index polynomials of prime step,
including a vanishing leading coefficient, the two exceptional primes,
and characteristic equal to the step. -/
theorem upperIndexPolynomial_irreducible_mod_prime_iff {p ℓ r : ℕ} [Fact p.Prime] (hl : ℓ.Prime) :
    Irreducible ((upperIndexPolynomial r ℓ).map (Int.castRingHom (ZMod p))) ↔
      if p ∣ lucasFibonacciSum r then p≠ℓ ∧
        (if p=5 then ℓ=2 else
          orderOf (if p%5=2 ∨ p%5=3 then -(p:ZMod ℓ) else (p:ZMod ℓ))=ℓ-1)
      else upperProjectiveRootCount p r ℓ=0 := by
  by_cases hU : p ∣ lucasFibonacciSum r
  swap
  · rw [if_neg hU]; exact upperIndexPolynomial_irreducible_iff_count_zero hl hU
  rw [if_pos hU]
  by_cases hp5 : p=5
  · rw [if_pos hp5]
    subst p
    by_cases h5 : 5=ℓ
    · subst ℓ
      simp [step_characteristic_reducible r]
    rw [and_iff_right h5]
    have hd := upperIndexPolynomial_degree_at_infinity hl h5 hU
    constructor
    · intro hi
      by_contra h2
      have hdeg : ((upperIndexPolynomial r ℓ).map (Int.castRingHom (ZMod 5))).natDegree≠1 := by
        rw [hd]; have := hl.one_lt; omega
      apply hi.not_isRoot_of_natDegree_ne_one hdeg (x:= -3)
      change Polynomial.eval _ _=0
      have ev := upperIndexPolynomial_aeval (F:=ZMod 5) r ℓ (-3:ZMod 5)
      rw [aeval_def,Algebra.algebraMap_self,eval₂_id] at ev
      rw [ev]
      obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne_zero
      rw [upperIndexForm_mod_five]
      have hn : n≠0 := by have := hl.one_lt; omega
      simp [hn]
    · rintro rfl
      apply irreducible_of_degree_eq_one
      exact (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 1)).mpr hd
  · rw [if_neg hp5]
    by_cases he : p=ℓ
    · subst ℓ
      simp [step_characteristic_reducible r]
    have hp11 : p≠11 := by
      intro eq
      subst p
      have hx := upperIndexForm_mod_eleven (1:ZMod 11) 0 r 0
      have h4 : (4:ZMod 11)≠0 := (ZMod.natCast_eq_zero_iff 4 11).not.mpr (by decide)
      exact (pow_ne_zero r h4) (by
        simpa [upperIndexForm,(ZMod.natCast_eq_zero_iff ..).mpr hU] using hx.symm)
    exact (upperIndexPolynomial_irreducible_at_infinity hp5 hp11 hl he hU).trans
      (and_iff_right he).symm

/-- The lower affine degree at a zero leading coefficient can still be irreducible. -/
example : Irreducible ((upperIndexPolynomial 1 5).map (Int.castRingHom (ZMod 2))) := by
  apply (upperIndexPolynomial_irreducible_mod_prime_iff (by decide : Nat.Prime 5)).mpr
  simp only [lucas_fibonacci_sum_one,show 2 ∣ 4 by decide,if_true,
    show (2:ℕ)≠5 by decide,if_false,show 2%5=2 by decide,true_or]
  refine ⟨by decide,?_⟩
  apply (orderOf_eq_iff (by decide : 0 < 5-1)).mpr
  constructor
  · decide
  · intro i hi hi'
    interval_cases i <;> decide

/-- At offset zero the septic has no projective root at 29. -/
example : Irreducible ((upperIndexPolynomial 0 7).map (Int.castRingHom (ZMod 29))) := by
  let : Fact (Nat.Prime 29) := ⟨by decide⟩
  apply (upperIndexPolynomial_irreducible_iff_count_zero (by decide : Nat.Prime 7)
    (by simp [lucas_fibonacci_sum_zero])).mpr
  rw [upperProjectiveRootCount_ordinary (by decide) (by decide) 0 7 (by decide)]
  decide

#print axioms upperIndexPolynomial_irreducible_mod_prime_iff

#print axioms upperIndexPolynomial_separable
#print axioms upperIndexPolynomial_degree_at_infinity
#print axioms upperIndexPolynomial_irreducible_at_infinity

#print axioms frobenius_fibonacci_root
#print axioms upper_ratio_frobenius_degree
#print axioms upperIndexPolynomial_factor_degree

#print axioms upperIndexPolynomial_nonlinear_factor_degree

end Arxiv.«2211.10788»
