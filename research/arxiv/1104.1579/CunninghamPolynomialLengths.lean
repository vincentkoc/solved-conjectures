import Mathlib
import FormalConjectures.Arxiv.«1104.1579».CunninghamChain

/-!
# Exact lengths of polynomial Cunningham chains

Jones uses the recurrence `f ↦ Xf ± 1` in integer polynomials and tests
irreducibility in rational polynomials.
-/

namespace CunninghamChain
open Polynomial

/-- At index zero the seed is the first polynomial in Jones's chain. -/
noncomputable def polynomialTerm (b : Bool) (f : ℤ[X]) : ℕ → ℤ[X]
  | 0 => f
  | i+1 => X * polynomialTerm b f i + C (if b then 1 else -1)

/-- The polynomial analogue of Jones's integer predicates. -/
def IsPolynomialChainOfLength (b : Bool) (f : ℤ[X]) (k : ℕ) : Prop :=
  0 < k ∧ 0 < f.leadingCoeff ∧
    (∀ i < k, Irreducible ((polynomialTerm b f i).map (Int.castRingHom ℚ))) ∧
    ¬ Irreducible ((polynomialTerm b f k).map (Int.castRingHom ℚ))

private lemma root_prod_small {s : Multiset ℂ} (hne : s ≠ 0)
    (h : ∀ z ∈ s, ‖z‖ < 1) : ‖s.prod‖ < 1 := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons z s ih =>
    have hz := h z (Multiset.mem_cons_self ..)
    have ht : ‖s.prod‖ ≤ 1 := by
      by_cases he : s = 0
      · simp [he]
      · exact (ih he (fun w hw => h w (Multiset.mem_cons_of_mem hw))).le
    rw [Multiset.prod_cons,norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ht) hz

/-- An integral polynomial of positive degree with leading coefficient ±1 and
nonzero constant term has a complex root on or outside the unit circle. -/
private lemma outer_root (f : ℤ[X]) (hd : 0 < f.natDegree)
    (h₀ : f.coeff 0 ≠ 0) (hu : IsUnit f.leadingCoeff) :
    ∃ z : ℂ, (f.map (Int.castRingHom ℂ)).IsRoot z ∧ 1 ≤ ‖z‖ := by
  classical
  let g := f.map (Int.castRingHom ℂ)
  have hg : g.natDegree = f.natDegree := natDegree_map_eq_of_injective (Int.cast_injective) _
  have hn : g.roots ≠ 0 := by
    intro he
    have hc := (IsAlgClosed.splits g).natDegree_eq_card_roots
    rw [he,Multiset.card_zero,hg] at hc
    omega
  by_contra! h
  have hs := root_prod_small hn (fun z hz => h z (isRoot_of_mem_roots hz))
  have hc := congrArg (fun z : ℂ => ‖z‖)
    (IsAlgClosed.splits g).coeff_zero_eq_leadingCoeff_mul_prod_roots
  have hu' : ‖g.leadingCoeff‖ = 1 := by
    change ‖(f.map _).leadingCoeff‖ = 1
    rw [leadingCoeff_map_of_injective Int.cast_injective]
    rcases Int.isUnit_iff.mp hu with e|e <;> simp [e]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,hu'] at hc
  have hconst : 1 ≤ ‖g.coeff 0‖ := by
    change 1 ≤ ‖(f.map _).coeff 0‖
    rw [coeff_map]
    change 1 ≤ ‖(f.coeff 0 : ℂ)‖
    rw [Complex.norm_intCast,← Int.cast_abs]
    exact_mod_cast (show (1 : ℤ) ≤ |f.coeff 0| by have hp := abs_pos.mpr h₀; omega)
  linarith

/-- A prime leading coefficient precludes a factorization if all complex
roots are strictly inside the unit disk and the constant term is a unit. -/
private lemma irreducible_of_prime_leading_inside (f : ℤ[X]) (hd : 0 < f.natDegree)
    (hu : IsUnit (f.coeff 0)) (hp : Irreducible f.leadingCoeff)
    (hroot : ∀ z : ℂ, (f.map (Int.castRingHom ℂ)).IsRoot z → ‖z‖ < 1) :
    Irreducible (f.map (Int.castRingHom ℚ)) := by
  have hprim : f.IsPrimitive := isPrimitive_iff_isUnit_of_C_dvd.mpr fun r h =>
    isUnit_of_dvd_unit ((C_dvd_iff_dvd_coeff _ _).mp h 0) hu
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
  refine ⟨fun h => by have := natDegree_eq_zero_of_isUnit h; omega, ?_⟩
  have factor (a b : ℤ[X]) (hab : f = a*b) (ha : IsUnit a.leadingCoeff) : IsUnit a := by
    have h0 : IsUnit (a.coeff 0) := by
      have hu' := hu
      rw [hab,Polynomial.mul_coeff_zero] at hu'
      exact isUnit_of_mul_isUnit_left hu'
    by_cases hdeg : a.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hdeg]
      exact isUnit_C.mpr h0
    obtain ⟨z,hz,hle⟩ := outer_root a (Nat.pos_of_ne_zero hdeg) h0.ne_zero ha
    have hfr : (f.map (Int.castRingHom ℂ)).IsRoot z := by
      rw [hab,Polynomial.map_mul]
      change _ = 0
      rw [eval_mul,show eval z (a.map (Int.castRingHom ℂ)) = 0 from hz,zero_mul]
    exact False.elim ((hroot z hfr).not_ge hle)
  intro a b hab
  have hl := congrArg leadingCoeff hab
  rw [leadingCoeff_mul] at hl
  rcases hp.isUnit_or_isUnit hl with ha|hb
  · exact Or.inl (factor a b hab ha)
  · exact Or.inr (factor b a (hab.trans (mul_comm _ _)) hb)

/-- If every coefficient below the leading one is nonpositive, evaluation at
one already bounds the contributions of all lower powers outside the disk. -/
private lemma inside_of_nonpositive_coeffs (g : ℝ[X]) (hm : 0 < g.leadingCoeff)
    (hcoeff : ∀ i < g.natDegree, g.coeff i ≤ 0) (hpos : 0 < g.eval 1)
    (z : ℂ) (hz : (g.map (algebraMap ℝ ℂ)).IsRoot z) : ‖z‖ < 1 := by
  classical
  by_contra! hge
  let I := Finset.range g.natDegree
  have hmass : (∑ i ∈ I, -g.coeff i) < g.leadingCoeff := by
    rw [eval_eq_sum_range,Finset.sum_range_succ] at hpos
    simp only [one_pow,mul_one] at hpos
    rw [Finset.sum_neg_distrib]
    change -(∑ i ∈ Finset.range g.natDegree, g.coeff i) < g.coeff g.natDegree
    linarith only [hpos]
  have hdeg : (g.map (algebraMap ℝ ℂ)).natDegree = g.natDegree :=
    natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective _
  change _ = 0 at hz
  rw [eval_eq_sum_range,hdeg,Finset.sum_range_succ] at hz
  simp only [coeff_map] at hz
  have he : (g.leadingCoeff : ℂ) * z ^ g.natDegree =
      -(∑ i ∈ I, (g.coeff i : ℂ) * z^i) := by
    change _ = -(∑ i ∈ Finset.range g.natDegree, _)
    exact eq_neg_of_add_eq_zero_right hz
  have hn := congrArg norm he
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hm,norm_neg] at hn
  have bound : ‖∑ i ∈ I, (g.coeff i : ℂ)*z^i‖ ≤
      (∑ i ∈ I, -g.coeff i)*‖z‖^g.natDegree := by
    refine (norm_sum_le ..).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hlt := Finset.mem_range.mp hi
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (hcoeff i hlt)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hge hlt.le) (neg_nonneg.mpr (hcoeff i hlt))
  have hp : 0 < ‖z‖^g.natDegree := pow_pos (by linarith) _
  exact (mul_lt_mul_of_pos_right hmass hp).not_ge (hn.trans_le bound)

/-- Removing a real root greater than one from a monic polynomial with
nonnegative coefficients below its subleading term leaves all roots inside
the unit circle, provided its value at one is negative. -/
private lemma one_outer_factor (f : ℝ[X]) (hm : f.Monic) (hd : 1 < f.natDegree)
    (hc : ∀ i, i+1 < f.natDegree → 0 ≤ f.coeff i) (hval : f.eval 1 < 0) :
    ∃ (r : ℝ) (q : ℝ[X]), 1 < r ∧ f = (X-C r)*q ∧
      ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ < 1 := by
  have ht := f.tendsto_atTop_of_leadingCoeff_nonneg
    (natDegree_pos_iff_degree_pos.mp (by omega)) (by rw [hm.leadingCoeff]; norm_num)
  obtain ⟨b,hb,hb'⟩ := ((Filter.eventually_gt_atTop (1 : ℝ)).and (ht.eventually_gt_atTop 0)).exists
  obtain ⟨r,hr,hr'⟩ := intermediate_value_Ioo hb.le f.continuous.continuousOn ⟨hval,hb'⟩
  obtain ⟨q,hq⟩ := dvd_iff_isRoot.mpr (show f.IsRoot r from hr')
  have hqm := (monic_X_sub_C r).of_mul_monic_left (hq ▸ hm)
  have hdq : f.natDegree = 1 + q.natDegree := by
    rw [hq,natDegree_mul (X_sub_C_ne_zero r) hqm.ne_zero,natDegree_X_sub_C]
  refine ⟨r,q,hr.1,hq,inside_of_nonpositive_coeffs q (by rw [hqm.leadingCoeff]; norm_num) ?_ ?_⟩
  · intro i hi
    induction i with
    | zero =>
      have h := hc 0 (by omega)
      rw [hq,mul_coeff_zero,coeff_sub] at h
      simp at h
      nlinarith [hr.1]
    | succ i ih =>
      have h := hc (i+1) (by omega)
      rw [hq,coeff_X_sub_C_mul] at h
      have := ih (by omega)
      nlinarith [hr.1]
  · rw [hq,eval_mul,eval_sub,eval_X,eval_C] at hval
    nlinarith [hr.1]

private lemma irreducible_of_one_outer_factor (f : ℤ[X]) (hm : f.Monic) (hd : 1 < f.natDegree)
    (hc : ∀ i, i+1 < f.natDegree → 0 ≤ f.coeff i) (hconst : f.coeff 0 ≠ 0)
    (hval : f.eval 1 < 0) : Irreducible (f.map (Int.castRingHom ℚ)) := by
  classical
  let F := f.map (Int.castRingHom ℝ)
  have hdeg : F.natDegree = f.natDegree := natDegree_map_eq_of_injective Int.cast_injective _
  have hc' (i : ℕ) (hi : i+1 < F.natDegree) : 0 ≤ F.coeff i := by
    rw [hdeg] at hi
    simpa [F] using (show (0 : ℝ) ≤ (f.coeff i : ℝ) by exact_mod_cast hc i hi)
  have hv : F.eval 1 < 0 := by
    change (f.map (Int.castRingHom ℝ)).eval 1 < 0
    rw [←map_one (Int.castRingHom ℝ),eval_map_apply]
    change ((f.eval 1 : ℤ) : ℝ) < 0
    exact_mod_cast hval
  obtain ⟨r,q,_,hq,hinside⟩ := one_outer_factor F (hm.map _) (by omega) hc' hv
  let c := Int.castRingHom ℂ
  let R := algebraMap ℝ ℂ
  have hq' : f.map c = (X-C (r:ℂ)) * q.map R := by
    have h := congrArg (Polynomial.map R) hq
    have he : R.comp (Int.castRingHom ℝ) = c := Subsingleton.elim _ _
    change f.map c = (X-C (R r)) * q.map R
    simpa only [F,Polynomial.map_map,he,Polynomial.map_mul,Polynomial.map_sub,map_X,map_C] using h
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).mp
  refine ⟨fun h => by have := natDegree_eq_zero_of_isUnit h; omega, ?_⟩
  intro a b hab
  have hlead : IsUnit (a.leadingCoeff*b.leadingCoeff) := by
    rw [← leadingCoeff_mul,←hab,hm.leadingCoeff]; exact isUnit_one
  have factor (g : ℤ[X]) (hl : IsUnit g.leadingCoeff) (h0 : g.coeff 0 ≠ 0)
      (hdiv : g.map c ∣ q.map R) : IsUnit g := by
    by_cases hdg : g.natDegree = 0
    · have e : g.leadingCoeff = g.coeff 0 := by simp [leadingCoeff,hdg]
      rw [eq_C_of_natDegree_eq_zero hdg]
      exact isUnit_C.mpr (e ▸ hl)
    obtain ⟨z,hz,hge⟩ := outer_root g (Nat.pos_of_ne_zero hdg) h0 hl
    exact False.elim ((hinside z (dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hz).trans hdiv))).not_ge hge)
  have hprod : a.map c * b.map c = (X-C (r:ℂ)) * q.map R := by
    rw [←Polynomial.map_mul,←hab,hq']
  have hdiv : X-C (r:ℂ) ∣ a.map c * b.map c := ⟨_,hprod⟩
  have hzero : a.coeff 0 * b.coeff 0 ≠ 0 := by rwa [←mul_coeff_zero,←hab]
  rcases (prime_X_sub_C (r:ℂ)).dvd_or_dvd hdiv with ⟨g,hg⟩|⟨g,hg⟩
  · right
    apply factor b (isUnit_of_mul_isUnit_right hlead) (right_ne_zero_of_mul hzero)
    rw [hg,mul_assoc] at hprod
    rw [←mul_left_cancel₀ (X_sub_C_ne_zero _) hprod]
    exact dvd_mul_left _ _
  · left
    apply factor a (isUnit_of_mul_isUnit_left hlead) (left_ne_zero_of_mul hzero)
    rw [hg,mul_left_comm] at hprod
    rw [←mul_left_cancel₀ (X_sub_C_ne_zero _) hprod]
    exact dvd_mul_right _ _

private noncomputable abbrev quadraticSeed (a b c : ℤ) : ℤ[X] := C a * X^2 + C b * X + C c

private lemma term_shape (b : Bool) (f : ℤ[X]) (hd : 0 < f.natDegree) (i : ℕ) :
    (polynomialTerm b f i).natDegree = f.natDegree+i ∧
      (polynomialTerm b f i).leadingCoeff = f.leadingCoeff := by
  induction i with
  | zero => simp [polynomialTerm]
  | succ i ih =>
    let g := polynomialTerm b f i
    have hgd : 0 < g.natDegree := by dsimp [g]; omega
    have hgn : g ≠ 0 := by intro h; simp [h] at hgd
    have hx : (X*g).natDegree = 1+g.natDegree := by rw [natDegree_mul X_ne_zero hgn,natDegree_X]
    have hl : (C (if b then (1:ℤ) else -1)).degree < (X*g).degree := by
      apply degree_lt_degree
      rw [hx,natDegree_C]
      omega
    change (X*g+C _).natDegree = _ ∧ (X*g+C _).leadingCoeff = _
    constructor
    · rw [natDegree_add_C,hx]
      dsimp [g]; omega
    · rw [add_comm,leadingCoeff_add_of_degree_lt hl,leadingCoeff_mul,leadingCoeff_X,one_mul]
      exact ih.2

private lemma term_eval_one (b : Bool) (f : ℤ[X]) (i : ℕ) :
    (polynomialTerm b f i).eval 1 = f.eval 1 + (i : ℤ)*(if b then 1 else -1) := by
  induction i with
  | zero => simp [polynomialTerm]
  | succ i ih => simp only [polynomialTerm,eval_add,eval_mul,eval_X,eval_C,one_mul,ih,Nat.cast_succ]; ring

private lemma term_coeff_zero (b : Bool) (f : ℤ[X]) (i : ℕ) :
    (polynomialTerm b f (i+1)).coeff 0 = if b then 1 else -1 := by
  cases b <;> simp [polynomialTerm]

private lemma first_coeff_nonneg (a : ℕ) (c : ℤ) (hc : 0 < c) (i j : ℕ) (hj : j+1 < 2+i) :
    0 ≤ (polynomialTerm true (quadraticSeed 1 (-((a:ℤ)+1+c)) c) i).coeff j := by
  induction i generalizing j with
  | zero =>
    obtain rfl : j = 0 := by omega
    simpa [polynomialTerm,quadraticSeed] using hc.le
  | succ i ih =>
    cases j with
    | zero => simp [polynomialTerm]
    | succ j =>
      rw [polynomialTerm,coeff_add,coeff_X_mul,coeff_C]
      simpa using ih j (by omega)

private lemma second_coeff_nonpos (a p : ℕ) (hp : a+1 < p) (i j : ℕ) (hj : j < 2+i) :
    (polynomialTerm false (quadraticSeed p (-((p:ℤ)-a-1)) (-1)) i).coeff j ≤ 0 := by
  induction i generalizing j with
  | zero =>
    have h : j ≤ 1 := by omega
    interval_cases j <;> simp [polynomialTerm,quadraticSeed,coeff_mul_X,coeff_one]
    omega
  | succ i ih =>
    cases j with
    | zero => simp [polynomialTerm]
    | succ j =>
      rw [polynomialTerm,coeff_add,coeff_X_mul,coeff_C]
      simpa using ih j (by omega)

private lemma stops_at_root_one (f : ℤ[X]) (hd : 1 < f.natDegree) (h : f.eval 1 = 0) :
    ¬Irreducible (f.map (Int.castRingHom ℚ)) := by
  intro hi
  have hroot : (f.map (Int.castRingHom ℚ)).IsRoot 1 := by
    change (f.map _).eval 1 = 0
    rw [←map_one (Int.castRingHom ℚ),eval_map_apply,h,map_zero]
  have hdeg := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hi hroot)
  rw [natDegree_map_eq_of_injective Int.cast_injective] at hdeg
  change f.natDegree = 1 at hdeg
  omega

private lemma first_quadratic_length (k c : ℕ) (hk : 0 < k) (hc : 0 < c) :
    IsPolynomialChainOfLength true (quadraticSeed 1 (-((k:ℤ)+1+c)) c) k := by
  let f := quadraticSeed 1 (-((k:ℤ)+1+c)) c
  have hd : f.natDegree = 2 := natDegree_quadratic one_ne_zero
  have hl : f.leadingCoeff = 1 := leadingCoeff_quadratic one_ne_zero
  have he (i : ℕ) : (polynomialTerm true f i).eval 1 = (i:ℤ)-k := by
    rw [term_eval_one]; simp [f,quadraticSeed]; ring
  have hs (i : ℕ) := term_shape true f (by omega) i
  refine ⟨hk,by change 0 < f.leadingCoeff; omega,?_,?_⟩
  · intro i hi
    let g := polynomialTerm true f i
    have hdeg : g.natDegree = 2+i := (hs i).1.trans (by rw [hd])
    have hm : g.Monic := (hs i).2.trans hl
    have h₀ : g.coeff 0 ≠ 0 := by
      cases i with
      | zero => simpa [g,f,polynomialTerm,quadraticSeed] using (show (c:ℤ) ≠ 0 by omega)
      | succ i => simp [g,term_coeff_zero]
    exact irreducible_of_one_outer_factor g hm (by omega)
      (fun j hj => first_coeff_nonneg k c (by exact_mod_cast hc) i j (by omega)) h₀
      (by dsimp [g]; rw [he]; omega)
  · apply stops_at_root_one
    · change 1 < (polynomialTerm _ f k).natDegree
      have := (hs k).1; omega
    · rw [he,sub_self]

private lemma second_quadratic_length (k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hpk : k+1 < p) :
    IsPolynomialChainOfLength false (quadraticSeed p (-((p:ℤ)-k-1)) (-1)) k := by
  let f := quadraticSeed p (-((p:ℤ)-k-1)) (-1)
  have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd : f.natDegree = 2 := natDegree_quadratic hp0
  have hl : f.leadingCoeff = p := leadingCoeff_quadratic hp0
  have he (i : ℕ) : (polynomialTerm false f i).eval 1 = (k:ℤ)-i := by
    rw [term_eval_one]; simp [f,quadraticSeed]; ring
  have hs (i : ℕ) := term_shape false f (by omega) i
  refine ⟨hk,by change 0 < f.leadingCoeff; omega,?_,?_⟩
  · intro i hi
    let g := polynomialTerm false f i
    have hdeg : g.natDegree = 2+i := (hs i).1.trans (by rw [hd])
    have hlead : g.leadingCoeff = p := (hs i).2.trans hl
    have h₀ : g.coeff 0 = -1 := by
      cases i with
      | zero => simp [g,f,polynomialTerm,quadraticSeed]
      | succ i => simp [g,term_coeff_zero]
    apply irreducible_of_prime_leading_inside g (by omega) (by rw [h₀]; simp)
      (by rw [hlead]; exact (Nat.prime_iff_prime_int.mp hp).irreducible)
    let G := g.map (Int.castRingHom ℝ)
    have dG : G.natDegree = g.natDegree := natDegree_map_eq_of_injective Int.cast_injective _
    have lG : 0 < G.leadingCoeff := by
      change 0 < (g.map _).leadingCoeff
      rw [leadingCoeff_map_of_injective Int.cast_injective,hlead]
      change 0 < ((p : ℤ) : ℝ)
      exact_mod_cast hp.pos
    have cG (j : ℕ) (hj : j < G.natDegree) : G.coeff j ≤ 0 := by
      have h := second_coeff_nonpos k p hpk i j (by omega)
      change ((g.map _).coeff j) ≤ 0
      rw [coeff_map]
      change (g.coeff j : ℝ) ≤ 0
      change g.coeff j ≤ 0 at h
      exact_mod_cast h
    have vG : 0 < G.eval 1 := by
      change 0 < (g.map (Int.castRingHom ℝ)).eval 1
      rw [←map_one (Int.castRingHom ℝ),eval_map_apply]
      change 0 < ((g.eval 1 : ℤ) : ℝ)
      exact_mod_cast (show 0 < g.eval 1 by dsimp [g]; rw [he]; omega)
    intro z hz
    apply inside_of_nonpositive_coeffs G lG cG vG z
    change ((g.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ)).IsRoot z
    rw [Polynomial.map_map,show (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ from Subsingleton.elim _ _]
    exact hz
  · apply stops_at_root_one
    · change 1 < (polynomialTerm _ f k).natDegree
      have := (hs k).1; omega
    · rw [he,sub_self]

/-- Jones's polynomial exact-length theorem, with irreducibility in ℚ[X]
and positive leading coefficient, witnessed in both cases by quadratic seeds. -/
theorem infinitely_many_quadratic_polynomial_chains (b : Bool) (k : ℕ) (hk : 0 < k) :
    {f : ℤ[X] | f.natDegree = 2 ∧ IsPolynomialChainOfLength b f k}.Infinite := by
  by_contra hf
  have hs := Set.not_infinite.mp hf
  cases b with
  | true =>
    have hfin := (hs.image (fun f : ℤ[X] => f.coeff 0)).bddAbove
    obtain ⟨m,hm⟩ := hfin
    let c := m.natAbs+1
    have hc : 0 < c := Nat.zero_lt_succ _
    let f := quadraticSeed 1 (-((k:ℤ)+1+c)) c
    have hmem : f ∈ {g : ℤ[X] | g.natDegree = 2 ∧ IsPolynomialChainOfLength true g k} :=
      ⟨natDegree_quadratic one_ne_zero,first_quadratic_length k c hk hc⟩
    have h := hm (Set.mem_image_of_mem (fun g : ℤ[X] => g.coeff 0) hmem)
    have he : f.coeff 0 = c := by simp [f,quadraticSeed]
    change f.coeff 0 ≤ m at h
    rw [he] at h
    dsimp [c] at h; omega
  | false =>
    obtain ⟨m,hm⟩ := (hs.image (fun f : ℤ[X] => f.leadingCoeff)).bddAbove
    obtain ⟨p,hp,hpr⟩ := Nat.exists_infinite_primes (m.natAbs+k+2)
    let f := quadraticSeed p (-((p:ℤ)-k-1)) (-1)
    have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hpr.ne_zero
    have hmem : f ∈ {g : ℤ[X] | g.natDegree = 2 ∧ IsPolynomialChainOfLength false g k} :=
      ⟨natDegree_quadratic hp0,second_quadratic_length k p hk hpr (by omega)⟩
    have h := hm (Set.mem_image_of_mem (fun g : ℤ[X] => g.leadingCoeff) hmem)
    have he : f.leadingCoeff = p := leadingCoeff_quadratic hp0
    change f.leadingCoeff ≤ m at h
    rw [he] at h
    omega

#print axioms infinitely_many_quadratic_polynomial_chains

/-- Evaluation at two recovers the pinned integer recurrences for positive
natural initial values. Irreducibility does not imply primality of a value. -/
theorem polynomialTerm_eval_two (b : Bool) (f : ℤ[X]) (p : ℕ) (hp : 0 < p)
    (he : f.eval 2 = p) (i : ℕ) :
    (polynomialTerm b f i).eval 2 =
      ((if b then firstKindTerm else secondKindTerm) p i : ℕ) := by
  cases b with
  | true =>
    induction i with
    | zero => simpa [polynomialTerm,firstKindTerm] using he
    | succ i ih => simp [polynomialTerm,firstKindTerm,ih]
  | false =>
    have pos (n : ℕ) : 0 < secondKindTerm p n := by
      induction n with
      | zero => exact hp
      | succ t ih => simp only [secondKindTerm]; omega
    induction i with
    | zero => simpa [polynomialTerm,secondKindTerm] using he
    | succ i ih =>
      simp only [Bool.false_eq_true,if_false] at ih ⊢
      simp only [polynomialTerm,Bool.false_eq_true,if_false,eval_add,eval_mul,eval_X,eval_C,ih,
        secondKindTerm,Nat.cast_sub (show 1 ≤ 2*secondKindTerm p i by have := pos i; omega),
        Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      ring

#print axioms polynomialTerm_eval_two

/-- Even a positive prime at X=2 need not preserve the first reducible index. -/
theorem polynomial_stop_can_specialize_to_prime :
    ∃ f : ℤ[X], IsPolynomialChainOfLength false f 1 ∧ f.eval 2 = 37 ∧
      (secondKindTerm 37 1).Prime ∧ ¬ IsSecondKindChainOfLength 37 1 := by
  refine ⟨quadraticSeed 17 (-15) (-1),
    second_quadratic_length 1 17 (by decide) (by decide) (by decide),?_,?_,?_⟩
  · norm_num [quadraticSeed]
  · norm_num [secondKindTerm]
  · intro h
    exact h.2.2 (by norm_num [secondKindTerm])

#print axioms polynomial_stop_can_specialize_to_prime

end CunninghamChain
