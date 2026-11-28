import Mathlib
import research.arxiv.«1104.1579».CunninghamPolynomialLengths

/-!
# Infinite polynomial Cunningham chains

Jones's recurrence preserves rational irreducibility at every index for
the first-kind seeds `pX + 1` with prime `p` and second-kind seeds `X − c`.
-/

namespace CunninghamChain

open Polynomial

/-- The seed has positive leading coefficient and every iterate is
irreducible in the rational polynomial ring. -/
def IsInfinitePolynomialChain (b : Bool) (f : ℤ[X]) : Prop :=
  0 < f.leadingCoeff ∧ ∀ i, Irreducible ((polynomialTerm b f i).map (Int.castRingHom ℚ))

private lemma eq_one_of_re_ge_one {w : ℂ} (hw : ‖w‖ ≤ 1) (hre : 1 ≤ w.re) : w = 1 := by
  have he : w.re = 1 := le_antisymm ((Complex.re_le_norm _).trans hw) hre
  have h := Complex.sq_norm_sub_sq_re w
  have him : w.im = 0 := by nlinarith [sq_nonneg w.im, norm_nonneg w, mul_self_le_mul_self (norm_nonneg w) hw]
  exact Complex.ext (by simpa using he) (by simpa using him)

private noncomputable abbrev primeSeed (p : ℕ) : ℤ[X] := C (p : ℤ) * X + C 1

private lemma first_term_identity (p : ℕ) (z : ℂ) (i : ℕ) :
    (z-1) * ((polynomialTerm true (primeSeed p) i).map (Int.castRingHom ℂ)).eval z =
      ((p : ℂ)*z-((p : ℂ)-1))*z^(i+1)-1 := by
  induction i with
  | zero => simp [polynomialTerm,primeSeed]; ring
  | succ i ih =>
    simp [polynomialTerm]
    rw [pow_succ z (i+1)]
    linear_combination z*ih

/-- Jones's first-kind linear family. Every positive prime leading
coefficient gives an infinite chain from the seed `pX + 1`. -/
theorem prime_linear_firstKind_infinite (p : ℕ) (hp : p.Prime) :
    IsInfinitePolynomialChain true (C (p : ℤ)*X + C 1) := by
  let f := primeSeed p
  have hp₀ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd : f.natDegree = 1 := natDegree_linear hp₀
  have hl : f.leadingCoeff = (p : ℤ) := leadingCoeff_linear hp₀
  refine ⟨by change 0 < f.leadingCoeff; rw [hl]; exact_mod_cast hp.pos, ?_⟩
  intro i
  let g := polynomialTerm true f i
  have hs := polynomialTerm_shape true f (by omega) i
  have hg : g.leadingCoeff = (p : ℤ) := hs.2.trans hl
  have hc : g.coeff 0 = 1 := by cases i <;> simp [g,f,primeSeed,polynomialTerm]
  apply irreducible_of_prime_leading_inside g (by change 0 < (polynomialTerm _ f i).natDegree; omega)
    (hc ▸ isUnit_one) (by rw [hg]; exact (Nat.prime_iff_prime_int.mp hp).irreducible)
  intro z hz
  by_contra! hge
  have hne : z ≠ 0 := by intro h; rw [h,norm_zero] at hge; linarith
  let w := z⁻¹
  have hw : ‖w‖ ≤ 1 := by simpa [w,norm_inv] using (inv_le_one_of_one_le₀ hge)
  have hcancel (j : ℕ) : z^j*w^j = 1 := by rw [←mul_pow]; simp [w,hne]
  have hgap : z^(i+1)*w^(i+2) = w := by rw [pow_succ w (i+1),←mul_assoc,hcancel,one_mul]
  have hid := first_term_identity p z i
  change ((polynomialTerm true (primeSeed p) i).map (Int.castRingHom ℂ)).eval z = 0 at hz
  rw [hz,mul_zero] at hid
  have he : (p : ℂ)*z^(i+2) = ((p:ℂ)-1)*z^(i+1)+1 := by
    rw [pow_succ z (i+1)]
    linear_combination -hid
  have hmul := congrArg (fun x : ℂ => x*w^(i+2)) he
  simp only [add_mul,mul_assoc,hgap,hcancel,mul_one,one_mul] at hmul
  have hreal := congrArg Complex.re hmul
  simp [Complex.mul_re,Complex.sub_re] at hreal
  have hu : (w^(i+2)).re ≤ 1 := (Complex.re_le_norm _).trans (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw)
  have hpp : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hw1 : w = 1 := eq_one_of_re_ge_one hw (by nlinarith)
  have hz1 : z = 1 := by simpa [w] using congrArg Inv.inv hw1
  rw [hz1,←map_one (Int.castRingHom ℂ),eval_map_apply] at hz
  have hev := polynomialTerm_eval_one true f i
  have h₁ : f.eval 1 = (p:ℤ)+1 := by simp [f,primeSeed]
  rw [h₁] at hev
  change ((g.eval 1 : ℤ) : ℂ) = 0 at hz
  have : g.eval 1 = 0 := by exact_mod_cast hz
  simp [g] at this
  simp at hev
  omega

#print axioms prime_linear_firstKind_infinite

open Filter Topology

private lemma roots_inside_of_strictly_increasing (q : ℝ[X]) (hm : q.Monic)
    (hc : 0 < q.coeff 0) (hv : 0 < q.eval 1)
    (hinc : ∀ i < q.natDegree, q.coeff i < q.coeff (i+1)) :
    ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ < 1 := by
  classical
  have ev : ∀ᶠ t in 𝓝 (1:ℝ), ∀ i ∈ Finset.range q.natDegree,
      q.coeff i < t*q.coeff (i+1) := by
    apply (Filter.eventually_all_finset _).2
    intro i hi
    have h : ContinuousAt (fun t : ℝ => t*q.coeff (i+1)) 1 := by fun_prop
    exact h.tendsto.eventually_const_lt (by simpa using hinc i (Finset.mem_range.mp hi))
  have lo : ∀ᶠ t in 𝓝[<] (1:ℝ), 0 < t := nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num))
  have hi : ∀ᶠ t in 𝓝[<] (1:ℝ), t < 1 := self_mem_nhdsWithin
  obtain ⟨t,ht₁,ht₀,ht⟩ := (hi.and (lo.and (ev.filter_mono nhdsWithin_le_nhds))).exists
  let f := (X-C t)*q
  have hfm : f.Monic := (monic_X_sub_C t).mul hm
  have hd : f.natDegree = 1+q.natDegree := by
    rw [show f = _ from rfl,natDegree_mul (X_sub_C_ne_zero t) hm.ne_zero,natDegree_X_sub_C]
  have hneg (i : ℕ) (hi : i < f.natDegree) : f.coeff i ≤ 0 := by
    cases i with
    | zero => simp [f,mul_coeff_zero]; positivity
    | succ j =>
      change ((X-C t)*q).coeff (j+1) ≤ 0
      rw [coeff_X_sub_C_mul]
      have := ht j (Finset.mem_range.mpr (by omega))
      linarith
  have hval : 0 < f.eval 1 := by
    simp only [f,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos (sub_pos.mpr ht₁) hv
  intro z hz
  apply inside_of_nonpositive_coeffs f (by rw [hfm.leadingCoeff]; norm_num) hneg hval
  change ((f.map _).eval z) = 0
  simp only [f,Polynomial.map_mul,eval_mul,show (q.map (algebraMap ℝ ℂ)).eval z = 0 from hz,mul_zero]

/-- Brauer's criterion for a monic integral polynomial of degree at least two
whose lower coefficients are negative and nonincreasing. -/
theorem brauer_irreducible_of_coeff (f : ℤ[X]) (hm : f.Monic) (hd : 1 < f.natDegree)
    (h₀ : f.coeff 0 < 0) (hc : ∀ i, i+1 < f.natDegree → f.coeff (i+1) ≤ f.coeff i) :
    Irreducible (f.map (Int.castRingHom ℚ)) := by
  let F := f.map (Int.castRingHom ℝ)
  have hdF : F.natDegree = f.natDegree := natDegree_map_eq_of_injective Int.cast_injective _
  have hmF : F.Monic := hm.map _
  have h0 : F.coeff 0 ≤ -1 := by
    change (f.map _).coeff 0 ≤ -1
    rw [coeff_map]
    change (f.coeff 0 : ℝ) ≤ -1
    exact_mod_cast (show f.coeff 0 ≤ -1 by omega)
  have hcoef (i : ℕ) (hi : i+1 < F.natDegree) : F.coeff (i+1) ≤ F.coeff i := by
    simp only [F,coeff_map]
    change (f.coeff (i+1) : ℝ) ≤ (f.coeff i : ℝ)
    exact_mod_cast hc i (by omega)
  have hneg (i : ℕ) (hi : i < F.natDegree) : F.coeff i ≤ -1 := by
    induction i with
    | zero => exact h0
    | succ j ih => exact (hcoef _ hi).trans (ih (by omega))
  have hv : F.eval 1 < 0 := by
    rw [eval_eq_sum_range,Finset.sum_range_succ]
    simp only [one_pow,mul_one]
    have hs := Finset.sum_le_sum (s := Finset.range F.natDegree)
      (fun i hi => hneg i (Finset.mem_range.mp hi))
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_neg,mul_one] at hs
    change (∑ i ∈ Finset.range F.natDegree, F.coeff i) + F.leadingCoeff < 0
    rw [hmF.leadingCoeff]
    have hdeg : (1 : ℝ) < F.natDegree := by exact_mod_cast (show 1 < F.natDegree by omega)
    linarith
  have hat := F.tendsto_atTop_of_leadingCoeff_nonneg
    (natDegree_pos_iff_degree_pos.mp (by omega)) (by rw [hmF.leadingCoeff]; norm_num)
  obtain ⟨b,hb,hb'⟩ := ((eventually_gt_atTop (1 : ℝ)).and (hat.eventually_gt_atTop 0)).exists
  obtain ⟨r,hr,hr'⟩ := intermediate_value_Ioo hb.le F.continuous.continuousOn ⟨hv,hb'⟩
  obtain ⟨q,hq⟩ := dvd_iff_isRoot.mpr (show F.IsRoot r from hr')
  have hqm := (monic_X_sub_C r).of_mul_monic_left (hq ▸ hmF)
  have hdq : F.natDegree = 1+q.natDegree := by
    rw [hq,natDegree_mul (X_sub_C_ne_zero r) hqm.ne_zero,natDegree_X_sub_C]
  have hq0 : F.coeff 0 = -r*q.coeff 0 := by simp [hq,mul_coeff_zero]
  have hqpos : 0 < q.coeff 0 := by nlinarith [hr.1]
  have hstep (j : ℕ) : F.coeff (j+1) = q.coeff j - r*q.coeff (j+1) := by
    rw [hq,coeff_X_sub_C_mul]
  have inc (i : ℕ) (hi : i < q.natDegree) : q.coeff i < q.coeff (i+1) := by
    induction i with
    | zero =>
      apply lt_of_mul_lt_mul_left (a := r) _ (by linarith [hr.1])
      linarith [hcoef 0 (by omega),hstep 0]
    | succ i ih =>
      apply lt_of_mul_lt_mul_left (a := r) _ (by linarith [hr.1])
      linarith [ih (by omega),hcoef (i+1) (by omega),hstep i,hstep (i+1)]
  have hqv : 0 < q.eval 1 := by rw [hq,eval_mul,eval_sub,eval_X,eval_C] at hv; nlinarith [hr.1]
  exact irreducible_of_real_linear_factor f hm (by omega) h₀.ne r q hq
    (roots_inside_of_strictly_increasing q hqm hqpos hqv inc)

#print axioms brauer_irreducible_of_coeff

private lemma minus_linear_coeffs (c : ℤ) (i : ℕ) :
    (polynomialTerm false (X-C c) i).coeff i = -c ∧
      ∀ j < i, (polynomialTerm false (X-C c) i).coeff j = -1 := by
  induction i with
  | zero => simp [polynomialTerm]
  | succ i ih =>
    constructor
    · simpa [polynomialTerm,coeff_X_mul,coeff_one] using ih.1
    · intro j hj
      cases j with
      | zero => simp [polynomialTerm]
      | succ j => simpa [polynomialTerm,coeff_X_mul,coeff_one] using ih.2 j (by omega)

/-- Exactly the monic linear seeds with negative constant term start
infinite second-kind polynomial chains. -/
theorem monic_linear_secondKind_infinite_iff (c : ℤ) :
    IsInfinitePolynomialChain false (X-C c) ↔ 1 ≤ c := by
  have hd : (X-C c).natDegree = 1 := natDegree_X_sub_C c
  have hs := polynomialTerm_shape false (X-C c) (by omega)
  constructor
  · intro h
    by_contra! hle
    let i := (1-c).toNat
    have hi : (i : ℤ) = 1-c := Int.toNat_of_nonneg (by omega)
    have hval := polynomialTerm_eval_one false (X-C c) i
    simp only [eval_sub,eval_X,eval_C,Bool.false_eq_true,if_false,hi] at hval
    have hev : (polynomialTerm false (X-C c) i).eval 1 = 0 := by linarith
    have hdg := (hs i).1
    have hr : ((polynomialTerm false (X-C c) i).map (Int.castRingHom ℚ)).IsRoot 1 := by
      change (Polynomial.map _ _).eval 1 = 0
      rw [←map_one (Int.castRingHom ℚ),eval_map_apply]
      rw [hev,map_zero]
    have hdeg := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root (h.2 i) hr)
    rw [natDegree_map_eq_of_injective Int.cast_injective] at hdeg
    change (polynomialTerm false (X-C c) i).natDegree = 1 at hdeg
    omega
  · intro hc
    refine ⟨by rw [(monic_X_sub_C c).leadingCoeff]; norm_num, ?_⟩
    intro i
    cases i with
    | zero =>
      simp only [polynomialTerm,Polynomial.map_sub,map_X,map_C]
      exact (prime_X_sub_C _).irreducible
    | succ i =>
      let g := polynomialTerm false (X-C c) (i+1)
      have hdg : g.natDegree = 1+(i+1) := (hs _).1.trans (by rw [hd])
      have hmon : g.Monic := (hs _).2.trans (monic_X_sub_C c).leadingCoeff
      obtain ⟨hsub,hlo⟩ := minus_linear_coeffs c (i+1)
      apply brauer_irreducible_of_coeff g hmon (by omega)
      · change (polynomialTerm false _ _).coeff 0 < 0
        rw [hlo 0 (by omega)]; norm_num
      · intro j hj
        change (polynomialTerm false _ _).coeff (j+1) ≤ (polynomialTerm false _ _).coeff j
        rw [hlo j (by omega)]
        rcases lt_or_eq_of_le (show j+1 ≤ i+1 by omega) with h|h
        · rw [hlo _ h]
        · rw [h,hsub]; omega

/-- Jones's Corollary 1.6, with infinitely many degree-one seeds for each sign. -/
theorem infinitely_many_linear_infinite_polynomial_chains (b : Bool) :
    {f : ℤ[X] | f.natDegree = 1 ∧ IsInfinitePolynomialChain b f}.Infinite := by
  by_contra hf
  have hs := Set.not_infinite.mp hf
  cases b with
  | true =>
    obtain ⟨m,hm⟩ := (hs.image (fun f => f.leadingCoeff)).bddAbove
    obtain ⟨p,hp,hpr⟩ := Nat.exists_infinite_primes (m.natAbs+1)
    have hn : (p:ℤ) ≠ 0 := by exact_mod_cast hpr.ne_zero
    have hmem : primeSeed p ∈ {f : ℤ[X] | f.natDegree = 1 ∧ IsInfinitePolynomialChain true f} :=
      ⟨natDegree_linear hn,prime_linear_firstKind_infinite p hpr⟩
    have h := hm (Set.mem_image_of_mem (fun f : ℤ[X] => f.leadingCoeff) hmem)
    change (primeSeed p).leadingCoeff ≤ m at h
    have he : (primeSeed p).leadingCoeff = (p : ℤ) := leadingCoeff_linear hn
    omega
  | false =>
    obtain ⟨m,hm⟩ := (hs.image (fun f => f.coeff 0)).bddBelow
    let c : ℤ := (m.natAbs : ℤ)+1
    have hc : 1 ≤ c := by dsimp [c]; omega
    have hmem : X-C c ∈ {f : ℤ[X] | f.natDegree = 1 ∧ IsInfinitePolynomialChain false f} :=
      ⟨natDegree_X_sub_C _,(monic_linear_secondKind_infinite_iff c).2 hc⟩
    have h := hm (Set.mem_image_of_mem (fun f : ℤ[X] => f.coeff 0) hmem)
    change m ≤ (X-C c).coeff 0 at h
    simp at h
    dsimp [c] at h
    omega

#print axioms monic_linear_secondKind_infinite_iff
#print axioms infinitely_many_linear_infinite_polynomial_chains

end CunninghamChain
