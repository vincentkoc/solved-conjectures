import Green28DoubleFibres

/-! An integer polynomial separating the real conjugates of a possible
two-level marginal in Green 28, with a count of required nonreal conjugates. -/

namespace Green28ConjugateSignature

open Polynomial Finset Green28 Green28AlgebraicWidth Green28DeficientFibre Green28DoubleFibres
open scoped Polynomial

/-- Homogenization of the degree-twelve integer auxiliary polynomial. -/
def form {R : Type*} [CommRing R] (x y : R) : R :=
  x*(x-y)*(x-2*y)*(x+y)^2*(x^2-2*y^2)*(x^2-x*y-y^2)*(x^3-x^2*y-2*x*y^2+y^3)

private theorem scale (x y : ℝ) : form (y*x) y = y^12*form x 1 := by unfold form; ring

private def Box (a b : ℤ) : Prop := ∀ t : ℝ, 0 ≤ t →
  |32*form ((a:ℝ)+b*t) (64*(1+t))| ≤ 29*(64*(1+t))^12

private theorem boxes (a b : ℤ)
    (mem : (a,b) ∈ ([(-91,-64),(-64,-37),(-37,-10),(-10,18),(18,45),(45,73),
      (73,100),(100,114),(114,121),(121,124),(124,128)] : List (ℤ×ℤ))) : Box a b := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at mem
  rcases mem with m|m|m|m|m|m|m|m|m|m|m <;> obtain ⟨rfl,rfl⟩ := m
  all_goals
    intro t ht
    rw [abs_le]
    constructor <;> rw [←sub_nonneg] <;> unfold form <;> push_cast <;> ring_nf <;> positivity

private theorem local_bound {a b : ℤ} (cert : Box a b) {x : ℝ}
    (left : (a:ℝ) ≤ 64*x) (right : 64*x<(b:ℝ)) : |form x 1| ≤ 29/32 := by
  let t := (64*x-a)/(b-64*x)
  have hp : 0<(b:ℝ)-64*x := sub_pos.mpr right
  have tp : 0 ≤ t := div_nonneg (sub_nonneg.mpr left) hp.le
  have eq : (a:ℝ)+b*t = 64*(1+t)*x := by dsimp [t]; field_simp; ring
  have h := cert t tp
  rw [eq,scale,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 32),abs_mul,
    abs_of_pos (pow_pos (show 0 < 64*(1+t) by positivity) 12)] at h
  have coef : 0<(64*(1+t))^12 := by positivity
  by_contra! fail
  exact (not_lt_of_ge h) (by nlinarith only [mul_lt_mul_of_pos_right fail coef])

/-- An exact bound on an interval containing every permitted real conjugate. -/
theorem real_bound {x : ℝ} (lo : -91 ≤ 64*x) (hi : x ≤ 2) : |form x 1| ≤ 29/32 := by
  by_cases top : x = 2
  · subst x; norm_num [form]
  have lt : 64*x < 128 := by linarith only [hi.lt_of_ne top]
  by_cases h0 : 64*x < -64
  · apply local_bound (boxes (-91) (-64) (by decide)) <;> push_cast <;> linarith
  by_cases h1 : 64*x < -37
  · apply local_bound (boxes (-64) (-37) (by decide)) <;> push_cast <;> linarith
  by_cases h2 : 64*x < -10
  · apply local_bound (boxes (-37) (-10) (by decide)) <;> push_cast <;> linarith
  by_cases h3 : 64*x < 18
  · apply local_bound (boxes (-10) (18) (by decide)) <;> push_cast <;> linarith
  by_cases h4 : 64*x < 45
  · apply local_bound (boxes (18) (45) (by decide)) <;> push_cast <;> linarith
  by_cases h5 : 64*x < 73
  · apply local_bound (boxes (45) (73) (by decide)) <;> push_cast <;> linarith
  by_cases h6 : 64*x < 100
  · apply local_bound (boxes (73) (100) (by decide)) <;> push_cast <;> linarith
  by_cases h7 : 64*x < 114
  · apply local_bound (boxes (100) (114) (by decide)) <;> push_cast <;> linarith
  by_cases h8 : 64*x < 121
  · apply local_bound (boxes (114) (121) (by decide)) <;> push_cast <;> linarith
  by_cases h9 : 64*x < 124
  · apply local_bound (boxes (121) (124) (by decide)) <;> push_cast <;> linarith
  apply local_bound (boxes 124 128 (by decide)) <;> push_cast <;> linarith

private theorem value_ne {x : ℝ} (lo : 1/2 < x) (hi : x < 1) : form x 1 ≠ 0 := by
  have pos : 0 < x := by linarith
  have sq : x^2 < x := by nlinarith only [mul_pos pos (sub_pos.mpr hi)]
  have cube : x^3 < x^2 := by nlinarith only [mul_pos (sq_pos_of_pos pos) (sub_pos.mpr hi)]
  unfold form
  simp only [mul_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_ne_zero_iff]
  repeat' constructor
  all_goals first | positivity | apply ne_of_lt; nlinarith only [lo,hi,sq,cube]

private theorem complex_bound {z : ℂ} (bound : ‖z‖ ≤ 2) : ‖form z 1‖ ≤ 65536 := by
  let h (a : ℤ) (v : ℂ) := (a:ℂ)+z*v
  have step (a : ℤ) {v : ℂ} {M : ℕ} (cap : ‖v‖ ≤ M) : ‖h a v‖ ≤ (a.natAbs+2*M:ℕ) := by
    calc
      ‖h a v‖ ≤ ‖(a:ℂ)‖+‖z*v‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul,Complex.norm_intCast]
        push_cast
        simp only [Nat.cast_natAbs,Int.cast_abs]
        gcongr
  have poly : form z 1 = h 0 (h 4 (h (-2) (h (-26) (h 5 (h 52 (h (-8) (h (-46)
      (h 9 (h 19 (h (-5) (h (-3) 1))))))))))) := by dsimp [form,h]; ring
  rw [poly]
  have h₀ : ‖(1:ℂ)‖ ≤ ((1:ℕ):ℝ) := by simp
  have h1 := step (-3) h₀
  have h2 := step (-5) h1
  have h3 := step (19) h2
  have h4 := step (9) h3
  have h5 := step (-46) h4
  have h6 := step (-8) h5
  have h7 := step (52) h6
  have h8 := step (5) h7
  have h9 := step (-26) h8
  have h10 := step (-2) h9
  have h11 := step (4) h10
  have h12 := step (0) h11
  exact h12.trans (by norm_num)

/-- All complex roots of the monic integral minimal polynomial, counted with multiplicity. -/
noncomputable def conjugates (u : ℝ) : Multiset ℂ := ((minpoly ℤ u).map (algebraMap ℤ ℂ)).roots

/-- For an integral real number and an integer polynomial which does not
vanish there, the product of the conjugate absolute values is at least one. -/
theorem one_le_conjugate_product {u : ℝ} (int : IsIntegral ℤ u) {g : ℤ[X]} (nz : aeval u g ≠ 0) :
    1 ≤ ‖((conjugates u).map fun z => aeval z g).prod‖ := by
  classical
  let f := minpoly ℤ u
  let D := f.resultant g
  have frac := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ int
  have cop : IsCoprime (f.map (algebraMap ℤ ℚ)) (g.map (algebraMap ℤ ℚ)) := by
    rw [←frac]
    refine ((minpoly.irreducible (int.tower_top (A := ℚ))).isCoprime_or_dvd _).resolve_right ?_
    rintro ⟨p,hp⟩
    have eq := congrArg (aeval u) hp
    rw [aeval_map_algebraMap,map_mul,minpoly.aeval,zero_mul] at eq
    exact nz eq
  have iq : Function.Injective (algebraMap ℤ ℚ) := Int.cast_injective
  have nr := resultant_ne_zero _ _ cop
  simp only [natDegree_map_eq_of_injective iq,resultant_map_map] at nr
  have dn : D ≠ 0 := fun e => nr (by change algebraMap ℤ ℚ D = 0; rw [e,map_zero])
  let F := f.map (algebraMap ℤ ℂ)
  have mon : F.Monic := (minpoly.monic int).map _
  have ir : Function.Injective (algebraMap ℤ ℂ) := Int.cast_injective
  have ident := resultant_eq_prod_eval F (g.map (algebraMap ℤ ℂ)) g.natDegree natDegree_map_le
    (IsAlgClosed.splits F)
  rw [mon.leadingCoeff,one_pow,one_mul] at ident
  simp only [F,natDegree_map_eq_of_injective ir,resultant_map_map] at ident
  change (D:ℂ) = _ at ident
  simp only [eval_map_algebraMap] at ident
  change 1 ≤ ‖(((f.map (algebraMap ℤ ℂ)).roots.map fun z => aeval z g).prod)‖
  rw [←ident,Complex.norm_intCast,←Int.cast_abs]
  exact_mod_cast (show 1 ≤ |D| from by have := abs_pos.mpr dn; omega)

private theorem product_estimate (S : Multiset ℂ) (v : ℂ → ℂ)
    (small : ∀ z ∈ S, z.im = 0 → ‖v z‖ ≤ 29/32) (large : ∀ z ∈ S, ‖v z‖ ≤ 65536) :
    ‖(S.map v).prod‖ ≤ (29/32:ℝ)^(S.filter fun z => z.im = 0).card*
      65536^(S.filter fun z => z.im ≠ 0).card := by
  classical
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    have ih := ih (fun t ht => small t (Multiset.mem_cons_of_mem ht))
      (fun t ht => large t (Multiset.mem_cons_of_mem ht))
    simp only [Multiset.map_cons,Multiset.prod_cons,norm_mul]
    by_cases re : z.im = 0
    · have le := mul_le_mul (small z (by simp) re) ih (norm_nonneg _) (by norm_num)
      simpa [re,pow_succ,mul_comm,mul_assoc,mul_left_comm] using le
    · have le := mul_le_mul (large z (by simp)) ih (norm_nonneg _) (by norm_num)
      simpa [re,pow_succ,mul_comm,mul_assoc,mul_left_comm] using le

private theorem count_bound {r c : ℕ} (pos : 0 < r+c)
    (one : 1 ≤ (29/32:ℝ)^r*65536^c) : r < 128*c := by
  by_contra! le
  have dec : (29/32:ℝ)^r ≤ (29/32:ℝ)^(128*c) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) le
  by_cases zero : c = 0
  · subst c; simp only [pow_zero,mul_one] at one
    exact (not_lt_of_ge one) (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
  · have small : (29/32:ℝ)^128*65536 < 1 := by norm_num
    have st := pow_lt_one₀ (show 0 ≤ (29/32:ℝ)^128*65536 by positivity) small zero
    rw [mul_pow,←pow_mul] at st
    exact (not_lt_of_ge one) ((mul_le_mul_of_nonneg_right dec (by positivity)).trans_lt st)

/-- In the double-fibre setting, strictly more than one conjugate in 129 is
nonreal. Each root of the minimal polynomial is counted with its multiplicity. -/
theorem signature_bound {u : ℝ} (int : IsIntegral ℤ u) (lo : 1/2 < u) (hi : u < 1)
    (bounds : ∀ z : ℂ, aeval z (minpoly ℚ u) = 0 → ‖z‖ ≤ 2 ∧ (‖z‖-1)*‖1-z‖ ≤ 1) :
    ((conjugates u).filter fun z => z.im = 0).card <
      128*((conjugates u).filter fun z => z.im ≠ 0).card := by
  classical
  let g : ℤ[X] := form X 1
  have evalg {K : Type} [Field K] [CharZero K] (z : K) : aeval z g = form z 1 := by
    have two : aeval z (2:ℤ[X]) = 2 := by rw [show (2:ℤ[X]) = 1+1 by norm_num,map_add,map_one]; norm_num
    simp [g,form,two]
  have integral := one_le_conjugate_product int (g := g) (by rw [evalg]; exact value_ne lo hi)
  let F := (minpoly ℤ u).map (algebraMap ℤ ℂ)
  have root {z : ℂ} (hz : z ∈ conjugates u) : aeval z (minpoly ℚ u) = 0 := by
    have e := isRoot_of_mem_roots hz
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ int,aeval_map_algebraMap]
    simpa only [IsRoot.def,eval_map_algebraMap] using e
  have small (z : ℂ) (hz : z ∈ conjugates u) (re : z.im = 0) : ‖aeval z g‖ ≤ 29/32 := by
    have eq : (z.re:ℂ) = z := by simpa [re] using z.re_add_im
    have ⟨a,b⟩ := bounds z (root hz)
    rw [←eq,Complex.norm_real,Real.norm_eq_abs] at a
    rw [←eq,←Complex.ofReal_one,←Complex.ofReal_sub] at b
    simp only [Complex.norm_real,Real.norm_eq_abs] at b
    have hi' := (abs_le.mp a).2
    have lo' : -91 ≤ 64*z.re := by
      by_contra! low
      rw [abs_of_neg (by linarith : z.re < 0),abs_of_pos (by linarith : 0 < 1-z.re)] at b
      nlinarith only [b,low,sq_nonneg (z.re+91/64)]
    have h := real_bound lo' hi'
    rw [evalg,←eq]
    have cast : form (z.re:ℂ) 1 = (form z.re 1:ℝ) := by unfold form; push_cast; rfl
    rw [cast,Complex.norm_real,Real.norm_eq_abs]; exact h
  have large (z : ℂ) (hz : z ∈ conjugates u) : ‖aeval z g‖ ≤ 65536 := by
    rw [evalg]; exact complex_bound (bounds z (root hz)).1
  apply count_bound _ (integral.trans (product_estimate _ _ small large))
  have partition := congrArg Multiset.card (Multiset.filter_add_not (fun z : ℂ => z.im = 0) (conjugates u))
  rw [Multiset.card_add] at partition
  rw [partition]
  change 0 < F.roots.card
  rw [←(IsAlgClosed.splits F).natDegree_eq_card_roots]
  change 0<((minpoly ℤ u).map (algebraMap ℤ ℂ)).natDegree
  rw [natDegree_map_eq_of_injective
    (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective)]
  exact minpoly.natDegree_pos int

/-- A two-level counterexample to Green 28 with local multiplicity at most two
forces a positive proportion of nonreal conjugates of its actual probability ratio. -/
theorem counterexample_signature {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q)) (levels : Green28TwoMassLevels.AtMostTwo Q)
    (double : ∀ b, IsGreatest Q.support b → ∀ d ∈ Q.support, Q d < Q b → DoubleAt P Q d) :
    ∃ b, IsGreatest Q.support b ∧ ∃ d ∈ Q.support, Q d < Q b ∧
      let S := conjugates (weight Q b d)
      (S.filter fun z => z.im = 0).card < 128*(S.filter fun z => z.im ≠ 0).card := by
  obtain ⟨b,qb,d,qd,low,int,lo,hi,_,bounds⟩ := counterexample_weight flat bad levels double
  exact ⟨b,qb,d,qd,low,signature_bound int lo hi bounds⟩

/-- Green 28 holds under the local double-fibre and two-level assumptions if
the deficient probability ratio is totally real, with arbitrary algebraic degree. -/
theorem uniform_of_totally_real_ratio {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (levels : Green28TwoMassLevels.AtMostTwo Q)
    (localBound : ∀ b, IsGreatest Q.support b → ∀ d ∈ Q.support, Q d < Q b →
      DoubleAt P Q d ∧ ∀ z ∈ conjugates (weight Q b d), z.im = 0) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  classical
  by_contra bad
  obtain ⟨b,qb,d,qd,low,sign⟩ := counterexample_signature flat bad levels
    (fun b qb d qd low => (localBound b qb d qd low).1)
  have re := (localBound b qb d qd low).2
  let S := conjugates (weight Q b d)
  have empty : (S.filter fun z => z.im ≠ 0) = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro z hz
    obtain ⟨mem,ne⟩ := Multiset.mem_filter.mp hz
    exact ne (re z mem)
  change (S.filter fun z => z.im = 0).card < 128*(S.filter fun z => z.im ≠ 0).card at sign
  simp [empty] at sign

#print axioms real_bound
#print axioms one_le_conjugate_product
#print axioms signature_bound
#print axioms counterexample_signature
#print axioms uniform_of_totally_real_ratio
end Green28ConjugateSignature
