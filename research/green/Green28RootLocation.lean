import Green28PrimitiveSupport
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# A root-location obstruction for Green 28

A nonreciprocal real monic factor with constant term one has a root on
each side of the unit circle. Real coefficients permit taking both witnesses
in the closed upper half-plane. Hasanbegović's palindromic-support argument
then gives a criterion on the roots of the output mask alone.
-/

namespace Green28RootLocation
open Polynomial Finset
open scoped Polynomial ComplexConjugate NNReal

private noncomputable def fromRoots (s : Multiset ℂ) : ℂ[X] :=
  (s.map (fun z => X-C z)).prod

private lemma fromRoots_cons (z : ℂ) (s : Multiset ℂ) :
    fromRoots (z::ₘs) = (X-C z)*fromRoots s := by simp [fromRoots]

private lemma reverse_linear (z : ℂ) : (X-C z).reverse = 1-C z*X := by
  rw [reverse,natDegree_X_sub_C]
  change (X + -C z).reflect 1 = _
  rw [reflect_add,reflect_one_X,←C_neg,reflect_C]
  simp; ring

private lemma fromRoots_reverse (s : Multiset ℂ) (unit : ∀ z ∈ s, ‖z‖=1) :
    (fromRoots s).reverse = C ((fromRoots s).coeff 0)*(fromRoots s).map (starRingEnd ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp [fromRoots,reverse]
  | cons z s ih =>
    have uz := unit z (Multiset.mem_cons_self ..)
    have ns : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq,uz,one_pow]
    have conjz : z * conj z = 1 := by simp [Complex.mul_conj,ns]
    have lin : 1-C z*X = C (-z)*(X-C (conj z)) := by
      rw [mul_sub,←C_mul,neg_mul,conjz]; simp; ring
    rw [fromRoots_cons,reverse_mul_of_domain,reverse_linear,lin,ih (fun a ha => unit a (Multiset.mem_cons_of_mem ha)),
      mul_coeff_zero,Polynomial.map_mul,Polynomial.map_sub,map_X,map_C]
    simp only [coeff_sub,coeff_X_zero,coeff_C_zero,zero_sub,C_mul]
    ring

/-- A real monic polynomial with unit-modulus roots is reciprocal up to
its constant term, which can have either sign. -/
theorem reverse_eq_scaled_of_unit_roots (f : ℝ[X]) (fm : f.Monic)
    (unit : ∀ z ∈ (f.map Complex.ofRealHom).roots, ‖z‖ = 1) :
    f.reverse = C (f.coeff 0)*f := by
  let F := f.map Complex.ofRealHom
  have fact : F = fromRoots F.roots := (IsAlgClosed.splits F).eq_prod_roots_of_monic (fm.map _)
  have h := fromRoots_reverse F.roots unit
  have conjfix : F.map (starRingEnd ℂ) = F := by ext n; simp [F,coeff_map]
  rw [←fact,conjfix] at h
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  simpa only [reverse,F,reflect_map,fm.natDegree_map,coeff_map,Polynomial.map_mul,map_C] using h

/-- A real monic polynomial with constant coefficient one and all its complex
roots on the unit circle agrees with its reversal. -/
theorem reciprocal_of_unit_roots (f : ℝ[X]) (fm : f.Monic) (fc : f.coeff 0 = 1)
    (unit : ∀ z ∈ (f.map Complex.ofRealHom).roots, ‖z‖=1) : f.reverse = f := by
  simpa [fc] using reverse_eq_scaled_of_unit_roots f fm unit

private lemma norm_product (f : ℝ[X]) (fm : f.Monic) (fc : f.coeff 0 = 1) :
    (((f.map Complex.ofRealHom).roots).map (fun z => ‖z‖₊)).prod = 1 := by
  let F := f.map Complex.ofRealHom
  have eq := (IsAlgClosed.splits F).coeff_zero_eq_prod_roots_of_monic (fm.map _)
  have const : F.coeff 0 = 1 := by simp [F,coeff_map,fc]
  rw [const] at eq
  have h := congrArg (fun c : ℂ => ‖c‖₊) eq
  rw [nnnorm_one,nnnorm_mul,nnnorm_pow,nnnorm_neg,nnnorm_one,one_pow,one_mul] at h
  exact (Multiset.prod_hom F.roots (nnnormHom : ℂ →*₀ ℝ≥0)).trans h.symm

private lemma both_sides (f : ℝ[X]) (fm : f.Monic) (fc : f.coeff 0 = 1) (bad : f.reverse ≠ f) :
    (∃ z ∈ (f.map Complex.ofRealHom).roots, ‖z‖ < 1) ∧
    (∃ z ∈ (f.map Complex.ofRealHom).roots, 1 < ‖z‖) := by
  let s := (f.map Complex.ofRealHom).roots
  let m := s.map (fun z => ‖z‖₊)
  have p : m.prod = 1 := norm_product f fm fc
  have mem {z : ℂ} (hz : z ∈ s) : ‖z‖₊ ∈ m := Multiset.mem_map.mpr ⟨z,hz,rfl⟩
  constructor
  · by_contra! h
    apply bad (reciprocal_of_unit_roots f fm fc (fun z hz => ?_))
    have ge (r : ℝ≥0) (hr : r ∈ m) : 1 ≤ r := by
      obtain ⟨x,hx,rfl⟩ := Multiset.mem_map.mp hr
      exact h x hx
    exact congrArg NNReal.toReal (Multiset.all_one_of_le_one_le_of_prod_eq_one ge p _ (mem hz))
  · by_contra! h
    apply bad (reciprocal_of_unit_roots f fm fc (fun z hz => ?_))
    have le (r : ℝ≥0) (hr : r ∈ m) : r ≤ 1 := by
      obtain ⟨x,hx,rfl⟩ := Multiset.mem_map.mp hr
      exact h x hx
    have eq : ‖z‖₊=1 := Multiset.all_one_of_le_one_le_of_prod_eq_one
      (α:=OrderDual ℝ≥0) (s:=m) le p _ (mem hz)
    exact congrArg NNReal.toReal eq

open Green28PolynomialReduction

/-- The interior terms of a convolution coefficient only use earlier
coefficients of the factors. -/
theorem coeff_mul_middle_mem {f g : ℝ[X]} (K : Subfield ℝ) {n : ℕ} (hn : 0 < n)
    (hf : ∀ i < n, f.coeff i ∈ K) (hg : ∀ i < n, g.coeff i ∈ K) :
    (f*g).coeff n-(f.coeff n*g.coeff 0 + f.coeff 0*g.coeff n) ∈ K := by
  let T := antidiagonal n
  let w (ij : ℕ×ℕ) := f.coeff ij.1*g.coeff ij.2
  have e : (0,n) ∈ T := mem_antidiagonal.mpr (by omega)
  have d : (n,0) ∈ T.erase (0,n) := mem_erase.mpr
    ⟨fun h => hn.ne' (congrArg Prod.fst h),mem_antidiagonal.mpr (by omega)⟩
  have rest : (∑ ij ∈ (T.erase (0,n)).erase (n,0), w ij) ∈ K := by
    apply K.sum_mem
    rintro ⟨i,j⟩ hij
    obtain ⟨ne,mem⟩ := mem_erase.mp hij
    obtain ⟨ne',elt⟩ := mem_erase.mp mem
    have eq : i+j = n := mem_antidiagonal.mp elt
    have l : i < n := by
      by_contra! h
      exact ne (Prod.ext (by change i = n; omega) (by change j = 0; omega))
    have r : j < n := by
      by_contra! h
      exact ne' (Prod.ext (by change i = 0; omega) (by change j = n; omega))
    exact K.mul_mem (hf i l) (hg j r)
  have eq : (f*g).coeff n = (∑ ij ∈ (T.erase (0,n)).erase (n,0), w ij)+(w (n,0)+w (0,n)) := by
    rw [←add_assoc,sum_erase_add _ _ d,sum_erase_add _ _ e,coeff_mul]
  change (f*g).coeff n-(w (n,0)+w (0,n)) ∈ K
  simpa only [eq,add_sub_cancel_right] using rest

/-- At a positive offset, the reflected left coefficient and the right coefficient
cannot both be nonzero: the boundary sum already has a contribution of one. -/
theorem reverse_coeff_eq_zero_or {f g : ℝ[X]} (fm : f.Monic) (gc : g.coeff 0 = 1)
    (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i) (bin : Binary (f*g))
    {n : ℕ} (hn : 0 < n) : f.reverse.coeff n = 0 ∨ g.coeff n = 0 := by
  by_cases nd : n ≤ f.natDegree
  · by_contra! nonzero
    let d := f.natDegree
    have rev : f.reverse.coeff n = f.coeff (d-n) := by rw [coeff_reverse,revAt_le nd]
    let T := antidiagonal d
    let w (ij : ℕ×ℕ) := f.coeff ij.1*g.coeff ij.2
    have e : (d,0) ∈ T := mem_antidiagonal.mpr (by omega)
    have v : (d-n,n) ∈ T.erase (d,0) := mem_erase.mpr
      ⟨fun h => hn.ne' (congrArg Prod.snd h),mem_antidiagonal.mpr (by dsimp [d]; omega)⟩
    have le : w (d-n,n) ≤ ∑ ij ∈ T.erase (d,0), w ij :=
      single_le_sum (fun x _ => mul_nonneg (fp _) (gp _)) v
    have eq : (∑ ij ∈ T.erase (d,0), w ij)+w (d,0) = (f*g).coeff d := by
      rw [sum_erase_add _ _ e,coeff_mul]
    have top : w (d,0) = 1 := by simp [w,d,fm.coeff_natDegree,gc]
    have extra : 0 < w (d-n,n) := mul_pos
      (lt_of_le_of_ne (fp _) (rev ▸ nonzero.1).symm) (lt_of_le_of_ne (gp _) nonzero.2.symm)
    rcases bin d with h|h <;> linarith
  · exact Or.inl (coeff_eq_zero_of_natDegree_lt ((reverse_natDegree_le f).trans_lt (lt_of_not_ge nd)))

private theorem rational_of_disjoint {f g : ℝ[X]} (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1)
    (bin : Binary (f*g)) (disj : ∀ i : ℕ, 0 < i → f.coeff i = 0 ∨ g.coeff i = 0) :
    ∀ i, f.coeff i ∈ (algebraMap ℚ ℝ).fieldRange ∧ g.coeff i ∈ (algebraMap ℚ ℝ).fieldRange := by
  let K := (algebraMap ℚ ℝ).fieldRange
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl|hn
    · exact ⟨fc ▸ K.one_mem,gc ▸ K.one_mem⟩
    have mid := coeff_mul_middle_mem K hn (fun i hi => (ih i hi).1) (fun i hi => (ih i hi).2)
    have zn : (f*g).coeff n ∈ K := (bin n).elim (fun e => e ▸ K.zero_mem) (fun e => e ▸ K.one_mem)
    have plus := K.sub_mem zn mid
    simp only [fc,gc,one_mul,mul_one,sub_sub_cancel] at plus
    rcases disj n hn with h|h
    · rw [h,zero_add] at plus
      exact ⟨h ▸ K.zero_mem,plus⟩
    · rw [h,add_zero] at plus
      exact ⟨plus,h ▸ K.zero_mem⟩

/-- Hasanbegović's palindromic-support criterion applied to a reciprocal
normalized factor. The cofactor may have arbitrary support and degree. -/
theorem binary_of_reciprocal {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) (sym : f.reverse = f) : Binary f ∧ Binary g := by
  have rational := rational_of_disjoint fc gc bin (fun n hi => by
    simpa only [sym] using reverse_coeff_eq_zero_or fm gc fp gp bin hi)
  exact rational_factor fm gm fp gp bin (fun i => (rational i).1)

/-- Count roots with nonnegative imaginary part, with multiplicity, to avoid
counting both members of a nonreal conjugate pair. -/
noncomputable def rootCount (P : ℂ[X]) (region : ℝ → Prop) : ℕ := by
  classical
  exact (P.roots.filter (fun z => region ‖z‖ ∧ 0 ≤ z.im)).card

private lemma rootCount_mul (F G : ℂ[X]) (f : F ≠ 0) (g : G ≠ 0) (region : ℝ → Prop) :
    rootCount (F*G) region = rootCount F region+rootCount G region := by
  classical
  simp [rootCount,roots_mul (mul_ne_zero f g),Multiset.filter_add]

private lemma real_rootCount_pos {f : ℝ[X]} (fm : f.Monic) (region : ℝ → Prop)
    (hit : ∃ z ∈ (f.map Complex.ofRealHom).roots, region ‖z‖) :
    0 < rootCount (f.map Complex.ofRealHom) region := by
  classical
  let F := f.map Complex.ofRealHom
  have nz : F ≠ 0 := (fm.map _).ne_zero
  obtain ⟨z,hz,reg⟩ := hit
  have exists_upper : ∃ w ∈ F.roots, region ‖w‖ ∧ 0 ≤ w.im := by
    by_cases sign : 0 ≤ z.im
    · exact ⟨z,hz,reg,sign⟩
    have bridge (w : ℂ) : F.IsRoot w ↔ aeval w f = 0 := by
      change (f.map (algebraMap ℝ ℂ)).eval w = 0 ↔ _
      rw [eval_map_algebraMap]
    have van : aeval z f = 0 := (bridge z).mp ((mem_roots nz).mp hz)
    have con : aeval (conj z) f = 0 := by rw [aeval_conj,van,map_zero]
    exact ⟨conj z,(mem_roots nz).mpr ((bridge _).mpr con),by simpa using reg,by simp; linarith⟩
  obtain ⟨w,hw,h⟩ := exists_upper
  apply Multiset.card_pos.mpr
  intro eq
  have inside : w ∈ F.roots.filter (fun z => region ‖z‖ ∧ 0 ≤ z.im) := Multiset.mem_filter.mpr ⟨hw,h⟩
  rw [eq] at inside
  exact Multiset.notMem_zero _ inside

/-- Each nonreciprocal normalized real factor consumes a conjugate class
strictly inside and another strictly outside the unit circle. -/
theorem two_root_obstruction {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) :
    (Binary f ∧ Binary g) ∨
      (2 ≤ rootCount ((f*g).map Complex.ofRealHom) (· < 1) ∧
       2 ≤ rootCount ((f*g).map Complex.ofRealHom) (1 < ·)) := by
  by_cases fs : f.reverse = f
  · exact Or.inl (binary_of_reciprocal fm gm fc gc fp gp bin fs)
  by_cases gs : g.reverse = g
  · exact Or.inl (binary_of_reciprocal gm fm gc fc gp fp (mul_comm f g ▸ bin) gs).symm
  obtain ⟨fi,fo⟩ := both_sides f fm fc fs
  obtain ⟨gi,go⟩ := both_sides g gm gc gs
  have a := real_rootCount_pos fm (· < 1) fi
  have b := real_rootCount_pos gm (· < 1) gi
  have c := real_rootCount_pos fm (1 < ·) fo
  have d := real_rootCount_pos gm (1 < ·) go
  right
  simp only [Polynomial.map_mul,rootCount_mul _ _ (fm.map _).ne_zero (gm.map _).ne_zero]
  exact ⟨by omega,by omega⟩

open Green28 Green28UniformSums Green28PrimitiveSupport

/-- Green 28 holds when the shifted output mask has at most one root in
either open radial region in the closed upper half-plane, counting multiplicity. -/
theorem uniform_of_root_count {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne)
    (few : let H := (outputMask S ne).map (Int.castRingHom ℂ)
           rootCount H (· < 1) ≤ 1 ∨ rootCount H (1 < ·) ≤ 1) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  obtain ⟨f,g,_,_,_,_,pf,pg,fm,gm,_,_,fc,gc,eq⟩ := mask_factorization ne sum
  have bin := ((pf.mul pg).uniform_iff (fm.mul gm)).mp flat
  obtain fair|bad := two_root_obstruction fm gm fc gc pf.nonneg pg.nonneg bin
  · exact ⟨(pf.uniform_iff fm).mpr fair.1,(pg.uniform_iff gm).mpr fair.2⟩
  · rw [eq,Polynomial.map_map,RingHom.ext_int (Complex.ofRealHom.comp (Int.castRingHom ℝ)) (Int.castRingHom ℂ)] at bad
    dsimp only at few
    omega

private lemma rootCount_le_of_dvd {H L : ℂ[X]} (nz : L ≠ 0) (dvd : H ∣ L) (r : ℝ → Prop) :
    rootCount H r ≤ rootCount L r := by
  obtain ⟨K,rfl⟩ := dvd
  obtain ⟨hn,kn⟩ := mul_ne_zero_iff.mp nz
  rw [rootCount_mul _ _ hn kn]
  omega

private lemma both_counts_le_degree (R : ℂ[X]) :
    rootCount R (· < 1)+rootCount R (1 < ·) ≤ R.natDegree := by
  classical
  let a (z : ℂ) := ‖z‖ < 1 ∧ 0 ≤ z.im
  let b (z : ℂ) := 1 < ‖z‖ ∧ 0 ≤ z.im
  have empty : R.roots.filter (fun z => a z ∧ b z) = 0 :=
    Multiset.filter_eq_nil.mpr (fun _ _ h => h.1.1.not_gt h.2.1)
  have le := Multiset.card_le_card (Multiset.filter_le (fun z => a z ∨ b z) R.roots)
  rw [show R.roots.filter (fun z => a z ∨ b z) = R.roots.filter a + R.roots.filter b by
    rw [Multiset.filter_add_filter,empty,add_zero]] at le
  exact (Multiset.card_add .. ▸ le).trans (Polynomial.card_roots' R)

/-- A root of a power of a roots-of-unity polynomial has modulus one. -/
theorem norm_of_cyclotomic_part {m e : ℕ} (pos : 0 < m) {z : ℂ}
    (hz : z ∈ (((X:ℂ[X])^m-1)^e).roots) : ‖z‖=1 := by
  have nz : (X:ℂ[X])^m-1 ≠ 0 := by simpa using X_pow_sub_C_ne_zero pos (1:ℂ)
  have van := (mem_roots (pow_ne_zero e nz)).mp hz
  rw [IsRoot.def,eval_pow,eval_sub,eval_pow,eval_X,eval_one] at van
  have unity := congrArg (fun t : ℂ => ‖t‖) (sub_eq_zero.mp (eq_zero_of_pow_eq_zero van))
  rw [norm_pow,norm_one,pow_eq_one_iff_of_nonneg (norm_nonneg _) pos.ne'] at unity
  exact unity

private lemma count_cyclotomic_part (m e : ℕ) (pos : 0 < m) (r : ℝ → Prop) (off : ¬r 1) :
    rootCount (((X:ℂ[X])^m-1)^e) r = 0 := by
  classical
  apply Multiset.card_eq_zero.mpr
  apply Multiset.filter_eq_nil.mpr
  intro z hz h
  exact off (norm_of_cyclotomic_part pos hz ▸ h.1)

/-- An integer-polynomial divisibility certificate covers arbitrary cyclotomic
degrees and multiplicities after removal of a residual factor of degree at most three. -/
theorem uniform_of_cubic_residual {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (R : ℤ[X]) (nz : R ≠ 0)
    (low : R.natDegree ≤ 3) (m e : ℕ) (mp : 0 < m)
    (dvd : outputMask S ne ∣ R*(X^m-1)^e) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  let R' := R.map (Int.castRingHom ℂ)
  have rn : R' ≠ 0 := (Polynomial.map_ne_zero_iff (Int.cast_injective (α:=ℂ))).mpr nz
  have un : (X:ℂ[X])^m-1 ≠ 0 := by simpa using X_pow_sub_C_ne_zero mp (1:ℂ)
  have dv : (outputMask S ne).map (Int.castRingHom ℂ) ∣ R'*((X:ℂ[X])^m-1)^e := by
    simpa only [R',Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,map_X,Polynomial.map_one] using
      Polynomial.map_dvd (Int.castRingHom ℂ) dvd
  have bound (r : ℝ → Prop) (off : ¬r 1) :
      rootCount ((outputMask S ne).map (Int.castRingHom ℂ)) r ≤ rootCount R' r := by
    have h := rootCount_le_of_dvd (mul_ne_zero rn (pow_ne_zero e un)) dv r
    simpa only [rootCount_mul _ _ rn (pow_ne_zero e un),count_cyclotomic_part m e mp r off,add_zero] using h
  have i := bound (· < 1) (lt_irrefl _)
  have o := bound (1 < ·) (lt_irrefl _)
  have total := both_counts_le_degree R'
  have degree : R'.natDegree ≤ 3 := natDegree_map_le.trans low
  apply uniform_of_root_count ne sum
  dsimp only
  omega

/-- Two identical translated blocks with a common mask of degree at most three
give a certificate at every positive shift for which the product is binary. -/
theorem uniform_of_two_cubic_blocks {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (R : ℤ[X]) (nz : R ≠ 0)
    (low : R.natDegree ≤ 3) (k : ℕ) (pos : 0 < k)
    (mask : outputMask S ne = R*(1+X^k)) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  apply uniform_of_cubic_residual ne sum R nz low (k*2) 1 (by omega)
  rw [mask,pow_one,pow_mul]
  exact ⟨X^k-1,by ring⟩

#print axioms reverse_eq_scaled_of_unit_roots
#print axioms norm_of_cyclotomic_part
#print axioms reciprocal_of_unit_roots
#print axioms coeff_mul_middle_mem
#print axioms reverse_coeff_eq_zero_or
#print axioms binary_of_reciprocal
#print axioms two_root_obstruction
#print axioms uniform_of_root_count
#print axioms uniform_of_cubic_residual
#print axioms uniform_of_two_cubic_blocks

end Green28RootLocation
