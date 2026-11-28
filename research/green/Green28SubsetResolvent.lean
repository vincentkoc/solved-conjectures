import Green28PrimitiveSupport
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.FieldTheory.Finite.Extension

/-! Exact tests for prescribed constant terms of factors of integer polynomials. -/

namespace Green28SubsetResolvent
open Finset

/-- The product indexed by the choices of exactly `k` signed roots.
Repeating a root in different positions preserves its multiplicity. -/
noncomputable def subsetProduct (d k : ℕ) (z : ℤ) : MvPolynomial (Fin d) ℤ :=
  ∏ U ∈ (univ : Finset (Fin d)).powersetCard k, (MvPolynomial.C z - ∏ i ∈ U, MvPolynomial.X i)

theorem subsetProduct_symmetric (d k : ℕ) (z : ℤ) : (subsetProduct d k z).IsSymmetric := by
  intro e
  let T := (univ : Finset (Fin d)).powersetCard k
  calc
    MvPolynomial.rename e (subsetProduct d k z) =
        ∏ U ∈ T, (MvPolynomial.C z - ∏ i ∈ U, MvPolynomial.X (e i)) := by
      simp [subsetProduct,T]
    _ = ∏ U ∈ ((univ : Finset (Fin d)).map e.toEmbedding).powersetCard k,
        (MvPolynomial.C z - ∏ i ∈ U, MvPolynomial.X i) := by
      rw [powersetCard_map,Finset.prod_map]
      apply prod_congr rfl
      intro U _
      change _ = MvPolynomial.C z - ∏ i ∈ U.map e.toEmbedding, MvPolynomial.X i
      rw [Finset.prod_map]
      rfl
    _ = subsetProduct d k z := by rw [map_univ_equiv];rfl

/-- Express the symmetric product in the elementary symmetric functions. -/
noncomputable def inCoefficients (d k : ℕ) (z : ℤ) : MvPolynomial (Fin d) ℤ :=
  (MvPolynomial.esymmAlgEquiv (Fin d) ℤ (Fintype.card_fin d)).symm
    ⟨subsetProduct d k z,subsetProduct_symmetric d k z⟩

theorem elementary_expansion (d k : ℕ) (z : ℤ) :
    MvPolynomial.aeval (fun i : Fin d => MvPolynomial.esymm (Fin d) ℤ (i+1:ℕ))
      (inCoefficients d k z) = subsetProduct d k z := by
  have eq := (MvPolynomial.esymmAlgEquiv (Fin d) ℤ (Fintype.card_fin d)).apply_symm_apply
    ⟨subsetProduct d k z,subsetProduct_symmetric d k z⟩
  exact (MvPolynomial.esymmAlgHom_apply _).symm.trans (congrArg Subtype.val eq)

open Polynomial

/-- An integer computed mathematically from the top coefficients of the mask. -/
noncomputable def resolventValue (H : ℤ[X]) (d k : ℕ) (z : ℤ) : ℤ :=
  MvPolynomial.aeval (fun i : Fin d => H.coeff (d-(i.val+1))) (inCoefficients d k z)

/-- In any splitting field, this same integer is the product of the
differences between the prescribed constant and the signed root products. -/
theorem value_in_splitting {K : Type*} [Field K] {H : ℤ[X]} {d : ℕ} (k : ℕ) (z : ℤ)
    (b : Fin d → K) (split : H.map (Int.castRingHom K) = ∏ i, (X+C (b i))) :
    (resolventValue H d k z : K) =
      ∏ U ∈ (univ : Finset (Fin d)).powersetCard k, ((z:K) - ∏ i ∈ U, b i) := by
  let a := fun i : Fin d => H.coeff (d-(i.val+1))
  have vieta (i : Fin d) : MvPolynomial.aeval b (MvPolynomial.esymm (Fin d) ℤ (i.val+1)) =
      (a i : K) := by
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    change _ = (Int.castRingHom K) (H.coeff (d-(i.val+1)))
    rw [←coeff_map,split]
    change _ = ((univ.val.map fun j : Fin d => X+C (b j)).prod).coeff _
    rw [Multiset.prod_X_add_C_coeff' _ _ (by simp)]
    congr 1
    simp only [Finset.card_val,card_univ,Fintype.card_fin]
    omega
  have eq := congrArg (MvPolynomial.aeval b) (elementary_expansion d k z)
  rw [MvPolynomial.comp_aeval_apply] at eq
  simp only [vieta,subsetProduct,map_prod,map_sub,MvPolynomial.aeval_X,eq_intCast,map_intCast] at eq
  change (Algebra.ofId ℤ K) (MvPolynomial.aeval a (inCoefficients d k z)) = _
  rw [MvPolynomial.comp_aeval_apply]
  exact eq

/-- Number the signed roots with multiplicity when the polynomial splits. -/
theorem signed_roots {K : Type*} [Field K] {F : K[X]} (mon : F.Monic) (spl : F.Splits)
    (d : ℕ) (deg : F.natDegree = d) : ∃ b : Fin d → K, F = ∏ i, (X + C (b i)) := by
  classical
  let l := F.roots.toList
  have len : l.length = d := by
    rw [show l.length = F.roots.card from Multiset.length_toList _,
      spl.natDegree_eq_card_roots.symm,deg]
  subst d
  rw [←len]
  refine ⟨fun i => -l[i.val],?_⟩
  rw [show (∏ i : Fin l.length, (X+C (-l[i.val]))) = (l.map (fun x => (X-C x))).prod by
    simpa only [map_neg,←sub_eq_add_neg] using Fin.prod_univ_fun_getElem l (fun x => (X-C x)) ]
  simpa only [l,←Multiset.prod_coe,←Multiset.map_coe,Multiset.coe_toList] using
    spl.eq_prod_roots_of_monic mon

/-- Roots are counted with multiplicity. In every splitting
field the vanishing of this integer is equivalent to the specified factor. -/
theorem value_zero_iff_of_splits {K : Type*} [Field K] {H : ℤ[X]} (hm : H.Monic)
    (spl : (H.map (Int.castRingHom K)).Splits)
    (k : ℕ) (z : ℤ) : (resolventValue H H.natDegree k z : K) = 0 ↔
      ∃ f : K[X], f.Monic ∧ f ∣ H.map (Int.castRingHom K) ∧ f.natDegree = k ∧ f.coeff 0 = (z:K) := by
  classical
  let F := H.map (Int.castRingHom K)
  have mon : F.Monic := hm.map _
  obtain ⟨b,split⟩ := signed_roots mon spl H.natDegree (hm.natDegree_map _)
  rw [value_in_splitting k z b split,Finset.prod_eq_zero_iff]
  have const (U : Finset (Fin H.natDegree)) : (∏ i ∈ U, (X+C (b i))).coeff 0 = ∏ i ∈ U, b i := by
    simp [coeff_zero_prod]
  have degree (U : Finset (Fin H.natDegree)) : (∏ i ∈ U, (X+C (b i))).natDegree = U.card := by
    simpa only [map_neg,sub_neg_eq_add] using natDegree_finsetProd_X_sub_C_eq_card U (fun i => -b i)
  constructor
  · rintro ⟨U,hu,zero⟩
    refine ⟨_,monic_prod_of_monic U _ (fun i _ => monic_X_add_C (b i)),?_,(degree U).trans (mem_powersetCard.mp hu).2,
      (const U).trans (sub_eq_zero.mp zero).symm⟩
    change _ ∣ F
    rw [split]
    exact Finset.prod_dvd_prod_of_subset U univ _ (subset_univ U)
  · rintro ⟨f,fm,⟨g,prod⟩,deg,zero⟩
    have gm := fm.of_mul_monic_left (prod ▸ hm.map (Int.castRingHom K))
    have eq : f*g = ∏ i, (X-C (-b i)) := by simpa only [map_neg,sub_neg_eq_add] using prod.symm.trans split
    obtain ⟨U,sub,uf⟩ := Green28PrimitiveSupport.divisor_subproduct (fun i => -b i) univ fm gm eq
    simp only [map_neg,sub_neg_eq_add] at uf
    rw [uf,degree] at deg
    rw [uf,const] at zero
    exact ⟨U,mem_powersetCard.mpr ⟨sub,deg⟩,sub_eq_zero.mpr zero.symm⟩

/-- The degree and constant-term criterion over an algebraically closed field. -/
theorem value_zero_iff {K : Type*} [Field K] [IsAlgClosed K] {H : ℤ[X]} (hm : H.Monic)
    (k : ℕ) (z : ℤ) : (resolventValue H H.natDegree k z : K) = 0 ↔
      ∃ f : K[X], f.Monic ∧ f ∣ H.map (Int.castRingHom K) ∧ f.natDegree = k ∧ f.coeff 0 = (z:K) :=
  value_zero_iff_of_splits hm (IsAlgClosed.splits _) k z

/-- Outside the prime divisors of a nonzero resolvent the complex and
modular tests for this degree and constant term agree. -/
theorem factors_at_large_prime {H : ℤ[X]} (hm : H.Monic) (k : ℕ) (z : ℤ)
    {p : ℕ} [Fact p.Prime] (big : (resolventValue H H.natDegree k z).natAbs < p) :
    (∃ f : (AlgebraicClosure (ZMod p))[X], f.Monic ∧ f ∣ H.map (Int.castRingHom _) ∧
      f.natDegree = k ∧ f.coeff 0 = (z:AlgebraicClosure (ZMod p))) ↔
    (∃ f : ℂ[X], f.Monic ∧ f ∣ H.map (Int.castRingHom ℂ) ∧ f.natDegree = k ∧ f.coeff 0 = (z:ℂ)) := by
  rw [←value_zero_iff hm,←value_zero_iff hm,CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p,Int.cast_eq_zero]
  constructor
  · intro dvd
    by_contra ne
    have bound := Int.natAbs_le_of_dvd_ne_zero dvd ne
    simpa using (not_le_of_gt big bound)
  · intro eq;rw [eq];exact dvd_zero _

private theorem all_subset_products {d k : ℕ} (hk : 0 < k) (w : Fin d → ℝ) :
    (∏ U ∈ (univ : Finset (Fin d)).powersetCard k, ∏ i ∈ U, w i) =
      (∏ i, w i)^((d-1).choose (k-1)) := by
  classical
  let T := (univ : Finset (Fin d)).powersetCard k
  have row (U : Finset (Fin d)) : (∏ i ∈ U, w i) = ∏ i, (if i ∈ U then w i else 1) := by
    rw [←prod_filter];simp
  have col (i : Fin d) : (T.filter (fun U => i ∈ U)).card = (d-1).choose (k-1) := by
    simpa only [T,singleton_subset_iff,card_singleton,card_univ,Fintype.card_fin] using
      card_filter_powersetCard_subset {i} univ k (subset_univ _) (by simpa using (show 1 ≤ k by omega))
  simp_rw [row]
  rw [prod_comm,←Finset.prod_pow]
  apply prod_congr rfl
  intro i _
  rw [←prod_filter,prod_const,col];simp

/-- A bound using the Mahler measure. Each signed root occurs in exactly
`choose (d-1) (k-1)` of the factors in the product. -/
theorem value_bound_mahler {H : ℤ[X]} (hm : H.Monic) {k : ℕ} (hk : 0 < k) (z : ℤ) :
    ((resolventValue H H.natDegree k z).natAbs:ℝ) ≤
      ((z.natAbs:ℝ)+1)^(H.natDegree.choose k) *
        (H.map (Int.castRingHom ℂ)).mahlerMeasure^((H.natDegree-1).choose (k-1)) := by
  classical
  let F := H.map (Int.castRingHom ℂ)
  let d := H.natDegree
  obtain ⟨b,split⟩ := signed_roots (hm.map (Int.castRingHom ℂ)) (IsAlgClosed.splits _) d (hm.natDegree_map _)
  let w := fun i => max 1 ‖b i‖
  let T := (univ : Finset (Fin d)).powersetCard k
  have castnorm (v : ℤ) : ‖(v:ℂ)‖ = (v.natAbs:ℝ) := by
    rw [norm_intCast_eq_abs_mul_norm_one];simp
  have prodM : (∏ i, w i) = F.mahlerMeasure := by
    change _ = (H.map (Int.castRingHom ℂ)).mahlerMeasure
    rw [split]
    simp only [Finset.prod,Polynomial.prod_mahlerMeasure_eq_mahlerMeasure_prod,Multiset.map_map,
      Function.comp_def,mahlerMeasure_X_add_C,w]
  have bound (U : Finset (Fin d)) :
      ‖(z:ℂ)-∏ i ∈ U, b i‖ ≤ ((z.natAbs:ℝ)+1)*∏ i ∈ U,w i := by
    have one : 1 ≤ ∏ i ∈ U, w i := Finset.one_le_prod (fun i _ => le_max_left _ _)
    have bnd : ‖∏ i ∈ U, b i‖ ≤ ∏ i ∈ U, w i := by
      rw [norm_prod];apply prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => le_max_right _ _)
    calc
      _ ≤ ‖(z:ℂ)‖+‖∏ i ∈ U, b i‖ := norm_sub_le _ _
      _ ≤ _ := by rw [castnorm,add_mul,one_mul];nlinarith [mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α:=ℝ) z.natAbs)]
  rw [←castnorm,value_in_splitting k z b split,norm_prod]
  apply (prod_le_prod (fun _ _ => norm_nonneg _) (fun U _ => bound U)).trans_eq
  rw [Finset.prod_mul_distrib,prod_const,card_powersetCard,card_univ,Fintype.card_fin,all_subset_products hk,prodM]

/-- This common extension degree works for all polynomials of degree at most `d` over the prime field. -/
def extensionDegree (d : ℕ) : ℕ := (range d).lcm (fun i => i+1)

/-- All irreducible factors split over a finite field of extension degree
divisible by each of their degrees. This also handles repeated factors. -/
theorem finite_splits {p m : ℕ} [Fact p.Prime] (pos : m ≠ 0) (h : (ZMod p)[X])
    (divides : ∀ q : (ZMod p)[X], Irreducible q → q ∣ h → q.natDegree ∣ m) :
    (h.map (algebraMap (ZMod p) (GaloisField p m))).Splits := by
  classical
  let K := GaloisField p m
  let φ := algebraMap (ZMod p) K
  have full : ((X^((Nat.card (ZMod p))^m)-X : (ZMod p)[X]).map φ).Splits := by
    rw [Nat.card_eq_fintype_card,ZMod.card,←GaloisField.card p m pos]
    exact FiniteField.splits_X_pow_nat_card_sub_X _
  have nz : X^((Nat.card (ZMod p))^m)-X ≠ (0 : (ZMod p)[X]) :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero _ pos Finite.one_lt_card
  induction h using WfDvdMonoid.induction_on_irreducible with
  | zero => simp
  | unit u hu => exact (hu.map (Polynomial.mapRingHom φ)).splits
  | mul a i _ prime ih =>
    rw [Polynomial.map_mul]
    apply Splits.mul
    · exact full.of_dvd (map_ne_zero nz) (Polynomial.map_dvd φ (prime.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp
        (divides i prime (dvd_mul_right i a))))
    · exact ih (fun q irr dvd => divides q irr (dvd.trans (dvd_mul_left a i)))

/-- The same finite field works for every degree at most `d`. -/
theorem splits_over_common_field {p : ℕ} [Fact p.Prime] {h : (ZMod p)[X]} (nz : h ≠ 0) (d : ℕ)
    (lower : h.natDegree ≤ d) :
    (h.map (algebraMap (ZMod p) (GaloisField p (extensionDegree d)))).Splits := by
  apply finite_splits (Finset.lcm_ne_zero_iff.mpr (by intros;omega))
  intro q irr dvd
  have pos := irr.natDegree_pos
  have cap := (natDegree_le_of_dvd dvd nz).trans lower
  obtain ⟨j,eq⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  rw [eq]
  exact Finset.dvd_lcm (f:=fun i : ℕ => i+1) (mem_range.mpr (by omega))

/-- A monic factor of a specified degree and constant term over `K`. -/
def HasFactor (K : Type*) [Field K] (H : ℤ[X]) (k : ℕ) (z : ℤ) : Prop :=
  ∃ f : K[X], f.Monic ∧ f ∣ H.map (Int.castRingHom K) ∧ f.natDegree = k ∧ f.coeff 0 = (z:K)

/-- An exact finite-field test for the prime divisors of the integer resolvent.
The extension is the same for every requested width and constant term. -/
theorem finite_factor_iff_dvd {H : ℤ[X]} (hm : H.Monic) (k : ℕ) (z : ℤ) (p : ℕ) [Fact p.Prime] :
    HasFactor (GaloisField p (extensionDegree H.natDegree)) H k z ↔
      (p:ℤ) ∣ resolventValue H H.natDegree k z := by
  let K := GaloisField p (extensionDegree H.natDegree)
  have spl : (H.map (Int.castRingHom K)).Splits := by
    have h := splits_over_common_field ((hm.map (Int.castRingHom (ZMod p))).ne_zero) H.natDegree
      (hm.natDegree_map _).le
    simpa only [Polynomial.map_map,RingHom.ext_int _ (Int.castRingHom K)] using h
  exact (value_zero_iff_of_splits hm spl k z).symm.trans (CharP.intCast_eq_zero_iff K p _)

/-- Every prime larger than the absolute integer resolvent gives exactly
the same answer in this specified finite field as over the complex numbers. -/
theorem finite_factor_iff_complex {H : ℤ[X]} (hm : H.Monic) (k : ℕ) (z : ℤ) {p : ℕ} [Fact p.Prime]
    (big : (resolventValue H H.natDegree k z).natAbs < p) :
    HasFactor (GaloisField p (extensionDegree H.natDegree)) H k z ↔ HasFactor ℂ H k z := by
  rw [finite_factor_iff_dvd hm,←CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p,
    value_zero_iff hm]
  exact factors_at_large_prime hm k z big

open Green28PrimitiveSupport

private theorem mask_coefficient (S : Finset ℤ) (ne : S.Nonempty) (j : ℕ) :
    (outputMask S ne).coeff j = if j ∈ S.image (fun z => (z-S.min' ne).toNat) then 1 else 0 := by
  classical
  simp only [outputMask,finsetSum_coeff,coeff_monomial,sum_ite_eq']

theorem mask_monic (S : Finset ℤ) (ne : S.Nonempty) : (outputMask S ne).Monic := by
  classical
  let H := outputMask S ne
  have nonzero : H ≠ 0 := by
    have inside : 0 ∈ S.image (fun z => (z-S.min' ne).toNat) :=
      mem_image.mpr ⟨S.min' ne,S.min'_mem ne,by simp⟩
    intro empty
    have zero := mask_coefficient S ne 0
    change H.coeff 0 = _ at zero
    simp [empty,inside] at zero
  have lead := mask_coefficient S ne H.natDegree
  change H.coeff H.natDegree = _ at lead
  rw [coeff_natDegree] at lead
  split at lead
  · exact lead
  · exact (nonzero (leadingCoeff_eq_zero.mp lead)).elim

/-- The spectral bound for a shifted output mask depends only on its number
of occupied sites and its degree. Square both sides to keep the test integral. -/
theorem mask_value_bound (S : Finset ℤ) (ne : S.Nonempty) {k : ℕ} (hk : 0 < k) :
    let H := outputMask S ne
    (resolventValue H H.natDegree k 1).natAbs^2 ≤
      4^(H.natDegree.choose k) * S.card^((H.natDegree-1).choose (k-1)) := by
  classical
  let H := outputMask S ne
  let F := H.map (Int.castRingHom ℂ)
  let d := H.natDegree
  let v := fun z : ℤ => (z-S.min' ne).toNat
  change (resolventValue H d k 1).natAbs^2 ≤ 4^(d.choose k)*S.card^((d-1).choose (k-1))
  have coeff (j : ℕ) : F.coeff j = if j ∈ S.image v then 1 else 0 := by
    by_cases mem : j ∈ S.image v <;> simp [F,H,mask_coefficient,show S.image (fun z => (z-S.min' ne).toNat) = S.image v from rfl,mem]
  have sup : F.support = S.image v := by
    ext j
    by_cases inside : j ∈ S.image v <;> simp [mem_support_iff,coeff,inside]
  have iv : Set.InjOn v (S:Set ℤ) := by
    intro x hx y hy eq
    have h := S.min'_le _ hx
    have h' := S.min'_le _ hy
    dsimp only [v] at eq
    omega
  have energy : (∑ i ∈ F.support, ‖F.coeff i‖^2) = (S.card:ℝ) := by
    rw [sup]
    calc
      _ = ∑ _i ∈ S.image v, (1:ℝ) := sum_congr rfl fun j hj => by rw [coeff,if_pos hj,norm_one,one_pow]
      _ = _ := by simp [card_image_of_injOn iv]
  have mah := F.mahlerMeasure_le_sqrt_sum_sq_norm_coeff
  rw [energy] at mah
  have bd := value_bound_mahler (mask_monic S ne) hk 1
  change ((resolventValue H d k 1).natAbs:ℝ) ≤ _ at bd
  norm_num only [Int.natAbs_one,Nat.cast_one,one_add_one_eq_two] at bd
  have le : ((resolventValue H d k 1).natAbs:ℝ) ≤
      2^(d.choose k) * (Real.sqrt (S.card:ℝ))^((d-1).choose (k-1)) := by
    exact bd.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ F.mahlerMeasure_nonneg mah _) (by positivity))
  have sq := pow_le_pow_left₀ (Nat.cast_nonneg _) le 2
  rw [mul_pow,pow_right_comm (2:ℝ) _ 2,pow_right_comm (Real.sqrt (S.card:ℝ)) _ 2,
    Real.sq_sqrt (Nat.cast_nonneg _)] at sq
  norm_num only [show (2:ℝ)^2=4 by norm_num] at sq
  exact_mod_cast sq

/-- One prime and one finite field decide, simultaneously for every positive
width, whether the output mask has a complex monic factor with constant one. -/
theorem finite_test_for_mask (S : Finset ℤ) (ne : S.Nonempty) (p : ℕ) [Fact p.Prime]
    (large : let d := (outputMask S ne).natDegree
      4^(d.choose (d/2)) * S.card^((d-1).choose ((d-1)/2)) < p^2) {k : ℕ} (hk : 0 < k) :
    let H := outputMask S ne
    HasFactor (GaloisField p (extensionDegree H.natDegree)) H k 1 ↔ HasFactor ℂ H k 1 := by
  let H := outputMask S ne
  let d := H.natDegree
  apply finite_factor_iff_complex (mask_monic S ne)
  have bound := mask_value_bound S ne hk
  have wide : 4^(d.choose k) ≤ 4^(d.choose (d/2)) := Nat.pow_le_pow_right (by decide) (Nat.choose_le_middle _ _)
  have mass : S.card^((d-1).choose (k-1)) ≤ S.card^((d-1).choose ((d-1)/2)) :=
    Nat.pow_le_pow_right (card_pos.mpr ne) (Nat.choose_le_middle _ _)
  have sq := lt_of_le_of_lt (bound.trans (Nat.mul_le_mul wide mass)) large
  exact lt_of_not_ge (fun h => sq.not_ge (Nat.pow_le_pow_left h 2))

/-- A characteristic-zero monic factor survives the width and constant-term
test at every prime, including primes where extra factors appear. -/
theorem finite_factor_of_factor {L : Type*} [Field L] [CharZero L] {H : ℤ[X]} (hm : H.Monic)
    {k : ℕ} {z : ℤ} (factor : HasFactor L H k z) (p : ℕ) [Fact p.Prime] :
    HasFactor (GaloisField p (extensionDegree H.natDegree)) H k z := by
  obtain ⟨f,fm,fd,deg,one⟩ := factor
  let K := AlgebraicClosure L
  let e := algebraMap L K
  have dvd := Polynomial.map_dvd e fd
  rw [Polynomial.map_map,RingHom.ext_int (e.comp (Int.castRingHom L)) (Int.castRingHom K)] at dvd
  have zero := (value_zero_iff (K:=K) hm k z).mpr
    ⟨_,fm.map e,dvd,(fm.natDegree_map _).trans deg,by rw [coeff_map,one,map_intCast]⟩
  apply (finite_factor_iff_dvd hm k z p).mpr
  rw [(Int.cast_eq_zero.mp zero)]
  exact dvd_zero _

open Green28 Green28UniformSums Green28PrimitiveSupport

/-- Excluding every positive width below half of the output width in the
specified finite field forces a constant summand in the original laws.
One prime suffices for this implication with no lower bound on its size. -/
theorem pure_of_finite_test {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (p : ℕ) [Fact p.Prime]
    (exclude : let H := outputMask S ne
      ∀ k, 0 < k → 2*k < H.natDegree → ¬HasFactor (GaloisField p (extensionDegree H.natDegree)) H k 1) :
    (∃ x, P = PMF.pure x) ∨ (∃ y, Q = PMF.pure y) := by
  let H := outputMask S ne
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  obtain ⟨f,g,_,_,_,_,fp,gp,fm,gm,fw,gw,f0,g0,prod⟩ := mask_factorization ne sum
  by_cases hf : f.natDegree = 0
  · exact Or.inl (pure_of_width_zero pf (fw ▸ hf))
  by_cases hg : g.natDegree = 0
  · exact Or.inr (pure_of_width_zero qf (gw ▸ hg))
  have bin := ((fp.mul gp).uniform_iff (fm.mul gm)).mp flat
  have diff := Green28AlgebraicWidth.unequal_widths fm gm fp.nonneg gp.nonneg f0 g0 bin (Nat.pos_of_ne_zero hf)
  have mon := mask_monic S ne
  have widths : f.natDegree+g.natDegree = H.natDegree := by
    rw [←natDegree_mul fm.ne_zero gm.ne_zero,prod,mon.natDegree_map]
  rcases lt_or_gt_of_ne diff with lt|gt
  · exact False.elim (exclude f.natDegree (by omega) (by change 2*f.natDegree < H.natDegree;omega)
      (finite_factor_of_factor mon (L:=ℝ) ⟨f,fm,prod ▸ dvd_mul_right f g,rfl,by simpa using f0⟩ p))
  · exact False.elim (exclude g.natDegree (by omega) (by change 2*g.natDegree < H.natDegree;omega)
      (finite_factor_of_factor mon (L:=ℝ) ⟨g,gm,prod ▸ dvd_mul_left g f,rfl,by simpa using g0⟩ p))

/-- The Green 28 conclusion for any selected prime passing the finite exclusion test. -/
theorem uniform_of_finite_test {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (p : ℕ) [Fact p.Prime]
    (exclude : let H := outputMask S ne
      ∀ k, 0 < k → 2*k < H.natDegree → ¬HasFactor (GaloisField p (extensionDegree H.natDegree)) H k 1) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q :=
  uniform_of_pure_factor ⟨S,ne,sum⟩ (pure_of_finite_test ne sum p exclude)

/-- Across all output widths that could be the shorter nonconstant marginal,
exclusion over the complex numbers is equivalent to exclusion at a single
prime. The prime in the certificate may be smaller than the universal bound. -/
theorem complex_exclusion_iff_one_prime (S : Finset ℤ) (ne : S.Nonempty) :
    let H := outputMask S ne
    (∀ k, 0 < k → 2*k < H.natDegree → ¬HasFactor ℂ H k 1) ↔
      ∃ (p : ℕ) (_ : Fact p.Prime), ∀ k, 0 < k → 2*k < H.natDegree →
        ¬HasFactor (GaloisField p (extensionDegree H.natDegree)) H k 1 := by
  let H := outputMask S ne
  let d := H.natDegree
  let N := 4^(d.choose (d/2)) * S.card^((d-1).choose ((d-1)/2))
  constructor
  · intro none
    obtain ⟨p,big,prime⟩ := Nat.exists_infinite_primes (N+1)
    let _ : Fact p.Prime := ⟨prime⟩
    have sq : N < p^2 := by have := prime.two_le; nlinarith
    exact ⟨p,inferInstance,fun k pos short factor => none k pos short ((finite_test_for_mask S ne p sq pos).mp factor)⟩
  · rintro ⟨p,prime,none⟩ k pos short factor
    exact none k pos short (finite_factor_of_factor (mask_monic S ne) factor p)

/-- The quantification over factor polynomials can use fixed-length vectors.
A field with `q` elements gives exactly `q^(k+1)` vectors in this test. -/
theorem factor_iff_vectors {K : Type*} [Field K] (H : ℤ[X]) (k : ℕ) (z : ℤ) :
    HasFactor K H k z ↔ ∃ v : Fin (k+1) → K,
      let f : K[X] := ∑ i, monomial i.val (v i)
      f.Monic ∧ f ∣ H.map (Int.castRingHom K) ∧ f.natDegree = k ∧ f.coeff 0 = (z:K) := by
  constructor
  · rintro ⟨f,fm,dvd,degree,zero⟩
    refine ⟨fun i => f.coeff i.val,?_⟩
    have recover : (∑ i : Fin (k+1), monomial i.val (f.coeff i.val)) = f := by
      calc
        _ = ∑ j ∈ range (k+1), monomial j (f.coeff j) := Fin.sum_univ_eq_sum_range (fun j => monomial j (f.coeff j)) _
        _ = f := by rw [←degree];exact f.as_sum_range.symm
    simpa only [recover] using And.intro fm ⟨dvd,degree,zero⟩
  · rintro ⟨v,test⟩
    exact ⟨_,test⟩

#print axioms subsetProduct_symmetric
#print axioms elementary_expansion
#print axioms value_in_splitting
#print axioms signed_roots
#print axioms value_zero_iff_of_splits
#print axioms value_zero_iff
#print axioms factors_at_large_prime
#print axioms value_bound_mahler
#print axioms finite_splits
#print axioms splits_over_common_field
#print axioms finite_factor_iff_dvd
#print axioms finite_factor_iff_complex
#print axioms mask_monic
#print axioms mask_value_bound
#print axioms finite_test_for_mask
#print axioms finite_factor_of_factor
#print axioms pure_of_finite_test
#print axioms uniform_of_finite_test
#print axioms complex_exclusion_iff_one_prime
#print axioms factor_iff_vectors
end Green28SubsetResolvent
