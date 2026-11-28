import Green28AlgebraicWidth
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.FieldTheory.Finite.GaloisField

/-! Primitive binary support polynomials for independent integer sums. -/

namespace Green28PrimitiveSupport

open Polynomial Finset

/-- A monic divisor of a split product selects a subfamily of its linear factors. -/
theorem divisor_subproduct {ι K : Type*} [Field K] (a : ι → K) (S : Finset ι)
    {f g : K[X]} (fm : f.Monic) (gm : g.Monic) (eq : f*g=∏ i ∈ S, (X-C (a i))) :
    ∃ U⊆S, f=∏ i ∈ U, (X-C (a i)) := by
  classical
  induction S using Finset.induction_on generalizing f g with
  | empty =>
    have h : f.natDegree+g.natDegree=0 := by
      rw [←natDegree_mul fm.ne_zero gm.ne_zero,eq]; simp
    have zero : f.natDegree=0 := by omega
    have val := fm.coeff_natDegree
    rw [zero] at val
    exact ⟨∅,Subset.rfl,by rw [eq_C_of_natDegree_eq_zero zero,val]; simp⟩
  | @insert j S fresh ih =>
    rw [prod_insert fresh] at eq
    let L : K[X] := X-C (a j)
    have lm : L.Monic := monic_X_sub_C _
    have dvd : L ∣ f*g := ⟨_,eq⟩
    rcases (prime_X_sub_C (a j)).dvd_mul.mp dvd with h|h
    · obtain ⟨t,ht⟩ := h
      have tm : t.Monic := lm.of_mul_monic_left (ht ▸ fm)
      have small : t*g=∏ i ∈ S, (X-C (a i)) := by
        apply mul_left_cancel₀ lm.ne_zero
        rw [←mul_assoc,show L*t=f from ht.symm]
        exact eq
      obtain ⟨U,sub,fe⟩ := ih tm gm small
      exact ⟨insert j U,Finset.insert_subset_insert _ sub,by
        rw [prod_insert (fun hj => fresh (sub hj)),←fe,ht]⟩
    · obtain ⟨t,ht⟩ := h
      have tm : t.Monic := lm.of_mul_monic_left (ht ▸ gm)
      have small : f*t=∏ i ∈ S, (X-C (a i)) := by
        apply mul_left_cancel₀ lm.ne_zero
        calc L*(f*t)=f*(L*t) := by ring
             _=_ := by rw [←ht]; exact eq
      obtain ⟨U,sub,fe⟩ := ih fm tm small
      exact ⟨U,sub.trans (Finset.subset_insert _ _),fe⟩

private theorem binary_sum (d : ℕ) : (∑ i ∈ range d, 2^i)+1=2^d := by
  induction d with
  | zero => simp
  | succ d ih => rw [sum_range_succ,pow_succ]; omega

/-- No proper monic factor with constant term one can select roots from
a full binary Frobenius orbit of multiplicative order `2^d-1`. -/
theorem orbit_obstruction {K : Type*} [Field K] [CharP K 2] {α : K} {d : ℕ}
    (ord : IsPrimitiveRoot α (2^d-1)) {f g : K[X]} (fm : f.Monic) (gm : g.Monic)
    (f0 : f.coeff 0=1) (eq : f*g=∏ i ∈ range d, (X-C (α^(2^i)))) : f=1 ∨ g=1 := by
  classical
  obtain ⟨U,sub,fe⟩ := divisor_subproduct (fun i => α^(2^i)) (range d) fm gm eq
  by_cases empty : U=∅
  · exact Or.inl (by simpa [empty] using fe)
  by_cases full : U=range d
  · apply Or.inr
    apply mul_left_cancel₀ fm.ne_zero
    rw [mul_one,eq,←full,←fe]
  have v : (∏ i ∈ U, α^(2^i))=1 := by
    rw [coeff_zero_eq_eval_zero,fe,eval_prod] at f0
    simpa [CharTwo.neg_eq] using f0
  have multiple := ord.dvd_of_pow_eq_one (∑ i ∈ U, 2^i) (by simpa only [Finset.prod_pow_eq_pow_sum] using v)
  have pos : 0<∑ i ∈ U, 2^i := Finset.sum_pos (fun i _ => by positivity) (Finset.nonempty_iff_ne_empty.mpr empty)
  have lt : (∑ i ∈ U, 2^i)<∑ i ∈ range d, 2^i :=
    by
      obtain ⟨j,hj,out⟩ := Finset.not_subset.mp (show ¬range d⊆U from fun h => full (Finset.Subset.antisymm sub h))
      exact Finset.sum_lt_sum_of_subset sub hj out (by positivity) (fun _ _ _ => Nat.zero_le _)
  have le := Nat.le_of_dvd pos multiple
  have e := binary_sum d
  omega

/-- A root of full multiplicative order in the binary field of the output
degree. For a monic integer polynomial this is the usual primitive-polynomial
condition on its reduction modulo two. -/
def PrimitiveBinary (H : ℤ[X]) : Prop := 0<H.natDegree ∧
  ∃ α : GaloisField 2 H.natDegree, H.eval₂ (Int.castRingHom _) α=0 ∧
    IsPrimitiveRoot α (2^H.natDegree-1)

private theorem orbit_factorization {K : Type*} [Field K] [CharP K 2] {H : ℤ[X]} (hm : H.Monic)
    (hd : 2≤H.natDegree) {α : K} (root : H.eval₂ (Int.castRingHom _) α=0)
    (ord : IsPrimitiveRoot α (2^H.natDegree-1)) :
    H.map (Int.castRingHom K)=∏ i ∈ range H.natDegree, (X-C (α^(2^i))) := by
  classical
  let d := H.natDegree
  let r := fun i : ℕ => α^(2^i)
  have van (i : ℕ) : H.eval₂ (Int.castRingHom K) (r i)=0 := by
    induction i with
    | zero => simpa [r] using root
    | succ i ih =>
      have e := H.hom_eval₂ (Int.castRingHom K) (frobenius K 2) (r i)
      rw [ih,map_zero,RingHom.ext_int ((frobenius K 2).comp (Int.castRingHom K)) (Int.castRingHom K)] at e
      change H.eval₂ _ (α^(2^(i+1)))=0
      rw [show 2^(i+1)=2^i*2 by rw [pow_succ],pow_mul]
      exact e.symm
  have lim {i : ℕ} (hi : i<d) : 2^i<2^d-1 := by
    have a := Nat.pow_le_pow_right (by decide : 0<2) (show i≤d-1 by omega)
    have hi' : 1≤d-1 := by dsimp [d]; omega
    have b := Nat.pow_le_pow_right (by decide : 0<2) hi'
    have e : 2^d=2^(d-1)*2 := by conv_lhs => rw [show d=d-1+1 by omega,pow_succ]
    omega
  have inj : Set.InjOn r (range d:Set ℕ) := by
    intro i hi j hj e
    exact Nat.pow_right_injective (by decide : 2≤2) (ord.pow_inj (lim (mem_range.mp hi)) (lim (mem_range.mp hj)) e)
  let T := (range d).image r
  let p := H.map (Int.castRingHom K)
  have pm : p.Monic := hm.map _
  have dvd : (∏ z ∈ T, (X-C z)) ∣ p := by
    apply (Multiset.prod_X_sub_C_dvd_iff_le_roots pm.ne_zero T.val).mpr
    apply (Multiset.le_iff_subset T.nodup).mpr
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (show z∈T from hz)
    exact (Polynomial.mem_roots pm.ne_zero).mpr (by simpa only [IsRoot,p,eval_map] using van i)
  have e := Polynomial.eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic T _ (fun z _ => monic_X_sub_C z)) pm dvd
    (by rw [natDegree_finsetProd_X_sub_C_eq_card]; dsimp only [T]; rw [card_image_of_injOn inj,card_range]; exact (hm.natDegree_map _).le)
  simpa only [T,Finset.prod_image inj] using e

/-- Reduce algebraic integers in a characteristic-zero field to an algebraically
closed field of a chosen prime characteristic, using one homomorphism for all coefficients. -/
theorem with_prime_residue (L : Type) [Field L] [CharZero L] (p : ℕ) [prime : Fact p.Prime] {goal : Prop} (run : ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K],
    (integralClosure ℤ L →+* K) → goal) : goal := by
  classical
  let O := integralClosure ℤ L
  let P := RingHom.ker (Int.castRingHom (ZMod p))
  let _ : P.IsMaximal := RingHom.ker_isMaximal_of_surjective _ ZMod.intCast_surjective
  obtain ⟨J,jm,above⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := O) P
  let _ := jm
  let R := O ⧸ J
  let _ : Field R := Ideal.Quotient.field J
  have inP : (p:ℤ)∈P := by change ((p:ℤ):ZMod p)=0; simp
  have inJ : (p:O)∈J := by
    rw [(Ideal.liesOver_iff J P).mp above] at inP
    simpa only [Ideal.under,Ideal.mem_comap,map_natCast] using inP
  let _ : CharP R p := (CharP.charP_iff_prime_eq_zero prime.out).mpr (by
    change (p : O ⧸ J)=0
    simpa only [map_natCast] using (Ideal.Quotient.eq_zero_iff_mem (I := J)).mpr inJ)
  exact run (AlgebraicClosure R) ((algebraMap R _).comp (Ideal.Quotient.mk J))

private theorem coefficients_in_O (H : ℤ[X]) (hm : H.Monic) (f : ℝ[X]) (fm : f.Monic)
    (dvd : f ∣ H.map (Int.castRingHom ℝ)) : (f.coeffs:Set ℝ) ⊆ (integralClosure ℤ ℝ).toSubring := by
  intro x hx
  obtain ⟨i,_,rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
  exact isIntegral_coeff_of_dvd H f hm fm dvd i

/-- Any restriction on the degrees of monic factors with constant term one
that holds after reduction over algebraically closed fields of a fixed prime characteristic
also holds for monic real factors of the integer polynomial. -/
theorem degrees_of_prime_reduction (p : ℕ) [Fact p.Prime] (H : ℤ[X]) (hm : H.Monic) {f g : ℝ[X]}
    (fm : f.Monic) (gm : g.Monic) (f0 : f.coeff 0=1) (eq : f*g=H.map (Int.castRingHom ℝ))
    (D : ℕ → ℕ → Prop) (test : ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K]
      (F G : K[X]), F.Monic → G.Monic → F.coeff 0=1 → F*G=H.map (Int.castRingHom K) →
      D F.natDegree G.natDegree) : D f.natDegree g.natDegree := by
  classical
  let T := (integralClosure ℤ ℝ).toSubring
  let F := f.toSubring T (coefficients_in_O H hm f fm (eq ▸ dvd_mul_right f g))
  let G := g.toSubring T (coefficients_in_O H hm g gm (eq ▸ dvd_mul_left g f))
  have mF : F.Monic := (monic_toSubring _ _ _).mpr fm
  have mG : G.Monic := (monic_toSubring _ _ _).mpr gm
  have zF : F.coeff 0=1 := Subtype.ext (by change (F.coeff 0).1=1; simpa only [F,coeff_toSubring'] using f0)
  have product : F*G=H.map (Int.castRingHom T) := by
    apply Polynomial.map_injective T.subtype Subtype.val_injective
    rw [Polynomial.map_mul,Polynomial.map_map,RingHom.ext_int (T.subtype.comp _) (Int.castRingHom ℝ)]
    simpa only [F,G,map_toSubring] using eq
  apply with_prime_residue ℝ p
  intro K fld cp closed φ
  have prodK : F.map φ*G.map φ=H.map (Int.castRingHom K) := by
    rw [←Polynomial.map_mul,product,Polynomial.map_map,RingHom.ext_int (φ.comp _) (Int.castRingHom K)]
  have zero : (F.map φ).coeff 0=1 := by rw [coeff_map,zF,map_one]
  have h := test K (F.map φ) (G.map φ) (mF.map φ) (mG.map φ) zero prodK
  simpa only [mF.natDegree_map,mG.natDegree_map,F,G,natDegree_toSubring] using h

/-- Degree restrictions on monic normalized factors can be tested in characteristic two. -/
theorem degrees_of_binary_reduction (H : ℤ[X]) (hm : H.Monic) {f g : ℝ[X]}
    (fm : f.Monic) (gm : g.Monic) (f0 : f.coeff 0=1) (eq : f*g=H.map (Int.castRingHom ℝ))
    (D : ℕ → ℕ → Prop) (test : ∀ (K : Type) [Field K] [CharP K 2] [IsAlgClosed K]
      (F G : K[X]), F.Monic → G.Monic → F.coeff 0=1 → F*G=H.map (Int.castRingHom K) →
      D F.natDegree G.natDegree) : D f.natDegree g.natDegree :=
  degrees_of_prime_reduction 2 H hm fm gm f0 eq D test

/-- A primitive binary reduction prevents two positive-degree monic real
factors with constant terms one. The other coefficients may have either sign. -/
theorem no_unit_constant_split (H : ℤ[X]) (hm : H.Monic) (prim : PrimitiveBinary H)
    {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic) (f0 : f.coeff 0=1)
    (eq : f*g=H.map (Int.castRingHom ℝ)) : f.natDegree=0 ∨ g.natDegree=0 := by
  apply degrees_of_binary_reduction H hm fm gm f0 eq (fun i j => i=0 ∨ j=0)
  intro K fld cp closed F G mF mG zero product
  by_contra! bad
  have deg : F.natDegree+G.natDegree=H.natDegree := by
    rw [←natDegree_mul mF.ne_zero mG.ne_zero,product,hm.natDegree_map]
  have hd : 2≤H.natDegree := by omega
  let _ := ZMod.algebra K 2
  let emb : GaloisField 2 H.natDegree →ₐ[ZMod 2] K := IsAlgClosed.lift
  obtain ⟨_,α,root,ord⟩ := prim
  have r : H.eval₂ (Int.castRingHom K) (emb α)=0 := by
    have v := H.hom_eval₂ (Int.castRingHom _) emb.toRingHom α
    rw [root,map_zero,RingHom.ext_int (emb.toRingHom.comp _) (Int.castRingHom K)] at v
    exact v.symm
  rcases orbit_obstruction (ord.map_of_injective emb.injective) mF mG zero
      (product.trans (orbit_factorization hm hd r (ord.map_of_injective emb.injective))) with e|e
  · exact bad.1 (by simp [e])
  · exact bad.2 (by simp [e])

open Green28 Green28UniformSums Green28PolynomialReduction

/-- The integer 0–1 polynomial whose exponents are the occupied output sites
translated so that their minimum is zero. -/
noncomputable def outputMask (S : Finset ℤ) (ne : S.Nonempty) : ℤ[X] :=
  ∑ j ∈ S.image (fun z => (z-S.min' ne).toNat), monomial j 1

private theorem outputMask_coeff (S : Finset ℤ) (ne : S.Nonempty) (j : ℕ) :
    (outputMask S ne).coeff j=if S.min' ne+(j:ℤ)∈S then 1 else 0 := by
  classical
  have e : j∈S.image (fun z => (z-S.min' ne).toNat) ↔ S.min' ne+(j:ℤ)∈S := by
    constructor
    · rintro h
      obtain ⟨z,hz,ej⟩ := mem_image.mp h
      have := S.min'_le _ hz
      rwa [show S.min' ne+(j:ℤ)=z by omega]
    · intro h
      exact mem_image.mpr ⟨_,h,by omega⟩
  simp only [outputMask,finsetSum_coeff,coeff_monomial,sum_ite_eq',e]

/-- An integer law whose two support endpoints coincide is a point mass. -/
theorem pure_of_width_zero {P : PMF ℤ} (fin : P.support.Finite) (hw : Green28AlgebraicWidth.width P=0) :
    ∃ x, P=PMF.pure x := by
  classical
  let A := fin.toFinset
  have ne : A.Nonempty := fin.toFinset_nonempty.mpr P.support_nonempty
  let x := A.min' ne
  have e : (A.max' ne-x).toNat=0 := by
    simpa only [Green28AlgebraicWidth.width,dif_pos fin] using hw
  have all (z : ℤ) (hz : z∈P.support) : z=x := by
    have h := fin.mem_toFinset.mpr hz
    have m := A.min'_le _ h
    have M := A.le_max' _ h
    dsimp [x] at *
    omega
  have sing : P.support={x} := by
    ext z
    constructor
    · exact fun hz => all z hz
    · rintro rfl
      exact fin.mem_toFinset.mp (A.min'_mem ne)
  refine ⟨x,PMF.ext fun z => ?_⟩
  by_cases he : z=x
  · subst z
    simpa using (P.apply_eq_one_iff x).mpr sing
  · rw [(P.apply_eq_zero_iff z).mpr (by simpa [sing] using he),PMF.pure_apply]
    simp [he]

/-- The normalized marginal polynomials multiply to the shifted mask
of the actual output law. -/
theorem mask_factorization {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q=PMF.uniformOfFinset S ne) :
    ∃ (f g : ℝ[X]) (a b : ℤ) (s t : ℝ), Models P f a s ∧ Models Q g b t ∧
      f.Monic ∧ g.Monic ∧ f.natDegree=Green28AlgebraicWidth.width P ∧
      g.natDegree=Green28AlgebraicWidth.width Q ∧ f.coeff 0=1 ∧ g.coeff 0=1 ∧
      f*g=(outputMask S ne).map (Int.castRingHom ℝ) := by
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  obtain ⟨f,a,s,fp,fm,fw,fa⟩ := Green28AlgebraicWidth.chart P pf
  obtain ⟨g,b,t,gp,gm,gw,ga⟩ := Green28AlgebraicWidth.chart Q qf
  have model := fp.mul gp
  have bin := (model.uniform_iff (fm.mul gm)).mp flat
  obtain ⟨fc,gc⟩ := Green28AlgebraicWidth.endpoints fm gm fp.nonneg gp.nonneg fa ga bin
  have sumSupp : (indepSum P Q).support=(S:Set ℤ) := by rw [sum,PMF.support_uniformOfFinset]
  have occ (j : ℕ) : (f*g).coeff j≠0 ↔ a+b+(j:ℤ)∈S := by
    have coeff := model.coeff j
    change _ ↔ a+b+(j:ℤ)∈(S:Set ℤ)
    rw [←sumSupp,PMF.mem_support_iff]
    have nt := (indepSum P Q).apply_ne_top (a+b+j)
    have iff : ((indepSum P Q) (a+b+j)).toReal≠0 ↔ (indepSum P Q) (a+b+j)≠0 := by simp [ENNReal.toReal_ne_zero,nt]
    rw [←iff,coeff,mul_ne_zero_iff]
    simp [fp.pos.ne',gp.pos.ne']
  have head : a+b∈S := by simpa only [Nat.cast_zero,add_zero] using (occ 0).mp (by rw [mul_coeff_zero,fc,gc]; norm_num)
  have least : S.min' ne=a+b := by
    apply le_antisymm (S.min'_le _ head)
    by_contra! lt
    have hz := model.below _ lt
    have h := S.min'_mem ne
    exact ((indepSum P Q).mem_support_iff _ |>.mp (sumSupp ▸ h)) hz
  have product : f*g=(outputMask S ne).map (Int.castRingHom ℝ) := by
    ext j
    simp only [coeff_map,outputMask_coeff,least,←occ j]
    rcases bin j with h|h <;> simp [h]
  exact ⟨f,g,a,b,s,t,fp,gp,fm,gm,fw,gw,fc,gc,product⟩

/-- A real factor obstruction on the shifted mask forces a constant summand. -/
theorem pure_factor_of_mask {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q=PMF.uniformOfFinset S ne)
    (obstruction : (outputMask S ne).Monic → ∀ {f g : ℝ[X]}, f.Monic → g.Monic →
      f.coeff 0=1 → f*g=(outputMask S ne).map (Int.castRingHom ℝ) →
      f.natDegree=0 ∨ g.natDegree=0) :
    (∃ x, P=PMF.pure x) ∨ (∃ y, Q=PMF.pure y) := by
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  obtain ⟨f,g,_,_,_,_,_,_,fm,gm,fw,gw,fc,_,product⟩ := mask_factorization ne sum
  have mon : (outputMask S ne).Monic := monic_of_injective Int.cast_injective (product ▸ fm.mul gm)
  rcases obstruction mon fm gm fc product with h|h
  · exact Or.inl (pure_of_width_zero pf (fw ▸ h))
  · exact Or.inr (pure_of_width_zero qf (gw ▸ h))

/-- An output support primitive modulo two admits only a point-mass factor
in any representation of its uniform law as an independent sum. -/
theorem pure_factor_of_primitive {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q=PMF.uniformOfFinset S ne) (primitive : PrimitiveBinary (outputMask S ne)) :
    (∃ x, P=PMF.pure x) ∨ (∃ y, Q=PMF.pure y) := by
  exact pure_factor_of_mask ne sum fun mon => no_unit_constant_split _ mon primitive

private theorem pure_ratios (x : ℤ) : RationalRatios (PMF.pure x) := by
  intro z y hy
  have ey : y=x := (PMF.mem_support_pure_iff _ _).mp hy
  subst y
  by_cases eq : z=x
  · subst z; exact ⟨1,by simp⟩
  · exact ⟨0,by simp [PMF.pure_apply,eq]⟩

/-- A point-mass summand of a uniform sum forces both marginals to be uniform. -/
theorem uniform_of_pure_factor {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (pure : (∃ x, P=PMF.pure x) ∨ (∃ y, Q=PMF.pure y)) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  apply uniform_of_rational_ratios flat
  rcases pure with ⟨x,rfl⟩|⟨y,rfl⟩
  · exact Or.inl (pure_ratios x)
  · exact Or.inr (pure_ratios y)

theorem uniform_of_primitive {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q=PMF.uniformOfFinset S ne) (primitive : PrimitiveBinary (outputMask S ne)) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  exact uniform_of_pure_factor ⟨S,ne,sum⟩ (pure_factor_of_primitive ne sum primitive)

private theorem periodic_prod {M : Type*} [CommMonoid M] (u : ℕ → M) (d : ℕ) (period : u d=u 0) :
    ∏ i ∈ range d, u (i+1)=∏ i ∈ range d, u i := by
  cases d with
  | zero => simp
  | succ d => rw [prod_range_succ,prod_range_succ' u d,period]

/-- Lift the binary coefficients of a full product of Frobenius conjugates to
an integer support mask of the same width. The roots may repeat. -/
theorem exists_orbit_support (d : ℕ) (hd : 0<d) (α : GaloisField 2 d) (power : α^(2^d-1)=1) :
    ∃ (S : Finset ℤ) (ne : S.Nonempty), S.min' ne=0 ∧ (outputMask S ne).natDegree=d ∧
      (outputMask S ne).map (Int.castRingHom (GaloisField 2 d))=
        ∏ i∈range d, (X-C (α^(2^i))) := by
  classical
  let K := GaloisField 2 d
  let _ : NeZero d := ⟨hd.ne'⟩
  let r := fun i : ℕ => α^(2^i)
  let F : K[X] := ∏ i ∈ range d, (X-C (r i))
  have fm : F.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have fd : F.natDegree=d := by simp [F,natDegree_finsetProd_X_sub_C_eq_card]
  have period : r d=r 0 := by
    have pow := power
    have e : 2^d=(2^d-1)+1 := by have := Nat.two_pow_pos d; omega
    change α^2^d=α^2^0
    rw [e,pow_succ,pow]; simp
  have perm : F.map (frobenius K 2)=F := by
    rw [Polynomial.map_prod]
    have eq (i : ℕ) : (X-C (r i)).map (frobenius K 2)=X-C (r (i+1)) := by
      rw [Polynomial.map_sub,map_X,map_C]
      change X-C ((α^(2^i))^2)=X-C (α^2^(i+1))
      rw [pow_succ 2 i,pow_mul]
    simp_rw [eq]
    exact periodic_prod (fun i => X-C (r i)) d (by rw [period])
  have bit (i : ℕ) : F.coeff i=0 ∨ F.coeff i=1 := by
    have e := congrArg (fun p : K[X] => p.coeff i) perm
    change (F.map _).coeff i=F.coeff i at e
    rw [coeff_map] at e
    change (F.coeff i)^2=F.coeff i at e
    have zero : F.coeff i*(F.coeff i-1)=0 := by linear_combination e
    simpa [sub_eq_zero] using mul_eq_zero.mp zero
  have c0 : F.coeff 0=1 := by
    dsimp only [F]
    rw [coeff_zero_prod]
    simp only [coeff_sub,coeff_X_zero,coeff_C_zero,zero_sub,CharTwo.neg_eq]
    simp only [r,Finset.prod_pow_eq_pow_sum]
    have h := binary_sum d
    rw [show (∑ i ∈ range d, 2^i)=2^d-1 by omega]
    exact power
  let S := F.support.image (Nat.cast : ℕ → ℤ)
  have z : (0:ℤ)∈S := Finset.mem_image.mpr ⟨0,mem_support_iff.mpr (c0 ▸ one_ne_zero),by simp⟩
  let ne : S.Nonempty := ⟨0,z⟩
  have least : S.min' ne=0 := by
    apply le_antisymm (S.min'_le _ z)
    obtain ⟨j,_,e⟩ := Finset.mem_image.mp (show S.min' ne∈S from S.min'_mem ne)
    omega
  let H := outputMask S ne
  have mapped : H.map (Int.castRingHom K)=F := by
    ext i
    have mem : (i:ℤ)∈S ↔ i∈F.support := by simp [S]
    rw [coeff_map,outputMask_coeff,least,zero_add]
    rcases bit i with h|h <;> simp [mem,mem_support_iff,h]
  have mon : H.Monic := by
    have deg : H.natDegree=d := by
      have supp : H.support=F.support := by
        ext j
        have mem : (j:ℤ)∈S ↔ j∈F.support := by simp [S]
        simp only [mem_support_iff,H,outputMask_coeff,least,zero_add]
        rcases bit j with h|h <;> simp [mem,mem_support_iff,h]
      change H.support.max.unbotD 0=d
      rw [supp]
      exact fd
    have site : (d:ℤ)∈S := Finset.mem_image.mpr ⟨d,(congrArg (fun j => j∈F.support) fd).mp (F.natDegree_mem_support_of_nonzero fm.ne_zero),rfl⟩
    change H.coeff H.natDegree=1
    rw [deg,outputMask_coeff,least,zero_add,if_pos site]
  have deg : H.natDegree=d := by rw [←mon.natDegree_map (Int.castRingHom K),mapped,fd]
  exact ⟨S,ne,least,deg,mapped⟩

/-- Every positive degree occurs as the width of a primitive support mask. -/
theorem exists_primitive_support (d : ℕ) (hd : 0<d) :
    ∃ (S : Finset ℤ) (ne : S.Nonempty), S.min' ne=0 ∧ (outputMask S ne).natDegree=d ∧
      PrimitiveBinary (outputMask S ne) := by
  classical
  let K := GaloisField 2 d
  let _ : NeZero d := ⟨hd.ne'⟩
  obtain ⟨u,hu⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := Kˣ)).mp inferInstance
  let α : K := u
  have ord : IsPrimitiveRoot α (2^d-1) := IsPrimitiveRoot.iff_orderOf.mpr (by
    rw [show orderOf α=orderOf u from orderOf_units,hu,Nat.card_units,show Nat.card K=2^d from GaloisField.card 2 d hd.ne'])
  obtain ⟨S,ne,least,deg,mapped⟩ := exists_orbit_support d hd α ord.pow_eq_one
  refine ⟨S,ne,least,deg,?_⟩
  unfold PrimitiveBinary
  rw [deg]
  refine ⟨hd,α,?_,ord⟩
  rw [←eval_map,mapped,eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hd)
  simp

#print axioms pure_of_width_zero
#print axioms with_prime_residue
#print axioms degrees_of_prime_reduction
#print axioms degrees_of_binary_reduction
#print axioms exists_orbit_support
#print axioms orbit_obstruction
#print axioms no_unit_constant_split
#print axioms pure_factor_of_primitive
#print axioms uniform_of_primitive
#print axioms exists_primitive_support

end Green28PrimitiveSupport
