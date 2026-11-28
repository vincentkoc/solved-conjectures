import Green51SixPencilGeometry

/-! # The nine coefficient planes for four-dimensional affine spaces -/

open Green51GoldSix Green51BCHCompression Green51BCHOptimality Green51GoldForms Polynomial Finset
open scoped Pointwise
namespace Green51SixPencils
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

open Green51BCH

noncomputable def shiftCoefficients (d : Kˣ) : Submodule F K :=
  (coeffMap (K := K)).ker.comap (LinearMap.mulLeft F (d : K))

private theorem shift_dimension (m : Module.finrank F K=6) (d : Kˣ) :
    Module.finrank F (shiftCoefficients d)=2 := by
  let f := LinearMap.mulLeft F (d : K)
  have inj : Function.Injective f := fun _ _ e => mul_left_cancel₀ d.ne_zero e
  have sur := Finite.injective_iff_surjective.mp inj
  have image : (shiftCoefficients d).map f=coeffMap.ker :=
    Submodule.map_comap_eq_self (by rw [LinearMap.range_eq_top.mpr sur]; exact le_top)
  have eq := ( (shiftCoefficients d).equivMapOfInjective f inj).finrank_eq
  change Module.finrank F (shiftCoefficients d)=Module.finrank F ((shiftCoefficients d).map f) at eq
  rw [image,coeff_dimension m] at eq
  exact eq

theorem shared_nonzero (m : Module.finrank F K=6)
    (d e : (powMonoidHom 7 : Kˣ →* Kˣ).range) {x : K} (nx : x≠0)
    (xm : x∈shiftCoefficients d.val) (xm':x∈shiftCoefficients e.val) : d=e := by
  let G := (powMonoidHom 7 : Kˣ →* Kˣ).range
  have nine (d : G) : (d.val : K)^9=1 := by
    obtain ⟨u,e⟩ := d.property
    change u^7=d.val at e
    rw [←e,Units.val_pow_eq_pow_val,←pow_mul,pow_sixty_three m u.ne_zero]
  have d7 := coefficient_seven (mul_ne_zero d.val.ne_zero nx) (show (d.val : K)*x∈coeffMap.ker from xm)
  have e7 := coefficient_seven (mul_ne_zero e.val.ne_zero nx) (show (e.val : K)*x∈coeffMap.ker from xm')
  rw [mul_pow] at d7 e7
  have h := mul_right_cancel₀ (pow_ne_zero 7 nx) (d7.trans e7.symm)
  have power (z : G) : ((z.val : K)^7)^4=(z.val : K) := by
    rw [←pow_mul,show 7*4=9*3+1 by decide,pow_succ,pow_mul,nine z,one_pow,one_mul]
  exact Subtype.ext (Units.ext (by rw [←power d,←power e,h]))

theorem four_iff_plane (m : Module.finrank F K=6) (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z) {a b : K} (na : a≠0) (nb : b≠0) (ab : a≠b) :
    HasFour (tracePair Q a b) ↔ ∃! d : (powMonoidHom 7 : Kˣ →* Kˣ).range,
      a∈shiftCoefficients d.val ∧ b∈shiftCoefficients d.val := by
  rw [four_iff_shift m Q nq sq test na nb ab]
  constructor
  · rintro ⟨t,ht,ha,hb⟩
    let u := Units.mk0 t ht
    let d : (powMonoidHom 7 : Kˣ →* Kˣ).range := ⟨u^7,u,rfl⟩
    have x : a∈shiftCoefficients d.val := by change t^7*a∈coeffMap.ker; rwa [mul_comm]
    have y : b∈shiftCoefficients d.val := by change t^7*b∈coeffMap.ker; rwa [mul_comm]
    exact ⟨d,⟨x,y⟩,fun e he => shared_nonzero m e d na he.1 x⟩
  · rintro ⟨d,⟨ha,hb⟩,_⟩
    obtain ⟨u,h⟩:=d.property
    change u^7=d.val at h
    refine ⟨(u : K),u.ne_zero,?_,?_⟩
    · change (d.val : K)*a∈coeffMap.ker at ha
      simpa [←h,mul_comm] using ha
    · change (d.val : K)*b∈coeffMap.ker at hb
      simpa [←h,mul_comm] using hb

theorem distinct_planes (m : Module.finrank F K=6) :
    Nat.card (Set.range (fun d : (powMonoidHom 7 : Kˣ →* Kˣ).range => shiftCoefficients d.val))=9 := by
  classical
  let G := (powMonoidHom 7 : Kˣ →* Kˣ).range
  have inj : Function.Injective (fun d : G => shiftCoefficients d.val) := by
    intro d e same
    change shiftCoefficients d.val=shiftCoefficients e.val at same
    have rk := shift_dimension m d.val
    obtain ⟨x,xm,nx⟩:=Submodule.exists_mem_ne_zero_of_ne_bot
      (show shiftCoefficients d.val≠⊥ by intro h; rw [h,finrank_bot] at rk; omega)
    have xm': x∈shiftCoefficients e.val := by rw [←same]; exact xm
    exact shared_nonzero m d e nx xm xm'
  have card : Nat.card Kˣ=63 := by
    rw [Nat.card_units,Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := F),ZMod.card,m]; decide
  rw [←Nat.card_congr (Equiv.ofInjective _ inj),IsCyclic.card_powMonoidHom_range,card]
  decide

open Green50Downsets Green51LocalFlats Classical in
theorem maximum_six (m : Module.finrank F K=6) (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z) {a b : K} (na : a≠0) (nb : b≠0) (ab : a≠b) :
    let L := tracePair Q a b
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)) =
      if a^36∈(coeffMap (K := K)).ker ∧ b*a^35∈(coeffMap (K := K)).ker then 4 else 3 := by
  classical
  let L := tracePair Q a b
  change maxCosetDim _ _ (Set.range (lifted L)+Set.range (lifted L))=_
  have nl : L≠0 := by
    intro zero; apply nq; ext x
    have h := congrArg Prod.fst (LinearMap.congr_fun zero (a⁻¹*x))
    change Q (a*(a⁻¹*x))=0 at h
    simpa [←mul_assoc,na] using h
  have upper (p : Space K × (F×F)) (W : Submodule F (Space K × (F×F)))
      (inside : p+ᵥ (W : Set _) ⊆ Set.range (lifted L)+Set.range (lifted L)) : Module.finrank F W≤4 := by
    by_contra! big
    have h := half_bound L nl p W inside (by omega)
    omega
  have rank : Module.finrank F L.range≤2 := (Submodule.finrank_le _).trans (by simp)
  obtain ⟨p,W,dim,sub⟩:=Green51BCHExceptional.two_tests_in_even 2 m L rank
  have low := (le_iff_coset (by decide : 0<3) _).mpr ⟨W,p,dim,sub⟩
  have high : maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L))≤4 := by
    by_contra! above
    obtain ⟨V,q,sz,inside⟩ := (le_iff_coset (by decide : 0<5) _).mp above
    exact (by decide : ¬(5 : ℕ)≤4) (sz.symm.trans_le (upper q V inside))
  split_ifs with good
  · obtain ⟨q,V,lo,inside⟩ := (canonical_test m Q nq sq test na nb ab).mpr good
    exact le_antisymm high ((le_iff_coset (by decide : 0<4) _).mpr ⟨V,q,le_antisymm (upper q V inside) lo,inside⟩)
  · apply le_antisymm _ low
    by_contra! above
    obtain ⟨V,q,sz,inside⟩ := (le_iff_coset (by decide : 0<4) _).mp above
    exact good ((canonical_test m Q nq sq test na nb ab).mp ⟨q,V,sz.ge,inside⟩)


end Green51SixPencils

#print axioms Green51SixPencils.shared_nonzero
#print axioms Green51SixPencils.four_iff_plane
#print axioms Green51SixPencils.distinct_planes
#print axioms Green51SixPencils.maximum_six
