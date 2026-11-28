import Green51SixPencilPlanes

/-! # Counting two-bit projections of the binary BCH curve in dimension six -/

open Green51GoldSix Green51BCHCompression Green51BCHOptimality Green51GoldForms Polynomial Finset
open scoped Pointwise
namespace Green51SixPencils
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

omit [Fintype K] in
private theorem cube_condition {a : K} (na : a≠0) :
    a^36∈(coeffMap (K := K)).ker ↔ (a^9)^3+a^9+1=0 := by
  let w := a^9
  have w4 : a^36=w^4 := by dsimp [w]; rw [←pow_mul]
  have map4 (z : K) : coeffMap (z^4)=(coeffMap z)^4 := by
    have add4 (a b : K) : (a+b)^4=a^4+b^4 := (iterateFrobenius K 2 2).map_add a b
    simp only [coeff_apply,add4,←pow_mul]
  change coeffMap (a^36)=0 ↔ w^3+w+1=0
  rw [w4,map4,pow_eq_zero_iff (by decide : 4≠0),coeff_apply,
    show w^4+w^2+w=w*(w^3+w+1) by ring,mul_eq_zero]
  exact or_iff_right (pow_ne_zero 9 na)

noncomputable def partners (Q : K →ₗ[F] F) (a : K) : Finset K := by
  classical
  exact univ.filter (fun b => a≠0 ∧ b≠0 ∧ a≠b ∧ HasFour (tracePair Q a b))

open Classical in
theorem partner_count (m : Module.finrank F K=6) (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z) (a : K) :
    (partners Q a).card=if (a^9)^3+a^9+1=0 then 2 else 0 := by
  classical
  by_cases na : a=0
  · subst a; simp [partners]
  by_cases cubic : (a^9)^3+a^9+1=0
  · rw [if_pos cubic]
    have good := (cube_condition na).mpr cubic
    let C := (coeffMap (K := K)).ker
    let f := LinearMap.mulLeft F (a^35)
    let S := C.comap f
    have inj : Function.Injective f := fun x y eq => mul_left_cancel₀ (pow_ne_zero 35 na) eq
    have sur := Finite.injective_iff_surjective.mp inj
    have image : S.map f=C := Submodule.map_comap_eq_self (by rw [LinearMap.range_eq_top.mpr sur]; exact le_top)
    have rank := (S.equivMapOfInjective f inj).finrank_eq
    change Module.finrank F S=Module.finrank F (S.map f) at rank
    rw [image,coeff_dimension m] at rank
    let V := univ.filter (fun z : K => z∈S)
    have card : V.card=4 := by
      change (univ.filter (·∈S)).card=4
      rw [←Fintype.card_subtype,Module.card_eq_pow_finrank (K := F),ZMod.card,rank]; decide
    have zero : (0 : K)∈V := mem_filter.mpr ⟨mem_univ _,S.zero_mem⟩
    have mem : a∈V := mem_filter.mpr ⟨mem_univ _,(show a^35*a∈C by simpa only [←pow_succ] using good)⟩
    have eq : partners Q a=(V.erase 0).erase a := by
      ext b
      simp only [partners,mem_filter,mem_univ,true_and,mem_erase,V]
      constructor
      · rintro ⟨_,nb,ab,flat⟩
        have h := (canonical_test m Q nq sq test na nb ab).mp flat
        exact ⟨Ne.symm ab,nb,(show a^35*b∈C by rw [mul_comm]; exact h.2)⟩
      · rintro ⟨ba,nb,h⟩
        refine ⟨na,nb,Ne.symm ba,(canonical_test m Q nq sq test na nb (Ne.symm ba)).mpr ⟨good,?_⟩⟩
        rw [mul_comm]; exact h
    rw [eq,card_erase_of_mem (mem_erase.mpr ⟨na,mem⟩),card_erase_of_mem zero,card]
  · rw [if_neg cubic,card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨_,nb,ab,flat⟩:= (mem_filter.mp (show b∈univ.filter _ from hb)).2
    exact cubic ((cube_condition na).mp ((canonical_test m Q nq sq test na nb ab).mp flat).1)


open Classical in
theorem active_coefficients (m : Module.finrank F K=6) :
    (univ.filter (fun c : K => (c^9)^3+c^9+1=0)).card=27 := by
  classical
  let A := univ.filter (fun c : K => c^9=1)
  let B := univ.filter (fun c : K => (c^9)^3+c^9+1=0)
  have union : A∪B=univ.filter (fun c : K => c^9=1 ∨ (c^9)^3+c^9+1=0) := by ext x; simp [A,B]
  let P : Polynomial K := X^9-1
  let D : Polynomial K := X^27+X^9+1
  have dp : P.natDegree=9 := by dsimp [P]; compute_degree!
  have dd : D.natDegree=27 := by dsimp [D]; compute_degree!
  have pn : P≠0 := by intro z; rw [z,natDegree_zero] at dp; omega
  have dn : D≠0 := by intro z; rw [z,natDegree_zero] at dd; omega
  have ax := Polynomial.card_le_degree_of_subset_roots (p := P) (Z := A) (by
    intro x hx
    apply (Polynomial.mem_roots pn).mpr
    simpa [P,sub_eq_zero] using (mem_filter.mp hx).2)
  have bx := Polynomial.card_le_degree_of_subset_roots (p := D) (Z := B) (by
    intro x hx
    apply (Polynomial.mem_roots dn).mpr
    simpa [D,←pow_mul] using (mem_filter.mp hx).2)
  have le := card_union_le A B
  rw [union,Green51GoldSix.count_coefficients m] at le
  change B.card=27
  omega

open Classical in
/-- Of the 3,906 ordered independent trace coefficient pairs, precisely 54 retain a four-flat. -/
theorem ordered_count (m : Module.finrank F K=6) (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z) :
    (∑ a : K,(partners Q a).card)=54 := by
  classical
  simp_rw [partner_count m Q nq sq test]
  rw [sum_ite,Finset.sum_const_zero,add_zero,sum_const,active_coefficients m]
  decide

omit [CharP K 2] in
private theorem coefficient_bijection (Q : K →ₗ[F] F) (nq : Q≠0) :
    Function.Bijective (fun s : K×K => tracePair Q s.1 s.2) := by
  let T := (Algebra.lmul F K).toLinearMap.compr₂ Q
  have sur : Function.Surjective T := by
    intro l
    obtain ⟨c,h⟩ := represent Q nq l
    exact ⟨c,LinearMap.ext (fun z => (h z).symm)⟩
  have dim : Module.finrank F K=Module.finrank F (K →ₗ[F] F) := by simp
  have inj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mpr sur
  constructor
  · rintro ⟨a,b⟩ ⟨c,d⟩ eq
    apply Prod.ext <;> apply inj <;> ext x
    · exact congrArg Prod.fst (LinearMap.congr_fun eq x)
    · exact congrArg Prod.snd (LinearMap.congr_fun eq x)
  · intro L
    obtain ⟨a,ha⟩ := represent Q nq ((LinearMap.fst F F F).comp L)
    obtain ⟨b,hb⟩ := represent Q nq ((LinearMap.snd F F F).comp L)
    exact ⟨(a,b), LinearMap.ext (fun x => Prod.ext (ha x).symm (hb x).symm)⟩

omit [Fintype K] in
private theorem onto_iff (Q : K →ₗ[F] F) (nq : Q≠0) (a b : K) :
    Function.Surjective (tracePair Q a b) ↔ a≠0 ∧ b≠0 ∧ a≠b := by
  constructor
  · intro sur
    obtain ⟨x,hx⟩:=sur (1,0)
    obtain ⟨y,hy⟩:=sur (0,1)
    have x1 : Q (a*x)=1 := congrArg Prod.fst hx
    have x0 : Q (b*x)=0 := congrArg Prod.snd hx
    have y1 : Q (b*y)=1 := congrArg Prod.snd hy
    exact ⟨fun h => by simp [h] at x1,fun h => by simp [h] at y1,fun h => by rw [h,x0] at x1; exact zero_ne_one x1⟩
  · rintro ⟨na,nb,ab⟩
    let U := Q.comp (LinearMap.mulLeft F a)
    have nu : U≠0 := by
      intro z; apply nq; ext x
      have eq := LinearMap.congr_fun z (a⁻¹*x)
      change Q (a*(a⁻¹*x))=0 at eq
      rwa [←mul_assoc,mul_inv_cancel₀ na,one_mul] at eq
    have one : b/a≠1 := fun h => ab ((div_eq_one_iff_eq na).mp h).symm
    have onto := Green51TwoGold.pair_surjective U nu (div_ne_zero nb na) one
    convert onto using 1
    ext x
    · rfl
    · change Q (b*x)=Q (a*(b/a*x))
      congr 1; field_simp

open Classical in
private theorem count_maps (Q : K →ₗ[F] F) (nq : Q ≠ 0) (P : (K →ₗ[F] F × F) → Prop) :
    Nat.card {L : K →ₗ[F] F × F // Function.Surjective L ∧ P L} =
      ∑ a : K, (Finset.univ.filter (fun b : K => a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ P (tracePair Q a b))).card := by
  classical
  let E : (K × K) ≃ (K →ₗ[F] F × F) := Equiv.ofBijective _ (coefficient_bijection Q nq)
  let R (a b : K) := a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ P (tracePair Q a b)
  let V (a : K) := Finset.univ.filter (R a)
  let S : {x : K × K // R x.1 x.2} ≃ {L : K →ₗ[F] F × F // Function.Surjective L ∧ P L} :=
    Equiv.subtypeEquiv E (by rintro ⟨a,b⟩; change R a b ↔ Function.Surjective (tracePair Q a b) ∧ P (tracePair Q a b); rw [onto_iff Q nq]; unfold R; tauto)
  let T : {x : K × K // R x.1 x.2} ≃ ((a : K) × ↥(V a)) :=
    { toFun := fun ⟨⟨a,b⟩,h⟩ => ⟨a,b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
      invFun := fun ⟨a,b⟩ => ⟨(a,b.val),(Finset.mem_filter.mp b.property).2⟩
      left_inv := by rintro ⟨⟨_,_⟩,_⟩; rfl
      right_inv := by rintro ⟨_,_,_⟩; rfl }
  rw [←Nat.card_congr S,Nat.card_congr T,Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Fintype.card_coe]
  rfl

/-- Exactly 54 surjective two-bit projections admit an affine four-space in dimension six. -/
theorem surjective_four_count (m : Module.finrank F K = 6) :
    Nat.card {L : K →ₗ[F] F × F // Function.Surjective L ∧ HasFour L} = 54 := by
  classical
  obtain ⟨Q,nq,sq,test⟩ := trace_functional (K := K)
  rw [count_maps Q nq]
  exact ordered_count m Q nq sq test

/-- The other 3,852 surjective projections have affine dimension three. -/
theorem surjective_no_four_count (m : Module.finrank F K = 6) :
    Nat.card {L : K →ₗ[F] F × F // Function.Surjective L ∧ ¬HasFour L} = 3852 := by
  classical
  obtain ⟨Q,nq,_,_⟩ := trace_functional (K := K)
  have card : Fintype.card K = 64 := by
    rw [Module.card_eq_pow_finrank (K := F),ZMod.card,m]; decide
  have yes := surjective_four_count (K := K) m
  rw [count_maps Q nq] at yes
  rw [count_maps Q nq]
  let V (a : K) := univ.filter (fun b : K => a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)
  have cv (a : K) : (V a).card = if a = 0 then 0 else 62 := by
    by_cases ha : a = 0
    · simp [V,ha]
    · rw [if_neg ha]
      have id : V a = (univ.erase 0).erase a := by
        ext b
        simp [V, ha, ne_comm, and_comm]
      rw [id,card_erase_of_mem (mem_erase.mpr ⟨ha,mem_univ _⟩),card_erase_of_mem (mem_univ _),card_univ,card]
  have sums := congrArg (fun f : K → ℕ => ∑ a, f a) (funext (fun a =>
    (V a).card_filter_add_card_filter_not (fun b => HasFour (tracePair Q a b))))
  simp only [sum_add_distrib,V,filter_filter,and_assoc] at sums
  have total : (∑ a : K, (V a).card) = 3906 := by
    simp_rw [cv]
    rw [sum_ite]
    simp [card,Finset.filter_ne']
  change _ = ∑ a : K, (V a).card at sums
  rw [total,yes] at sums
  apply Nat.add_left_cancel (n := 54)
  calc
    _ = 54 + ∑ a : K, #((V a).filter (fun b => ¬HasFour (tracePair Q a b))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      apply congrArg Finset.card
      ext b
      simp [V,and_assoc]
    _ = 3906 := by simpa only [V,filter_filter,and_assoc] using sums
    _ = _ := by decide


open Green51BCH

open Classical in
theorem largest_dimension (m : Module.finrank F K = 6)
    (L : K →ₗ[F] F × F) (sur : Function.Surjective L) :
    maxCosetDim F (Space K × (F × F)) (Set.range (lifted L) + Set.range (lifted L)) =
      if HasFour L then 4 else 3 := by
  classical
  obtain ⟨Q,nq,sq,test⟩ := trace_functional (K := K)
  obtain ⟨⟨a,b⟩,eq⟩ := (coefficient_bijection Q nq).surjective L
  change tracePair Q a b = L at eq
  subst L
  obtain ⟨na,nb,ab⟩ := (onto_iff Q nq a b).mp sur
  rw [maximum_six m Q nq sq test na nb ab,canonical_test m Q nq sq test na nb ab]
  split_ifs <;> rfl

/-- Count every surjective projection by the largest affine dimension in the original double. -/
theorem dimension_counts (m : Module.finrank F K = 6) (d : ℕ) :
    Nat.card {L : K →ₗ[F] F × F // Function.Surjective L ∧
      maxCosetDim F (Space K × (F × F)) (Set.range (lifted L) + Set.range (lifted L)) = d} =
      if d = 3 then 3852 else if d = 4 then 54 else 0 := by
  classical
  let md (L : K →ₗ[F] F × F) := maxCosetDim F (Space K × (F × F))
    (Set.range (lifted L) + Set.range (lifted L))
  change Nat.card {L : K →ₗ[F] F × F // Function.Surjective L ∧ md L = d} = _
  by_cases three : d = 3
  · subst d
    rw [if_pos rfl,←surjective_no_four_count (K := K) m]
    apply Nat.card_congr
    apply Equiv.subtypeEquiv (Equiv.refl _)
    intro L
    change (Function.Surjective L ∧ md L = 3) ↔ Function.Surjective L ∧ ¬HasFour L
    by_cases sur : Function.Surjective L
    · simp [sur,md,largest_dimension m L sur]
    · simp [sur]
  · by_cases four : d = 4
    · subst d
      rw [if_neg three,if_pos rfl,←surjective_four_count (K := K) m]
      apply Nat.card_congr
      apply Equiv.subtypeEquiv (Equiv.refl _)
      intro L
      change (Function.Surjective L ∧ md L = 4) ↔ Function.Surjective L ∧ HasFour L
      by_cases sur : Function.Surjective L
      · simp [sur,md,largest_dimension m L sur]
      · simp [sur]
    · rw [if_neg three,if_neg four]
      let : IsEmpty {L : K →ₗ[F] F × F // Function.Surjective L ∧ md L = d} :=
        ⟨fun ⟨L,sur,h⟩ => by
          change maxCosetDim _ _ _ = d at h
          rw [largest_dimension m L sur] at h
          split_ifs at h <;> omega⟩
      exact Nat.card_of_isEmpty


end Green51SixPencils

#print axioms Green51SixPencils.partner_count
#print axioms Green51SixPencils.active_coefficients
#print axioms Green51SixPencils.ordered_count
#print axioms Green51SixPencils.surjective_four_count
#print axioms Green51SixPencils.surjective_no_four_count
#print axioms Green51SixPencils.largest_dimension
#print axioms Green51SixPencils.dimension_counts
