import Green51BCHCandidates

/-! # A collision among candidate seventh-coordinate kernels in dimension six -/

open Green50Downsets Green51BCH Green51BCHCompression Green51BCHOptimality Green51BCHFlags
open scoped Pointwise
namespace Green51BCHExceptional
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K]

omit [CharP K 2] in
/-- Scalar multiplication preserving a three-plane permutes its seven nonzero elements. -/
private theorem scalar_seven (a b : Cube 3 →ₗ[F] K) (ia : Function.Injective a) (ib : Function.Injective b)
    (h : a.range=b.range) (w : K) (scale : ∀ v,b v=w*a v) : w^7=1 := by
  classical
  let s : Finset (Cube 3) := Finset.univ.erase 0
  have card : s.card=7 := by
    rw [show s.card=Fintype.card (Cube 3)-1 by simp [s]]
    decide
  have image_nonzero (f : Cube 3 →ₗ[F] K) (inj : Function.Injective f) (x : K) :
      x∈s.image f ↔ x∈f.range ∧ x≠0 := by
    constructor
    · rintro hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨⟨v,rfl⟩,fun z => (Finset.mem_erase.mp hv).1 ((f.map_eq_zero_iff inj).mp z)⟩
    · rintro ⟨⟨v,rfl⟩,nz⟩
      exact Finset.mem_image.mpr ⟨v,Finset.mem_erase.mpr ⟨fun z => nz (z ▸ f.map_zero),Finset.mem_univ _⟩,rfl⟩
  have eq : s.image a=s.image b := by ext x;rw [image_nonzero a ia,image_nonzero b ib,h]
  have prodEq := congrArg (fun u : Finset K => ∏ x∈u,x) eq
  simp only [Finset.prod_image ia.injOn,Finset.prod_image ib.injOn] at prodEq
  simp_rw [scale] at prodEq
  rw [Finset.prod_mul_distrib,Finset.prod_const,card] at prodEq
  have nz : ∏ v∈s,a v≠0 := Finset.prod_ne_zero_iff.mpr
    (fun v hv z => (Finset.mem_erase.mp hv).1 ((a.map_eq_zero_iff ia).mp z))
  exact mul_right_cancel₀ nz (prodEq.symm.trans (one_mul _).symm)

theorem candidate_collision [Fintype K] (dim : Module.finrank F K=6) :
    ¬Function.Injective (candidateMap (K:=K)) := by
  classical
  have cu : Fintype.card Kˣ=63 := by rw [←Nat.card_eq_fintype_card,units_card dim]
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨w,order⟩ := exists_prime_orderOf_dvd_card (G:=Kˣ) 3 (cu ▸ by decide)
  have pw : (w:K)^3=1 := by
    exact congrArg (fun u : Kˣ => (u:K)) (order ▸ pow_orderOf_eq_one w : w^3=1)
  let mul := LinearMap.mulLeft F (w:K)
  have inj : Function.Injective mul := fun _ _ e => mul_left_cancel₀ w.ne_zero e
  obtain ⟨Q,trace⟩ := trace_test (K:=K)
  let P := Q.prod (Q.comp mul)
  have rank := P.finrank_range_add_finrank_ker
  have bound := Submodule.finrank_le P.range
  change Module.finrank F P.range≤Module.finrank F (F × F) at bound
  rw [Module.finrank_prod,Module.finrank_self] at bound
  obtain ⟨e,ie⟩ := finrank_le_iff_exists_linearMap.mp
    (show Module.finrank F (Cube 3)≤Module.finrank F P.ker by simp only [Cube,Module.finrank_fintype_fun_eq_card,Fintype.card_fin];omega)
  let a := P.ker.subtype.comp e
  have ia : Function.Injective a := P.ker.subtype_injective.comp ie
  let b := mul.comp a
  have ib : Function.Injective b := inj.comp ia
  have z (v : Cube 3) : P (a v)=0 := (e v).property
  let j := a.codRestrict (TraceSpace K) (fun v => (trace _).mp (congrArg Prod.fst (z v)))
  let k := b.codRestrict (TraceSpace K) (fun v => (trace _).mp (congrArg Prod.snd (z v)))
  let A : Planes (TraceSpace K) := ⟨j.range,by
    simpa [Cube] using j.finrank_range_of_inj (fun x y eq => ia (congrArg (fun v : TraceSpace K => (v:K)) eq))⟩
  let B : Planes (TraceSpace K) := ⟨k.range,by
    simpa [Cube] using k.finrank_range_of_inj (fun x y eq => ib (congrArg (fun v : TraceSpace K => (v:K)) eq))⟩
  have diff : A≠B := by
    intro same
    have ran : a.range=b.range := by
      have sj := congrArg (fun C : Planes (TraceSpace K) => C.val.map (TraceSpace K).subtype) same
      change j.range.map (TraceSpace K).subtype=k.range.map (TraceSpace K).subtype at sj
      rw [←LinearMap.range_comp,←LinearMap.range_comp] at sj
      exact sj
    have h := scalar_seven a b ia ib ran (w:K) (fun _ => rfl)
    have h7 : (w:K)^7=(w:K) := by calc
      (w:K)^7=((w:K)^3)^2*(w:K) := by ring
      _ = _ := by rw [pw];simp
    have u : w=1 := Units.ext (h7.symm.trans h)
    simp [u] at order
  have eq (x y : Cube 3) : bracket (b x) (b y)=bracket (a x) (a y) := by
    change bracket ((w:K)*a x) ((w:K)*a y)=_
    calc
      _ = (w:K)^3*bracket (a x) (a y) := by unfold bracket;ring
      _ = _ := by rw [pw,one_mul]
  let ident : NinthRoots K := ⟨1,one_pow _⟩
  intro inject
  apply diff
  apply congrArg Prod.snd (inject (a₁:=(ident,A)) (a₂:=(ident,B)) ?_)
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨_,⟨x,rfl⟩,_,⟨y,rfl⟩,rfl⟩
    exact Submodule.subset_span ⟨k x,⟨x,rfl⟩,k y,⟨y,rfl⟩,congrArg (fun z => (ident.val:K)*z) (eq x y).symm⟩
  · rintro _ ⟨_,⟨x,rfl⟩,_,⟨y,rfl⟩,rfl⟩
    exact Submodule.subset_span ⟨j x,⟨x,rfl⟩,j y,⟨y,rfl⟩,congrArg (fun z => (ident.val:K)*z) (eq x y)⟩

end Green51BCHExceptional
#print axioms Green51BCHExceptional.candidate_collision
