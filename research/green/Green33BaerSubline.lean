import Mathlib
/-! A geometric progression forced by a non-Sidon three-dimensional subspace. -/
open Submodule
namespace Green33BaerProgressions
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Multiplication by s preserves enough of W to force three consecutive
terms of a geometric progression in W. -/
theorem three_terms (W : Submodule F K) (dim : Module.finrank F W=3)
    (s : K) (nz : s≠0) (c b : K) (hc : c≠0) (indep : b∉F ∙ c)
    (cw : c∈W) (bw : b∈W) (sc : s*c∈W) (sb : s*b∈W) :
    ∃ y : K,y≠0 ∧ y∈W ∧ s*y∈W ∧ s*(s*y)∈W := by
  let m:K≃ₗ[F] K:=LinearEquiv.ofBijective (Algebra.lmul F K s)
    ⟨fun _ _ e => mul_left_cancel₀ nz e,fun x => ⟨s⁻¹*x,by change s*(s⁻¹*x)=x;field_simp⟩⟩
  let U:=W⊓W.comap m.toLinearMap
  have uc : c∈U := ⟨cw,sc⟩
  have ub : b∈U := ⟨bw,sb⟩
  have line : F ∙ c≤U := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr uc)
  have two : 2≤Module.finrank F U := by
    by_contra! small
    have eq:=Submodule.eq_of_le_of_finrank_le line (show Module.finrank F U≤Module.finrank F (F ∙ c) by rw [finrank_span_singleton hc];omega)
    exact indep (eq.symm ▸ ub)
  let V:=U.map m.toLinearMap
  have vs : V≤W := Submodule.map_le_iff_le_comap.mpr inf_le_right
  have us : U≤W := inf_le_left
  have cap:=(Submodule.finrank_mono (sup_le us vs)).trans_eq dim
  have size:=m.finrank_map_eq U
  have rank:=Submodule.finrank_sup_add_finrank_inf_eq U V
  have overlap : U⊓V≠⊥ := by
    intro eq
    rw [eq,finrank_bot] at rank
    change Module.finrank F V=Module.finrank F U at size
    omega
  obtain ⟨z,hz,nonzero⟩:=Submodule.exists_mem_ne_zero_of_ne_bot overlap
  obtain ⟨y,hy,h⟩:=hz.2
  have zy : s*y=z := h
  have yn : y≠0 := fun eq => nonzero (by rw [←zy,eq,mul_zero])
  exact ⟨y,yn,us hy,us (zy ▸ hz.1),zy ▸ hz.1.2⟩

/-- Two inequivalent projective factorizations in W supply the common ratio
and direction for the progression. -/
theorem collision_progression (W : Submodule F K) (dim : Module.finrank F W=3)
    (a b c d : Kˣ) (aw : (a:K)∈W) (bw : (b:K)∈W) (cw : (c:K)∈W) (dw : (d:K)∈W)
    (collision : (a:K)*b=c*(d:K)) (ac : (a:K)∉F ∙ (c:K)) (ad : (a:K)∉F ∙ (d:K)) :
    ∃ s y : K,s∉Set.range (algebraMap F K) ∧ y≠0 ∧ y∈W ∧ s*y∈W ∧ s*(s*y)∈W := by
  let s:K:=(a:K)/(c:K)
  have sc : s*c=a := div_mul_cancel₀ _ c.ne_zero
  have sb : s*b=d := by dsimp only [s];field_simp;linear_combination collision
  have bc : (b:K)∉F ∙ (c:K) := by
    rintro hb
    obtain ⟨r,hr⟩:=Submodule.mem_span_singleton.mp hb
    have h : r • (a:K)=d := by rw [←sc,←mul_smul_comm,hr,sb]
    have hn : r≠0 := by intro z;rw [z,zero_smul] at h;exact d.ne_zero h.symm
    apply ad
    exact Submodule.mem_span_singleton.mpr ⟨r⁻¹,by rw [←h,inv_smul_smul₀ hn]⟩
  have ns : s∉Set.range (algebraMap F K) := by
    rintro ⟨r,hr⟩
    exact ac (Submodule.mem_span_singleton.mpr ⟨r,by rw [Algebra.smul_def,hr,sc]⟩)
  obtain ⟨y,yn,wy,wsy,wssy⟩:=three_terms W dim s (div_ne_zero a.ne_zero c.ne_zero)
    c b c.ne_zero bc cw bw (sc ▸ aw) (sb ▸ dw)
  exact ⟨s,y,ns,yn,wy,wsy,wssy⟩
#print axioms three_terms
#print axioms collision_progression
end Green33BaerProgressions

namespace Green33BaerForms

section RationalForm
variable {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K]
    [Algebra F K] [IsScalarTower F E K]

private def liftCoords (e : K≃ₗ[E](Fin 3→E)) : (Fin 3→F)→ₗ[F]K :=
  (e.symm.restrictScalars F).toLinearMap.comp (LinearMap.pi fun j =>
    (Algebra.linearMap F E).comp (LinearMap.proj j))

/-- An arbitrary projective image of the rational subplane in a chosen E-frame. -/
def rationalForm (F : Type*) [Field F] [Algebra F E] [Algebra F K] [IsScalarTower F E K]
    (e : K≃ₗ[E](Fin 3→E)) : Submodule F K :=
  (liftCoords (F:=F) e).range

theorem form_rank (e : K≃ₗ[E](Fin 3→E)) : Module.finrank F (rationalForm F e)=3 := by
  have h : Function.Injective (liftCoords (F:=F) e) := by
    intro a b eq
    have t:=congrArg e eq
    change e (e.symm _) = e (e.symm _) at t
    rw [e.apply_symm_apply,e.apply_symm_apply] at t
    exact funext fun j => (algebraMap F E).injective (congrFun t j)
  rw [rationalForm,LinearMap.finrank_range_of_inj h]
  simp

/-- Scaling between two nonzero rational points uses a rational scalar. -/
theorem form_scattered (e : K≃ₗ[E](Fin 3→E)) {y:K} (hy:y∈rationalForm F e)
    (yn:y≠0) (r:E) (hr:r • y∈rationalForm F e) : r∈Set.range (algebraMap F E) := by
  obtain ⟨a,ha⟩:=hy
  obtain ⟨b,hb⟩:=hr
  have val (c : Fin 3→F) : e (liftCoords e c)=fun j => algebraMap F E (c j) := e.apply_symm_apply _
  have aa : e y=fun j => algebraMap F E (a j) := ha ▸ val a
  have bb:=congrArg e hb
  rw [val,e.map_smul,aa] at bb
  obtain ⟨j,nz⟩ : ∃ j,a j≠0 := by
    by_contra! zero
    apply yn
    rw [←ha,show a=0 from funext zero,map_zero]
  refine ⟨b j/a j,?_⟩
  rw [map_div₀,div_eq_iff ((map_ne_zero (algebraMap F E)).mpr nz)]
  exact congrFun bb j
#print axioms form_rank
#print axioms form_scattered
end RationalForm

end Green33BaerForms
namespace Green33BaerSubline

section Roots
open Polynomial
open scoped Polynomial IntermediateField
variable {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K]
    [Algebra F K] [IsScalarTower F E K] [FiniteDimensional E K]

private theorem quadratic_injective (s : K) (rank : Module.finrank E K=3)
    (ns : s∉Set.range (algebraMap E K)) {P : E[X]} (small : P.natDegree≤2)
    (zero : aeval s P=0) : P=0 := by
  have hi : IsIntegral E s:=Algebra.IsIntegral.isIntegral s
  have prime : Module.finrank E E⟮s⟯ ∣ 3 :=
    ⟨Module.finrank E⟮s⟯ K,rank ▸ (Module.finrank_mul_finrank E E⟮s⟯ K).symm⟩
  have no : Module.finrank E E⟮s⟯≠1 := fun e =>
    ns (IntermediateField.mem_bot.mp (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp e))
  have deg : (minpoly E s).natDegree=3 := by
    rw [←IntermediateField.adjoin.finrank hi]
    exact ((by decide : Nat.Prime 3).eq_one_or_self_of_dvd _ prime).resolve_left no
  by_contra h
  have b:=Polynomial.natDegree_le_of_dvd (minpoly.dvd E s zero) h
  omega

/-- A scalar-projective equality between two products of subline points
recovers both parameters, as an unordered pair. -/
theorem root_pair (s : K) (rank : Module.finrank E K=3) (ns : s∉Set.range (algebraMap E K))
    (a b c d : F) (r : E)
    (eq : (s+algebraMap F K a)*(s+algebraMap F K b)=
      algebraMap E K r*((s+algebraMap F K c)*(s+algebraMap F K d))) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  let emb:=algebraMap F E
  let L (x:F) : E[X] := X+C (emb x)
  let P:E[X]:=L a*L b-C r*(L c*L d)
  have small : P.natDegree≤2 := by dsimp [P,L];compute_degree
  have zero : aeval s P=0 := by
    dsimp only [P,L,emb]
    simp only [map_sub,map_mul,map_add,aeval_X,aeval_C,←IsScalarTower.algebraMap_apply]
    exact sub_eq_zero.mpr eq
  have poly:=sub_eq_zero.mp (quadratic_injective s rank ns small zero)
  have one : r=1 := by
    have h:=congrArg (fun f:E[X] => f.leadingCoeff) poly
    have mon (u v:F) : (L u*L v).Monic := (monic_X_add_C ..).mul (monic_X_add_C ..)
    rw [(mon a b).leadingCoeff,leadingCoeff_mul,leadingCoeff_C,(mon c d).leadingCoeff,mul_one] at h
    exact h.symm
  rw [one,map_one,one_mul] at poly
  have same : a=c ∨ a=d := by
    have h:=congrArg (eval (-(emb a))) poly
    simp only [L,eval_mul,eval_add,eval_X,eval_C,neg_add_cancel,zero_mul] at h
    rcases mul_eq_zero.mp h.symm with h|h
    · exact Or.inl (emb.injective (by linear_combination -h))
    · exact Or.inr (emb.injective (by linear_combination -h))
  have sum := congrArg (fun f:E[X] => f.coeff 1) poly
  have coeff (x y:F) : (L x*L y).coeff 1=emb x+emb y := by simp [L,mul_add,add_mul,add_comm]
  rw [coeff,coeff] at sum
  rcases same with rfl|rfl
  · exact Or.inl ⟨rfl,emb.injective (add_left_cancel sum)⟩
  · exact Or.inr ⟨rfl,emb.injective (by linear_combination sum)⟩
#print axioms root_pair
end Roots


section Labels
variable {F E K G : Type*} [Field F] [Fintype F] [Field E] [Field K] [Algebra F E]
    [Algebra E K] [Algebra F K] [IsScalarTower F E K] [FiniteDimensional E K]
    [AddCommGroup G] [DecidableEq G] [Fintype G]
open Finset
open scoped Pointwise

/-- Projective labels of the nonzero vectors in W. A sign or parity embedding
may already be part of the label map. -/
noncomputable def layer (tag : Kˣ→G) (W : Submodule F K) (z : G) : Finset G := by
  classical exact univ.filter fun g => ∃ u:Kˣ,(u:K)∈W ∧ g=z+tag u

/-- A progression plane contains a translate of a two-fold sumset with all
unordered root pairs distinct, in the actual big-field projective quotient. -/
theorem split_products (tag : Kˣ→G) (mul : ∀ u v,tag (u*v)=tag u+tag v)
    (same : ∀ u v,tag u=tag v → ∃ r:E,(u:K)=r • (v:K))
    (W : Submodule F K) (z : G) (s y : K) (rank : Module.finrank E K=3)
    (ns : s∉Set.range (algebraMap E K)) (yn : y≠0)
    (wy : y∈W) (wsy : s*y∈W) (wss : s*(s*y)∈W) :
    ∃ X : Finset G,∃ c:G,X.card=Fintype.card F ∧ (X+X).card=(Fintype.card F+1).choose 2 ∧
      (X+X).image (c+·)⊆layer tag W z := by
  classical
  have nz (a:F) : s+algebraMap F K a≠0 := by
    intro zero
    apply ns
    exact ⟨-(algebraMap F E a),by rw [map_neg,←IsScalarTower.algebraMap_apply];linear_combination -zero⟩
  let u (a:F):=Units.mk0 (s+algebraMap F K a) (nz a)
  let g (a:F):=tag (u a)
  let X:=univ.image g
  let h:Sym2 F→G:=Sym2.lift ⟨fun a b => g a+g b,fun _ _ => add_comm ..⟩
  have hinj : Function.Injective h := by
    rintro ⟨a,b⟩ ⟨c,d⟩ eq
    have ht : tag (u a*u b)=tag (u c*u d) := by rw [mul,mul];exact eq
    obtain ⟨r,eq⟩:=same _ _ ht
    apply Sym2.eq_iff.mpr
    apply root_pair s rank ns a b c d r
    simpa only [Algebra.smul_def,Units.val_mul,u,Units.val_mk0] using eq
  have ginj : Function.Injective g := by
    intro a b eq
    have h' : h (Sym2.mk a a)=h (Sym2.mk b b) := by change g a+g a=g b+g b;rw [eq]
    rcases Sym2.eq_iff.mp (hinj h') with h|h <;> exact h.1
  have im : univ.image h=X+X := by
    ext v
    constructor
    · intro hv
      obtain ⟨⟨a,b⟩,_,rfl⟩:=mem_image.mp hv
      exact add_mem_add (mem_image_of_mem _ (mem_univ a)) (mem_image_of_mem _ (mem_univ b))
    · intro hv
      obtain ⟨v,hvv,w,hw,rfl⟩:=mem_add.mp hv
      obtain ⟨a,_,rfl⟩:=mem_image.mp hvv
      obtain ⟨b,_,rfl⟩:=mem_image.mp hw
      exact mem_image.mpr ⟨Sym2.mk a b,mem_univ _,rfl⟩
  let v:=Units.mk0 y yn
  refine ⟨X,z+tag v,by dsimp only [X];rw [card_image_of_injective _ ginj,card_univ],?_,?_⟩
  · rw [←im,card_image_of_injective _ hinj,card_univ,Sym2.card]
  · intro k hk
    obtain ⟨l,hl,rfl⟩:=mem_image.mp hk
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hl
    obtain ⟨a,_,rfl⟩:=mem_image.mp ha
    obtain ⟨b,_,rfl⟩:=mem_image.mp hb
    have sum:=W.add_mem (W.add_mem wss (W.smul_mem (a+b) wsy)) (W.smul_mem (a*b) wy)
    have eq : y*((s+algebraMap F K a)*(s+algebraMap F K b)) =
        s*(s*y)+(a+b) • (s*y)+(a*b) • y := by simp only [Algebra.smul_def,map_add,map_mul];ring
    refine mem_filter.mpr ⟨mem_univ _,v*(u a*u b),?_,?_⟩
    · change y*((s+algebraMap F K a)*(s+algebraMap F K b))∈W
      rw [eq];exact sum
    · rw [mul,mul];change z+tag v+(g a+g b)=z+(tag v+(g a+g b));abel
#print axioms split_products
end Labels


section Baer
open Green33BaerForms Green33BaerProgressions
open Finset
open scoped Pointwise
variable {F E K G : Type*} [Field F] [Fintype F] [Field E] [Field K] [Algebra F E]
    [Algebra E K] [Algebra F K] [IsScalarTower F E K] [FiniteDimensional E K] [FiniteDimensional F K]
    [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- Two inequivalent multiplicative pairs in a rational projective subplane
force a translated projective square of the full subline size. -/
theorem baer_split (frame : K≃ₗ[E](Fin 3→E)) (tag : Kˣ→G) (mul : ∀ u v,tag (u*v)=tag u+tag v)
    (same : ∀ u v,tag u=tag v → ∃ r:E,(u:K)=r • (v:K)) (z : G)
    (a b c d : Kˣ) (aw : (a:K)∈rationalForm F frame) (bw : (b:K)∈rationalForm F frame)
    (cw : (c:K)∈rationalForm F frame) (dw : (d:K)∈rationalForm F frame)
    (collision : (a:K)*b=c*(d:K)) (ac : (a:K)∉F ∙ (c:K)) (ad : (a:K)∉F ∙ (d:K)) :
    ∃ X : Finset G,∃ shift:G,X.card=Fintype.card F ∧ (X+X).card=(Fintype.card F+1).choose 2 ∧
      (X+X).image (shift+·)⊆layer tag (rationalForm F frame) z := by
  obtain ⟨s,y,off,yn,wy,wsy,wss⟩:=collision_progression _ (form_rank frame) a b c d aw bw cw dw collision ac ad
  have ns : s∉Set.range (algebraMap E K) := by
    rintro ⟨r,hr⟩
    have h : r • y∈rationalForm F frame := by rwa [Algebra.smul_def,hr]
    obtain ⟨u,hu⟩:=form_scattered frame wy yn r h
    apply off
    exact ⟨u,by rw [IsScalarTower.algebraMap_apply F E K,hu,hr]⟩
  have rank : Module.finrank E K=3 := by rw [frame.finrank_eq];simp
  exact split_products tag mul same _ z s y rank ns yn wy wsy wss

#print axioms baer_split
end Baer

section Count
open Finset Green33BaerForms
variable {F E K G : Type*} [Field F] [Fintype F] [Field E] [Field K] [Fintype K] [Algebra F E]
    [Algebra E K] [Algebra F K] [IsScalarTower F E K] [AddCommGroup G] [Fintype G]

/-- Each rational point has exactly t−1 vector representatives, uniformly in
the projective frame, translation and choice of faithful quotient coordinates. -/
theorem layer_card (frame : K≃ₗ[E](Fin 3→E)) (tag : Kˣ→G)
    (same : ∀ u v,tag u=tag v ↔ ∃ r:E,(u:K)=r • (v:K)) (z : G) :
    (layer tag (rationalForm F frame) z).card=(Fintype.card F)^2+Fintype.card F+1 := by
  classical
  let W:=rationalForm F frame
  let L:=layer tag W z
  have rep (g:↥L) : ∃ u:Kˣ,(u:K)∈W ∧ g.val=z+tag u := by simpa only [L,layer,mem_filter,mem_univ,true_and] using g.property
  choose u inside coord using rep
  let V:={w:W // w≠0}
  let v (p:↥L × Fˣ) : V := ⟨⟨(p.2:F) • (u p.1:K), W.smul_mem _ (inside p.1)⟩,
    fun eq => (smul_ne_zero p.2.ne_zero (u p.1).ne_zero) (congrArg Subtype.val eq)⟩
  have scale (p:↥L × Fˣ) : (v p).val.val=algebraMap F K (p.2:F)*(u p.1:K) := Algebra.smul_def ..
  let key (w:V):=Units.mk0 w.val.val (fun h => w.property (Subtype.ext h))
  have coord' (p:↥L × Fˣ) : z+tag (key (v p))=p.1.val := by
    rw [coord p.1]
    apply congrArg (z+·)
    exact (same _ _).mpr ⟨algebraMap F E (p.2:F),by
      change (v p).val.val=_
      rw [scale,Algebra.smul_def,←IsScalarTower.algebraMap_apply]⟩
  have inj : Function.Injective v := by
    rintro ⟨g,a⟩ ⟨j,b⟩ eq
    have gj : g=j := Subtype.ext ((coord' (g,a)).symm.trans ((congrArg (fun w => z+tag (key w)) eq).trans (coord' (j,b))))
    subst j
    have h:=congrArg (fun w:V => w.val.val) eq
    rw [scale,scale] at h
    exact Prod.ext rfl (Units.ext ((algebraMap F K).injective (mul_right_cancel₀ (u g).ne_zero h)))
  have surj : Function.Surjective v := by
    intro w
    let g:↥L:=⟨z+tag (key w),by simpa only [L,layer,mem_filter,mem_univ,true_and] using (show ∃ u:Kˣ,(u:K)∈W ∧ z+tag (key w)=z+tag u from ⟨key w,w.val.property,rfl⟩)⟩
    have e : tag (key w)=tag (u g) := add_left_cancel (coord g)
    obtain ⟨r,hr⟩:=(same _ _).mp e
    change w.val.val=r • (u g:K) at hr
    obtain ⟨a,ha⟩:=form_scattered frame (inside g) (u g).ne_zero r (hr ▸ w.val.property)
    have eq : w.val.val=(algebraMap F K a)*(u g:K) := by rw [hr,Algebra.smul_def,←ha,←IsScalarTower.algebraMap_apply]
    have nz : a≠0 := by rintro rfl;rw [map_zero,zero_mul] at eq;exact w.property (Subtype.ext eq)
    exact ⟨(g,Units.mk0 a nz),Subtype.ext (Subtype.ext ((scale (g,Units.mk0 a nz)).trans eq.symm))⟩
  have sz:=Fintype.card_congr (Equiv.ofBijective v ⟨inj,surj⟩)
  rw [Fintype.card_prod,Fintype.card_coe,Fintype.card_units] at sz
  change L.card*(Fintype.card F-1)=Fintype.card {w:W // w≠0} at sz
  rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,Module.card_eq_pow_finrank (K:=F) (V:=W),show Module.finrank F W=3 from form_rank frame] at sz
  have one:=Fintype.one_lt_card (α:=F)
  have prod : ((Fintype.card F)^2+Fintype.card F+1)*(Fintype.card F-1)=(Fintype.card F)^3-1 := by
    have cube : 1≤(Fintype.card F)^3 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ ((Fintype.card_pos (α:=F)).ne'))
    zify [one.le,cube]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) (sz.trans prod.symm)
#print axioms layer_card
end Count

end Green33BaerSubline
