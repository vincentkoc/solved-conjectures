import Green51QuadraticRelations
import Green51AffineMatchings

/-! # Affine flats in the double of the binary quadratic embedding -/
open Finset Green50Downsets
open scoped Classical Pointwise Matrix
namespace Green51QuadraticFlats
local notation "F" => ZMod 2

/-- All endpoint labels of a represented affine flat of dimension at least
three are distinct when the double avoids linear three-spaces. -/
theorem disjoint_representatives {G : Type*} [AddCommGroup G] [Module F G] [Fintype G]
    [DecidableEq G] {d:ℕ} (large:3≤d) (A:Finset G)
    (avoid : ¬∃ W : Submodule F G,Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A)
    (a:Cube d×F→G) (inA:∀ i,a i∈A) (p:G) (L:Cube d →ₗ[F] G)
    (inj : Function.Injective L) (pairs:∀ z,a (z,0)+a (z,1)=p+L z) :
    Function.Injective a := by
  let B := univ.image a
  have sub : B⊆A := by
    rintro _ h;obtain ⟨i,_,rfl⟩ := mem_image.mp h;exact inA i
  have avoidB : ¬∃ W : Submodule F G,Module.finrank F W=3 ∧ ∀ w∈W,w∈B+B := by
    rintro ⟨W,dim,mem⟩
    exact avoid ⟨W,dim,fun w hw => add_subset_add sub sub (mem w hw)⟩
  have retained : p +ᵥ (L.range:Set G) ⊆ ↑(B+B) := by
    apply Set.image_subset_iff.mpr
    intro v hv
    obtain ⟨z,rfl⟩ := hv
    exact mem_add.mpr ⟨_,mem_image_of_mem a (mem_univ (z,0)),_,mem_image_of_mem a (mem_univ (z,1)),pairs z⟩
  have dim : Module.finrank F L.range=d := by rw [L.finrank_range_of_inj inj];simp [Cube]
  have cost := Green51AffineMatchings.affine_flat_cost B avoidB L.range p retained (by rw [dim];exact large)
  rw [dim] at cost
  have eq : B.card=(univ:Finset (Cube d×F)).card := by
    refine le_antisymm card_image_le ?_
    simpa [Cube,pow_succ] using cost
  exact fun _ _ e => card_image_iff.mp eq (mem_univ _) (mem_univ _) e

private def face (z w u:Cube 3) : Finset (Cube 3) := {z,w,z+u,w+u}
private theorem two_faces (z w:Cube 3) (ne:z≠w) :
    ∃ P Q : Finset (Cube 3),P.card=4 ∧ Q.card=4 ∧ (∑ i∈P,i)=0 ∧ (∑ i∈Q,i)=0 ∧ P∩Q={z,w} := by
  have search : ∀ z w:Cube 3,z≠w → ∃ u v:Cube 3,
      (face z w u).card=4 ∧ (face z w v).card=4 ∧
      (∑ i∈face z w u,i)=0 ∧ (∑ i∈face z w v,i)=0 ∧ face z w u∩face z w v={z,w} := by
    decide +kernel
  obtain ⟨u,v,facts⟩ := search z w ne
  exact ⟨_,_,facts⟩

private def endpoints {n:ℕ} (a : Cube 3×F → Cube n) (P : Finset (Cube 3)) : Finset (Cube n) :=
  (P ×ˢ (univ : Finset F)).image a

private theorem endpoints_closed {n:ℕ} (a : Cube 3×F → Cube n) (inj:Function.Injective a)
    (p : Matrix (Coordinates n) (Coordinates n) F)
    (L : Cube 3 →ₗ[F] Matrix (Coordinates n) (Coordinates n) F)
    (pairs : ∀ z,quad (a (z,0))+quad (a (z,1))=p+L z)
    (P : Finset (Cube 3)) (size:P.card=4) (total:∑ i∈P,i=0)
    {x y t : Cube n} (hx:x∈endpoints a P) (hy:y∈endpoints a P) (ht:t∈endpoints a P) :
    x+y+t∈endpoints a P := by
  apply eight_closed _ ?_ ?_ hx hy ht
  · rw [endpoints,card_image_of_injective _ inj,card_product,size,card_univ,ZMod.card]
  · have four : 4 • p=0 := by
      rw [show 4=2*2 from rfl,mul_nsmul,two_nsmul,ZModModule.add_self]
    rw [endpoints,sum_image inj.injOn,sum_product]
    simp only [show ∀ g:F→Matrix (Coordinates n) (Coordinates n) F,
      (∑ b,g b)=g 0+g 1 from fun g => Fin.sum_univ_two g,pairs,sum_add_distrib,
      sum_const,size,four,zero_add]
    rw [←map_sum L,total,map_zero]

private theorem endpoint_mem {n:ℕ} (a : Cube 3×F→Cube n) {P : Finset (Cube 3)}
    {i : Cube 3} (hi:i∈P) (b:F) : a (i,b)∈endpoints a P :=
  mem_image_of_mem a (mem_product.mpr ⟨hi,mem_univ _⟩)

private theorem same_pair_sums {n:ℕ} (a : Cube 3×F→Cube n) (inj:Function.Injective a)
    (p : Matrix (Coordinates n) (Coordinates n) F)
    (L : Cube 3 →ₗ[F] Matrix (Coordinates n) (Coordinates n) F)
    (pairs : ∀ z,quad (a (z,0))+quad (a (z,1))=p+L z) (z w : Cube 3) :
    a (z,0)+a (z,1)=a (w,0)+a (w,1) := by
  by_cases eq : z=w
  · rw [eq]
  obtain ⟨P,Q,pc,qc,ps,qs,overlap⟩ := two_faces z w eq
  have zmem : z∈P ∧ z∈Q := mem_inter.mp (overlap ▸ mem_insert_self z {w})
  have wmem : w∈P ∧ w∈Q := mem_inter.mp (overlap ▸ mem_insert_of_mem (mem_singleton_self w))
  let y := a (z,0)+a (z,1)+a (w,0)
  have yP : y∈endpoints a P := endpoints_closed a inj p L pairs P pc ps
    (endpoint_mem a zmem.1 0) (endpoint_mem a zmem.1 1) (endpoint_mem a wmem.1 0)
  have yQ : y∈endpoints a Q := endpoints_closed a inj p L pairs Q qc qs
    (endpoint_mem a zmem.2 0) (endpoint_mem a zmem.2 1) (endpoint_mem a wmem.2 0)
  obtain ⟨⟨i,b⟩,hi,hit⟩ := mem_image.mp yP
  obtain ⟨j,hj,jhit⟩ := mem_image.mp yQ
  have same : (i,b)=j := inj (hit.trans jhit.symm)
  subst j
  have iw : i=z ∨ i=w := by
    have h := mem_inter.mpr ⟨(mem_product.mp hi).1,(mem_product.mp hj).1⟩
    rwa [overlap,mem_insert,mem_singleton] at h
  have swap (s t u : Cube n) : (s+t+u=s ↔ t=u) ∧ (s+t+u=t ↔ s=u) ∧ (s+t+u=u ↔ s=t) := by
    constructor
    · rw [add_assoc,add_eq_left,←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self]
    constructor
    · rw [add_right_comm,add_eq_right,←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self]
    · rw [add_eq_right,←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self]
  have dis := swap (a (z,0)) (a (z,1)) (a (w,0))
  have b01 : b=0 ∨ b=1 := (show ∀ b:F,b=0 ∨ b=1 from by decide) b
  rcases iw with i0|i1 <;> subst i <;> rcases b01 with b0|b1 <;> subst b
  · exact False.elim (eq (congrArg Prod.fst (inj (dis.1.mp hit.symm))))
  · exact False.elim (eq (congrArg Prod.fst (inj (dis.2.1.mp hit.symm))))
  · exact False.elim (zero_ne_one (congrArg Prod.snd (inj (dis.2.2.mp hit.symm))))
  · have e := congrArg (·+a (w,0)) hit
    dsimp only [y] at e
    rwa [add_assoc (a (z,0)+a (z,1)),ZModModule.add_self,add_zero,add_comm (a (w,1)),eq_comm] at e

abbrev Target (n:ℕ) := Matrix (Coordinates n) (Coordinates n) F
def horizontal (n:ℕ) : Target n →ₗ[F] Cube n := {
  toFun := fun M i => M none (some i)
  map_add' := by intros;rfl
  map_smul' := by intros;rfl }
theorem horizontal_quad {n:ℕ} (x : Cube n) : horizontal n (quad x)=x := by
  funext i;change 1*x i=x i;exact one_mul _

private theorem triple_vertical {n:ℕ} (p : Target n) (L : Cube 3 →ₗ[F] Target n)
    (inj : Function.Injective L) (inside : ∀ z,p+L z∈graph n+graph n) (w:Cube 3) :
    horizontal n (L w)=0 := by
  have pairs (z:Cube 3) : ∃ a b:Cube n,quad a+quad b=p+L z := by
    obtain ⟨a,ha,b,hb,e⟩ := mem_add.mp (inside z)
    obtain ⟨x,_,rfl⟩ := mem_image.mp ha
    obtain ⟨y,_,rfl⟩ := mem_image.mp hb
    exact ⟨_,_,e⟩
  choose x y eq using pairs
  let a (i:Cube 3×F) := if i.2=0 then x i.1 else y i.1
  have q (z:Cube 3) : quad (a (z,0))+quad (a (z,1))=p+L z := by simpa [a] using eq z
  have uniq := disjoint_representatives (by decide : 3≤3) (graph n) (avoids_linear n)
    (fun i => quad (a i)) (fun i => mem_image_of_mem quad (mem_univ (a i))) p L inj q
  have pair := same_pair_sums a (fun _ _ e => uniq (congrArg quad e)) p L q w 0
  have proj (z:Cube 3) : a (z,0)+a (z,1)=horizontal n p+horizontal n (L z) := by
    simpa only [map_add,horizontal_quad] using congrArg (horizontal n) (q z)
  rw [proj,proj,map_zero,map_zero,add_zero] at pair
  exact (add_eq_left.mp pair)

private theorem three_through {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (large : 3≤Module.finrank F V) {w:V} (nz:w≠0) :
    ∃ U : Submodule F V,Module.finrank F U=3 ∧ w∈U := by
  let U := F ∙ w
  have one : Module.finrank F U=1 := finrank_span_singleton nz
  obtain ⟨x,hx⟩ := U.exists_of_finrank_lt (by omega)
  have nx : x∉U := by simpa only [one_smul] using hx 1 one_ne_zero
  let V₂ := U⊔F ∙ x
  have two : Module.finrank F V₂=2 := (Submodule.finrank_sup_span_singleton nx).trans (by rw [one])
  obtain ⟨y,hy⟩ := V₂.exists_of_finrank_lt (by omega)
  have ny : y∉V₂ := by simpa only [one_smul] using hy 1 one_ne_zero
  exact ⟨V₂⊔F ∙ y,(Submodule.finrank_sup_span_singleton ny).trans (by rw [two]),
    (le_sup_left : V₂≤V₂⊔F ∙ y) ((le_sup_left : U≤V₂) (Submodule.mem_span_singleton_self w))⟩

/-- Every affine flat of dimension at least three in the quadratic double
has a constant first-coordinate projection. -/
theorem fixed_horizontal {n:ℕ} (p : Target n) (W:Submodule F (Target n))
    (large : 3≤Module.finrank F W) (inside : p +ᵥ (W:Set (Target n)) ⊆ ↑(graph n+graph n)) :
    W≤(horizontal n).ker := by
  intro v hv
  by_cases vz : v=0
  · rw [vz];exact Submodule.zero_mem _
  have nz : (⟨v,hv⟩:W)≠0 := fun e => vz (congrArg Subtype.val e)
  obtain ⟨U,dim,mem⟩ := three_through large nz
  let e : Cube 3 ≃ₗ[F] U := LinearEquiv.ofFinrankEq _ _ (by simp [Cube,dim])
  let L := W.subtype.comp (U.subtype.comp e.toLinearMap)
  have inj : Function.Injective L := Subtype.val_injective.comp (Subtype.val_injective.comp e.injective)
  have all (z:Cube 3) : p+L z∈graph n+graph n := inside ⟨L z,(e z).val.property,rfl⟩
  have covered := triple_vertical p L inj all (e.symm ⟨⟨v,hv⟩,mem⟩)
  simpa [L] using covered

private def displacement {n:ℕ} (x : Cube n) (i:Coordinates n) : F := i.elim 0 x
private theorem disp_add {n:ℕ} (x y:Cube n) (i:Coordinates n) :
    displacement (x+y) i=displacement x i+displacement y i := by cases i <;> simp [displacement]

def polar {n:ℕ} (t:Cube n) : Cube n →ₗ[F] Target n := {
  toFun := fun x i j => displacement t i*displacement x j+displacement x i*displacement t j
  map_add' := by
    intro x y;ext i j
    change _=(displacement t i*displacement x j+displacement x i*displacement t j)+
      (displacement t i*displacement y j+displacement y i*displacement t j)
    simp only [disp_add,mul_add,add_mul];abel
  map_smul' := by
    intro k x;ext i j
    change _=k*(displacement t i*displacement x j+displacement x i*displacement t j)
    cases i <;> cases j <;> (simp [displacement]; try ring) }


theorem derivative {n:ℕ} (t x:Cube n) :
    quad x+quad (x+t)=(quad 0+quad t)+polar t x := by
  ext i j
  change homogeneous x i*homogeneous x j+homogeneous (x+t) i*homogeneous (x+t) j=
    (homogeneous 0 i*homogeneous 0 j+homogeneous t i*homogeneous t j)+
      (displacement t i*displacement x j+displacement x i*displacement t j)
  cases i <;> cases j <;> simp [homogeneous,displacement,add_mul,mul_add,ZModModule.add_self]
  all_goals (abel_nf; simp [show (2:F)=0 from rfl])

theorem polar_ker {n:ℕ} {t:Cube n} (nz:t≠0) : (polar t).ker=F ∙ t := by
  obtain ⟨j,hj⟩ : ∃ j,t j≠0 := by
    by_contra! h;exact nz (funext h)
  have tj : t j=1 := ((show ∀ k:F,k=0 ∨ k=1 from by decide) _).resolve_left hj
  apply le_antisymm
  · intro x hx
    refine Submodule.mem_span_singleton.mpr ⟨x j,?_⟩
    funext i
    have e := congrFun (congrFun (show polar t x=0 from hx) (some j)) (some i)
    change t j*x i+x j*t i=0 at e
    rw [tj,one_mul,←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self] at e
    exact e.symm
  · apply Submodule.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    change polar t t=0
    ext i j
    exact ZModModule.add_self _

theorem fiber_dimension {n:ℕ} {t:Cube n} (nz:t≠0) :
    Module.finrank F (polar t).range+1=n := by
  have h := (polar t).finrank_range_add_finrank_ker
  rw [polar_ker nz,finrank_span_singleton nz] at h
  simpa [Cube] using h

/-- All pair sums of labels whose inputs differ by t. -/
def fiber {n:ℕ} (t:Cube n) : Set (Target n) := (quad 0+quad t) +ᵥ ((polar t).range:Set (Target n))

theorem fiber_iff {n:ℕ} (t:Cube n) (y:Target n) :
    y∈fiber t ↔ y∈graph n+graph n ∧ horizontal n y=t := by
  constructor
  · rintro ⟨_,⟨x,rfl⟩,e⟩
    have y_eq : y=quad x+quad (x+t) := e.symm.trans (derivative t x).symm
    rw [y_eq]
    refine ⟨add_mem_add (mem_image_of_mem quad (mem_univ x)) (mem_image_of_mem quad (mem_univ (x+t))),?_⟩
    rw [map_add,horizontal_quad,horizontal_quad,←add_assoc,ZModModule.add_self,zero_add]
  · rintro ⟨inDouble,eq⟩
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp inDouble
    obtain ⟨x,_,rfl⟩ := mem_image.mp ha
    obtain ⟨z,_,rfl⟩ := mem_image.mp hb
    rw [map_add,horizontal_quad,horizontal_quad] at eq
    have other : z=x+t := by rw [←eq,←add_assoc,ZModModule.add_self,zero_add]
    rw [other,derivative]
    exact ⟨polar t x,⟨x,rfl⟩,rfl⟩

theorem flat_iff_single_fiber {n:ℕ} (p:Target n) (W:Submodule F (Target n))
    (rank : 3≤Module.finrank F W) :
    p +ᵥ (W:Set (Target n)) ⊆ ↑(graph n+graph n) ↔
      p +ᵥ (W:Set (Target n)) ⊆ fiber (horizontal n p) := by
  constructor
  · intro inside y hy
    obtain ⟨w,hw,e⟩ := (show ∃ w∈W,p+w=y from hy)
    apply (fiber_iff _ _).mpr
    refine ⟨inside hy,?_⟩
    rw [←e,map_add,show horizontal n w=0 from fixed_horizontal p W rank inside hw,add_zero]
  · exact fun sub y hy => ((fiber_iff _ _).mp (sub hy)).1

theorem flat_card {V:Type*} [AddCommGroup V] [Module F V] [Fintype V] [DecidableEq V]
    (p:V) (W:Submodule F V) :
    (p +ᵥ (W:Set V)).toFinset.card=2^(Module.finrank F W) := by
  have eq : (p +ᵥ (W:Set V)).toFinset=W.carrier.toFinset.image (fun w => p+w) := by
    ext y
    simp only [Set.mem_toFinset,mem_image]
    rfl
  rw [eq,card_image_of_injective _ (fun _ _ e => add_left_cancel e),Set.toFinset_card]
  change Fintype.card W=_
  rw [Module.card_eq_pow_finrank (K:=F),ZMod.card]

theorem fiber_zero (n:ℕ) : fiber (0:Cube n)={0} := by
  have pz : polar (0:Cube n)=0 := by
    apply LinearMap.ext
    intro x
    ext i j
    change displacement (0:Cube n) i*displacement x j+displacement x i*displacement (0:Cube n) j=0
    cases i <;> cases j <;> simp [displacement]
  rw [fiber,pz,LinearMap.range_zero,ZModModule.add_self,zero_vadd]
  rfl

/-- All top-dimensional flats in the double, indexed by their common input difference. -/
theorem largest_flats {n:ℕ} (large:4≤n) (D:Set (Target n)) :
    (∃ (p:Target n) (W:Submodule F (Target n)),Module.finrank F W+1=n ∧
      D=p +ᵥ (W:Set (Target n)) ∧ D⊆↑(graph n+graph n)) ↔
    ∃ t : Cube n,t≠0 ∧ D=fiber t := by
  constructor
  · rintro ⟨p,W,dim,rfl,inside⟩
    have sub := (flat_iff_single_fiber p W (by omega)).mp inside
    have small := card_le_card (Set.toFinset_subset_toFinset.mpr sub)
    rw [flat_card] at small
    have nz : horizontal n p≠0 := by
      intro eq
      rw [eq,fiber_zero] at small
      simp only [Set.toFinset_singleton,card_singleton] at small
      have pow := Nat.pow_le_pow_right (by decide : 0<2) (show 3≤Module.finrank F W by omega)
      omega
    refine ⟨_,nz,Set.toFinset_inj.mp (eq_of_subset_of_card_le (Set.toFinset_subset_toFinset.mpr sub) ?_)⟩
    rw [fiber,flat_card,flat_card]
    have dimT := fiber_dimension nz
    rw [show Module.finrank F (polar (horizontal n p)).range=Module.finrank F W by omega]
  · rintro ⟨t,nz,rfl⟩
    exact ⟨_,_,fiber_dimension nz,rfl,fun y hy => ((fiber_iff t y).mp hy).1⟩

theorem number_of_largest_flats {n:ℕ} (large:4≤n) :
    (Set.ncard {D:Set (Target n) | ∃ (p:Target n) (W:Submodule F (Target n)),
      Module.finrank F W+1=n ∧ D=p +ᵥ (W:Set (Target n)) ∧ D⊆↑(graph n+graph n)})=2^n-1 := by
  have eq : {D:Set (Target n) | ∃ (p:Target n) (W:Submodule F (Target n)),
      Module.finrank F W+1=n ∧ D=p +ᵥ (W:Set (Target n)) ∧ D⊆↑(graph n+graph n)}=
      (↑((univ.erase (0:Cube n)).image fiber):Set (Set (Target n))) := by
    ext D
    simp only [Set.mem_ofPred_eq,largest_flats large,mem_coe,mem_image,mem_erase,mem_univ,and_true]
    exact exists_congr fun _ => and_congr_right fun _ => eq_comm
  have inj : Function.Injective (@fiber n) := by
    intro a b e
    have h : quad 0+quad a∈fiber a := ⟨0,Submodule.zero_mem _,add_zero _⟩
    exact ((fiber_iff a _).mp h).2.symm.trans ((fiber_iff b _).mp (e ▸ h)).2
  rw [eq,Set.ncard_coe_finset,card_image_of_injective _ inj,card_erase_of_mem (mem_univ _),card_univ]
  simp [Cube]

end Green51QuadraticFlats

#print axioms Green51QuadraticFlats.disjoint_representatives
#print axioms Green51QuadraticFlats.horizontal_quad
#print axioms Green51QuadraticFlats.fixed_horizontal
#print axioms Green51QuadraticFlats.derivative
#print axioms Green51QuadraticFlats.polar_ker
#print axioms Green51QuadraticFlats.fiber_dimension
#print axioms Green51QuadraticFlats.fiber_iff
#print axioms Green51QuadraticFlats.flat_iff_single_fiber
#print axioms Green51QuadraticFlats.flat_card
#print axioms Green51QuadraticFlats.fiber_zero
#print axioms Green51QuadraticFlats.largest_flats
#print axioms Green51QuadraticFlats.number_of_largest_flats
