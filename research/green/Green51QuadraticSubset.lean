import Green51QuadraticFlats

/-! # An inverse theorem for doubles of quadratic images -/

open Finset Green50Downsets
open scoped Classical Pointwise
namespace Green51QuadraticFlats
local notation "F" => ZMod 2

/-- Rank-nullity on a subspace that contains the kernel of the linear map. -/
theorem map_rank {E H:Type*} [AddCommGroup E] [Module F E] [Module.Finite F E]
    [AddCommGroup H] [Module F H] (f:E →ₗ[F] H) (U:Submodule F E) (contained:f.ker≤U) :
    Module.finrank F (U.map f)+Module.finrank F f.ker=Module.finrank F U := by
  have r := (f.domRestrict U).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict,LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe contained).finrank_eq] at r
  exact r

theorem both_labels {n:ℕ} (A:Finset (Cube n)) (x t:Cube n) (nz:t≠0) :
    quad x+quad (x+t)∈A.image quad+A.image quad ↔ x∈A ∧ x+t∈A := by
  constructor
  · intro h
    obtain ⟨a,ha,b,hb,eq⟩ := mem_add.mp h
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ha
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hb
    have shape := congrArg (horizontal n) eq
    simp only [map_add,horizontal_quad,←add_assoc,ZModModule.add_self,zero_add] at shape
    have right : v=u+t := by rw [←shape,←add_assoc,ZModModule.add_self,zero_add]
    rw [right,derivative,derivative] at eq
    have images := add_left_cancel eq
    have same : u+x∈(polar t).ker := by
      change polar t (u+x)=0
      rw [map_add,images,ZModModule.add_self]
    rw [polar_ker nz] at same
    obtain ⟨k,hk⟩ := Submodule.mem_span_singleton.mp same
    rcases (show ∀ k:F,k=0 ∨ k=1 from by decide) k with h|h <;> subst k
    · rw [zero_smul,eq_comm,←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self] at hk
      rw [←hk,←right];exact ⟨hu,hv⟩
    · rw [one_smul] at hk
      have vu : v=x := by rw [right,hk,←add_assoc,ZModModule.add_self,zero_add]
      have ux : x+t=u := by rw [hk,add_left_comm,ZModModule.add_self,add_zero]
      exact ⟨vu ▸ hv,ux ▸ hu⟩
  · rintro ⟨h,h'⟩
    exact add_mem_add (mem_image_of_mem quad h) (mem_image_of_mem quad h')

private theorem span_in_range {n:ℕ} {p:Target n} {W:Submodule F (Target n)} {t:Cube n}
    (sub:p +ᵥ (W:Set (Target n)) ⊆ fiber t) :
    ∃ x : Cube n, (quad 0+quad t)+polar t x=p ∧ W≤(polar t).range := by
  obtain ⟨_,⟨x,rfl⟩,eq⟩ := sub (show p∈p +ᵥ (W:Set (Target n)) from ⟨0,W.zero_mem,add_zero _⟩)
  refine ⟨x,eq,?_⟩
  intro w hw
  obtain ⟨_,⟨y,rfl⟩,hy⟩ := sub (show p+w∈p +ᵥ (W:Set (Target n)) from ⟨w,hw,rfl⟩)
  change (quad 0+quad t)+polar t y=p+w at hy
  change (quad 0+quad t)+polar t x=p at eq
  rw [←eq,add_assoc (quad 0+quad t) (polar t x) w] at hy
  have diff := add_left_cancel hy
  exact ⟨y+x,by rw [map_add,diff,add_right_comm,ZModModule.add_self,zero_add]⟩

/-- A flat of dimension d≥3 in a quadratic-image double is equivalent to a
flat of dimension d+1 in the input set itself. -/
theorem subset_inverse {n d:ℕ} (large:3≤d) (A:Finset (Cube n)) :
    (∃ (p:Target n) (W:Submodule F (Target n)),Module.finrank F W=d ∧
      p +ᵥ (W:Set (Target n)) ⊆ ↑(A.image quad+A.image quad)) ↔
    ∃ (x:Cube n) (U:Submodule F (Cube n)),Module.finrank F U=d+1 ∧
      x +ᵥ (U:Set (Cube n)) ⊆ ↑A := by
  constructor
  · rintro ⟨p,W,dim,inside⟩
    have sub : A.image quad⊆graph n := image_subset_image (subset_univ A)
    have full : p +ᵥ (W:Set (Target n)) ⊆ ↑(graph n+graph n) :=
      fun y hy => add_subset_add sub sub (inside hy)
    let t := horizontal n p
    have vertical : p +ᵥ (W:Set (Target n)) ⊆ fiber t := (flat_iff_single_fiber p W (by rw [dim];exact large)).mp full
    obtain ⟨x,base,contained⟩ := span_in_range vertical
    have nz : t≠0 := by
      intro e
      have cards := card_le_card (Set.toFinset_subset_toFinset.mpr vertical)
      rw [flat_card,dim,e,fiber_zero,Set.toFinset_singleton,card_singleton] at cards
      have lb := Nat.pow_le_pow_right (by decide : 0<2) large
      omega
    let U := W.comap (polar t)
    have image : U.map (polar t)=W := Submodule.map_comap_eq_self contained
    have ker : (polar t).ker≤U := by
      intro z hz
      change polar t z∈W
      rw [show polar t z=0 from hz];exact W.zero_mem
    have rank := map_rank (polar t) U ker
    rw [image,dim,polar_ker nz,finrank_span_singleton nz] at rank
    refine ⟨x,U,rank.symm,?_⟩
    apply Set.image_subset_iff.mpr
    intro u hu
    apply ((both_labels A (x+u) t nz).mp ?_).1
    rw [derivative,map_add,←add_assoc,base]
    exact inside ⟨polar t u,hu,rfl⟩
  · rintro ⟨x,U,dim,sub⟩
    obtain ⟨t,ht,nz⟩ : ∃ t∈U,t≠0 := by
      by_contra! h
      have eq : U=⊥ := eq_bot_iff.mpr (fun t ht => (Submodule.mem_bot F).mpr (h t ht))
      rw [eq,finrank_bot] at dim;omega
    have ker : (polar t).ker≤U := by rw [polar_ker nz];exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ht)
    have rank := map_rank (polar t) U ker
    rw [polar_ker nz,finrank_span_singleton nz,dim] at rank
    refine ⟨quad x+quad (x+t),U.map (polar t),by omega,?_⟩
    apply Set.image_subset_iff.mpr
    rintro _ ⟨u,hu,rfl⟩
    have h1 : x+u∈A := sub ⟨u,hu,rfl⟩
    have h2 : x+u+t∈A := sub ⟨u+t,U.add_mem hu ht,(add_assoc _ _ _).symm⟩
    have h := (both_labels A (x+u) t nz).mpr ⟨h1,h2⟩
    rw [derivative,map_add,←add_assoc,←derivative] at h
    exact h

/-- The lower cutoff three is sharp. The quadratic double of the binary
plane contains a plane although the input cannot contain a three-flat. -/
theorem two_exception :
    (∃ W:Submodule F (Target 2),Module.finrank F W=2 ∧ ∀ w∈W,w∈graph 2+graph 2) ∧
    ¬∃ U:Submodule F (Cube 2),Module.finrank F U=3 := by
  let f (j:Fin 2) : Target 2 := quad 0+quad (Pi.single j 1)
  let L := Fintype.linearCombination F f
  have inj : Function.Injective L := by
    change ∀ ⦃x y:Cube 2⦄,L x=L y → x=y
    dsimp only [L,f]; decide +kernel
  have cover : ∀ x:Cube 2,L x∈graph 2+graph 2 := by dsimp only [L,f]; decide +kernel
  constructor
  · refine ⟨L.range,?_,?_⟩
    · rw [L.finrank_range_of_inj inj];simp
    · rintro _ ⟨x,rfl⟩;exact cover x
  · rintro ⟨U,dim⟩
    have h := Submodule.finrank_le U
    rw [dim] at h
    simp [Cube] at h

end Green51QuadraticFlats
#print axioms Green51QuadraticFlats.both_labels
#print axioms Green51QuadraticFlats.subset_inverse

#print axioms Green51QuadraticFlats.two_exception
#print axioms Green51QuadraticFlats.map_rank
