import Green50SymplecticSpaces

/-! # Simultaneous isotropy of two alternating forms in odd dimension -/

namespace Green51TwoAlternating
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- An alternating form on an odd-dimensional space has a nontrivial radical. -/
theorem radical_of_odd (A : LinearMap.BilinForm F V) (alt : A.IsAlt)
    (k : ℕ) (dim : Module.finrank F V=2*k+1) :
    ∃ v : V, v≠0 ∧ ∀ w, A v w=0 := by
  obtain ⟨m,size,_,a,b,expr⟩ :=
    Green50SymplecticSpaces.alternating_decomposition F _ A alt dim
  let P := (LinearMap.pi a).prod (LinearMap.pi b)
  have bound := Submodule.finrank_le P.range
  change Module.finrank F P.range ≤ Module.finrank F ((Fin m → F) × (Fin m → F)) at bound
  rw [Module.finrank_prod,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at bound
  have rank := P.finrank_range_add_finrank_ker
  rw [dim] at rank
  have pos : 0<Module.finrank F P.ker := by omega
  obtain ⟨v,mem,nz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show P.ker≠⊥ by
    intro eq;rw [eq,finrank_bot] at pos;omega)
  have pa (i : Fin m) : a i v=0 := congrFun (congrArg Prod.fst (show P v=0 from mem)) i
  have pb (i : Fin m) : b i v=0 := congrFun (congrArg Prod.snd (show P v=0 from mem)) i
  exact ⟨v,nz,fun w => by rw [expr];simp [pa,pb]⟩

omit [FiniteDimensional F V] in
theorem extend_isotropic (A : LinearMap.BilinForm F V) (alt : A.IsAlt)
    (S : Submodule F V) (v : V) (orth : ∀ s∈S,A v s=0)
    (iso : ∀ x∈S,∀ y∈S,A x y=0) :
    ∀ x∈S ⊔ Submodule.span F {v},∀ y∈S ⊔ Submodule.span F {v},A x y=0 := by
  rintro x hx y hy
  obtain ⟨s,hs,v₁,h₁,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨t,ht,v₂,h₂,rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp h₁
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp h₂
  have h : A s v=0 := by rw [←alt.neg_eq,orth s hs,neg_zero]
  simp [map_add,map_smul,iso s hs t ht,h,orth t ht,alt.self_eq_zero]

theorem extend_dim (S : Submodule F V) (v : V) (nv : v∉S) :
    Module.finrank F (S ⊔ Submodule.span F {v} : Submodule F V) = Module.finrank F S+1 := by
  have nz : v≠0 := fun h => nv (h ▸ S.zero_mem)
  have dis := Submodule.disjoint_span_singleton.mpr (fun h : v∈S => (nv h).elim)
  have d := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span F {v})
  rw [dis.eq_bot,finrank_bot,finrank_span_singleton nz,add_zero] at d
  exact d


/-- Two alternating forms in dimension 2k+1 have a common isotropic
subspace of dimension k+1 over any field. -/
theorem simultaneous (F : Type*) [Field F] (k : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (A B : LinearMap.BilinForm F V), A.IsAlt → B.IsAlt → Module.finrank F V=2*k+1 →
      ∃ S : Submodule F V, Module.finrank F S=k+1 ∧
        (∀ x∈S,∀ y∈S,A x y=0) ∧ (∀ x∈S,∀ y∈S,B x y=0) := by
  classical
  induction k with
  | zero =>
    intro V _ _ _ A B ha hb dim
    obtain ⟨v,nz,_⟩ := radical_of_odd A ha 0 dim
    refine ⟨Submodule.span F {v},finrank_span_singleton nz,?_,?_⟩
    all_goals
      rintro x hx y hy
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [ha.self_eq_zero,hb.self_eq_zero]
  | succ k ih =>
    intro V _ _ _ A B ha hb dim
    obtain ⟨v,nz,rad⟩ := radical_of_odd A ha (k+1) dim
    obtain ⟨l,one⟩ := Module.Projective.exists_dual_eq_one F nz
    let P := (B v).prod l
    have rank := P.finrank_range_add_finrank_ker
    have bound := Submodule.finrank_le P.range
    change Module.finrank F P.range ≤ Module.finrank F (F × F) at bound
    rw [Module.finrank_prod,Module.finrank_self] at bound
    let Z := Fin (2*k+1) → F
    have dz : Module.finrank F Z=2*k+1 := by simp [Z]
    obtain ⟨e,inj⟩ := finrank_le_iff_exists_linearMap.mp
      (show Module.finrank F Z≤Module.finrank F P.ker by omega)
    let j := P.ker.subtype.comp e
    have ji : Function.Injective j := P.ker.subtype_injective.comp inj
    let R := j.range
    have dr : Module.finrank F R=2*k+1 := (j.finrank_range_of_inj ji).trans dz
    obtain ⟨C,sz,hA,hB⟩ := ih (A.restrict R) (B.restrict R)
      (fun z => ha z.val) (fun z => hb z.val) dr
    let S := C.map R.subtype
    have sr : Module.finrank F S=k+1 := (R.finrank_map_subtype_eq C).trans sz
    have zero (x) (hx:x∈S) : P x=0 := by
      obtain ⟨y,_,rfl⟩ := hx
      obtain ⟨z,hz⟩ := y.property
      change P y.val=0
      rw [←hz]
      exact (e z).property
    have outside : v∉S := fun h => one_ne_zero (one.symm.trans (congrArg Prod.snd (zero v h)))
    refine ⟨S ⊔ Submodule.span F {v},by rw [extend_dim S v outside,sr],?_,?_⟩
    · apply extend_isotropic A ha S v (fun x _ => rad x)
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      exact hA x hx y hy
    · apply extend_isotropic B hb S v (fun x hx => congrArg Prod.fst (zero x hx))
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      exact hB x hx y hy

end Green51TwoAlternating
#print axioms Green51TwoAlternating.radical_of_odd
#print axioms Green51TwoAlternating.extend_isotropic
#print axioms Green51TwoAlternating.extend_dim
#print axioms Green51TwoAlternating.simultaneous
