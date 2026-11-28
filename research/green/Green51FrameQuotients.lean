import Green51SectionPartition
import Green51CircuitEquivalence

/-! # Counting maps presenting an unlabelled circuit frame -/

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise
variable {G K : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]
  [AddCommGroup K] [Module F K] [DecidableEq K] [Fintype K]

omit [Fintype K] in
private theorem lift_frame_bijection {C D : Finset G} {B : Finset K}
    (m : ShortestOddCircuit D C) (n : ShortestOddCircuit B B)
    (full : Submodule.span F (B : Set K) = ⊤)
    (P : Submodule F G) (comp : IsCompl P (Submodule.span F (C : Set G)))
    (e : ↥C ≃ ↥B) :
    ∃ f : G →ₗ[F] K, Function.Surjective f ∧
      (∀ p ∈ P, f p=0) ∧ (∀ i : C, f i = (e i).val) ∧
      ∀ x, f x ∈ B ↔ x ∈ (P : Set G).toFinset+C := by
  classical
  let V := Submodule.span F (C : Set G)
  let W := Submodule.span F (B : Set K)
  obtain ⟨l,onC⟩ := Green51MissingMasks.circuit_span_equiv m n e
  let f : G →ₗ[F] K := W.subtype.comp (l.toLinearMap.comp (V.projectionOnto P comp.symm))
  have kill (p : G) (hp : p ∈ P) : f p=0 := by
    change ((l (V.projectionOnto P comp.symm p) : W) : K) = 0
    rw [Submodule.projectionOnto_apply_of_mem_right comp.symm hp,map_zero]; rfl
  have onV (v : V) : f v=(l v).val := by
    change ((l (V.projectionOnto P comp.symm v.val) : W) : K) = _
    rw [Submodule.projectionOnto_apply_of_mem_left comp.symm v.property]
  have onPoints (i : C) : f i=(e i).val :=
    (onV ⟨i.val,Submodule.subset_span i.property⟩).trans (onC i)
  refine ⟨f,?_,kill,onPoints,?_⟩
  · intro y
    let w : W := ⟨y,by change y ∈ Submodule.span F (B : Set K); rw [full]; trivial⟩
    exact ⟨(l.symm w).val,(onV _).trans (congrArg Subtype.val (l.apply_symm_apply w))⟩
  · intro x
    constructor
    · intro hx
      have hx' : x ∈ P ⊔ V := comp.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨p,hp,v,hv,rfl⟩ := Submodule.mem_sup.mp hx'
      rw [map_add,kill _ hp,zero_add] at hx
      let b : B := ⟨f v,hx⟩
      let i := e.symm b
      have ei : (e i).val=f v := congrArg Subtype.val (e.apply_symm_apply b)
      have eq : (⟨i.val,Submodule.subset_span i.property⟩ : V) = ⟨v,hv⟩ :=
        l.injective (Subtype.ext ((onC i).trans (ei.trans (onV ⟨v,hv⟩))))
      exact mem_add.mpr ⟨p,Set.mem_toFinset.mpr hp,i.val,i.property,
        congrArg (fun z : V => p+z.val) eq⟩
    · intro hx
      obtain ⟨p,hp,i,hi,rfl⟩ := mem_add.mp hx
      rw [map_add,kill _ (Set.mem_toFinset.mp hp),zero_add,onPoints ⟨i,hi⟩]
      exact (e ⟨i,hi⟩).property
end Green51GirthFrame

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise
variable {G K : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]
  [AddCommGroup K] [Module F K] [DecidableEq K] [Fintype K]

private theorem surjective_frame {B : Finset K} (n : ShortestOddCircuit B B)
    (full : Submodule.span F (B : Set K) = ⊤)
    (f : G →ₗ[F] K) (surj : Function.Surjective f) :
    let U := univ.filter (fun x => f x ∈ B)
    ∃ C, ShortestOddCircuit U C ∧ C.card=B.card ∧
      IsCompl f.ker (Submodule.span F (C : Set G)) ∧ U=(f.ker : Set G).toFinset+C := by
  classical
  dsimp only
  obtain ⟨j,sec⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr surj)
  have left (x : K) : f (j x) = x := LinearMap.congr_fun sec x
  have inj : Function.Injective j := Function.LeftInverse.injective left
  let C := B.image j
  have len : C.card = B.card := card_image_of_injOn inj.injOn
  have span : Submodule.span F (C : Set G) = j.range := by
    dsimp [C]; rw [coe_image,←LinearMap.map_span,full,Submodule.map_top]
  have comp : IsCompl f.ker (Submodule.span F (C : Set G)) := by
    rw [span]
    constructor
    · apply Submodule.disjoint_def.mpr
      rintro x hx ⟨y,rfl⟩
      have hy := (left y).symm.trans hx
      rw [hy,map_zero]
    · apply codisjoint_iff.mpr
      apply top_unique
      intro x _
      exact Submodule.mem_sup.mpr ⟨x-j (f x),by simp [LinearMap.mem_ker,left],j (f x),⟨f x,rfl⟩,sub_add_cancel _ _⟩
  have circ : ShortestOddCircuit C C := by
    refine ⟨Subset.rfl,len ▸ n.2.1,?_,?_⟩
    · dsimp only [C]; rw [sum_image (fun _ _ _ _ he => inj he),←map_sum,n.2.2.1,map_zero]
    · intro R sub odd zero
      have inB : R.image f ⊆ B := by
        intro x hx
        obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
        obtain ⟨b,hb,rfl⟩ := mem_image.mp (sub hy)
        rwa [left]
      have one : Set.InjOn f (R : Set G) := by
        intro x hx y hy eq
        obtain ⟨a,ha,rfl⟩ := mem_image.mp (sub hx)
        obtain ⟨b,hb,rfl⟩ := mem_image.mp (sub hy)
        rw [left,left] at eq
        rw [eq]
      have size := card_image_of_injOn one
      have gz : ∑ x ∈ R.image f, x = 0 := by
        rw [sum_image one,←map_sum,zero,map_zero]
      simpa [len,size] using n.2.2.2 _ inB (size ▸ odd) gz
  have same : univ.filter (fun x => f x ∈ B) = (f.ker : Set G).toFinset+C := by
    ext x; rw [mem_filter]; simp only [mem_univ,true_and]
    constructor
    · intro hx
      exact mem_add.mpr ⟨x-j (f x),Set.mem_toFinset.mpr (by simp [LinearMap.mem_ker,left]),
        j (f x),mem_image.mpr ⟨f x,hx,rfl⟩,sub_add_cancel _ _⟩
    · intro hx
      obtain ⟨p,hp,y,hy,rfl⟩ := mem_add.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
      rw [map_add,show f p=0 from LinearMap.mem_ker.mp (Set.mem_toFinset.mp hp),left,zero_add]
      exact hb
  exact ⟨C,same ▸ (container_size_girth circ f.ker comp).1,len,comp,same⟩
end Green51GirthFrame

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise
variable {G K : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]
  [AddCommGroup K] [Module F K] [DecidableEq K] [Fintype K]

omit [Fintype K] in
private theorem restrict_frame {C U : Finset G} {B : Finset K} (m : ShortestOddCircuit U C)
    (n : ShortestOddCircuit B B) (large : 5 ≤ B.card) (size : C.card=B.card)
    (full : Submodule.span F (B : Set K) = ⊤)
    (P : Submodule F G) (frame : U=(P : Set G).toFinset+C)
    (f : G →ₗ[F] K) (surj : Function.Surjective f) (pre : ∀ x, f x ∈ B ↔ x ∈ U) :
    (∀ p ∈ P, f p=0) ∧ ∃ e : ↥C ≃ ↥B, ∀ i : C, f i=(e i).val := by
  classical
  have comp : IsCompl (⊥ : Submodule F K) (Submodule.span F (B : Set K)) := by rw [full]; exact isCompl_bot_top
  have reprB (x : K) : x ∈ B ↔ ∃ t ∈ (⊥ : Submodule F K), ∃ i ∈ B, x=t+i := by simp
  have kill (p : G) (hp : p ∈ P) : f p=0 := by
    apply (periods_iff n large comp reprB (f p)).mpr
    intro y hy
    obtain ⟨x,rfl⟩ := surj y
    obtain ⟨t,ht,i,hi,x_eq⟩ := mem_add.mp (frame ▸ (pre x).mp hy)
    rw [←map_add]; apply (pre _).mpr
    rw [frame,←x_eq]
    exact mem_add.mpr ⟨t+p,Set.mem_toFinset.mpr (P.add_mem (Set.mem_toFinset.mp ht) hp),
      i,hi,add_right_comm t p i⟩
  let r (i : C) : B := ⟨f i,(pre _).mpr (m.1 i.property)⟩
  have onto : Function.Surjective r := by
    intro b
    obtain ⟨x,eq⟩ := surj b.val
    have hx : x ∈ U := (pre _).mp (eq ▸ b.property)
    obtain ⟨p,hp,i,hi,num⟩ := mem_add.mp (frame ▸ hx)
    refine ⟨⟨i,hi⟩,Subtype.ext ?_⟩
    change f i=b.val
    rw [←num,map_add,kill _ (Set.mem_toFinset.mp hp),zero_add] at eq
    exact eq
  have bij := (Fintype.bijective_iff_surjective_and_card r).mpr ⟨onto,by simpa using size⟩
  exact ⟨kill,Equiv.ofBijective r bij,fun _ => rfl⟩

omit [Fintype K] in
private theorem frame_fiber_card {C U : Finset G} {B : Finset K} (m : ShortestOddCircuit U C)
    (n : ShortestOddCircuit B B) (large : 5 ≤ B.card) (size : C.card=B.card)
    (full : Submodule.span F (B : Set K) = ⊤) (P : Submodule F G)
    (comp : IsCompl P (Submodule.span F (C : Set G))) (frame : U=(P : Set G).toFinset+C) :
    Nat.card {f : G →ₗ[F] K // Function.Surjective f ∧ ∀ x, f x ∈ B ↔ x ∈ U} =
      B.card.factorial := by
  classical
  let T := {f : G →ₗ[F] K // Function.Surjective f ∧ ∀ x, f x ∈ B ↔ x ∈ U}
  have res (f : T) := restrict_frame m n large size full P frame f.val f.property.1 f.property.2
  let b (f : T) : ↥C ≃ ↥B := (res f).2.choose
  have pts (f : T) (i : C) : f.val i=(b f i).val := (res f).2.choose_spec i
  have inj : Function.Injective b := by
    intro f h eq
    apply Subtype.ext
    apply LinearMap.eqLocus_eq_top.mp
    apply top_unique
    rw [←comp.sup_eq_top]
    apply sup_le
    · intro p hp
      exact ((res f).1 _ hp).trans ((res h).1 _ hp).symm
    · apply Submodule.span_le.mpr
      intro i hi
      exact (pts f ⟨i,hi⟩).trans ((congrArg (fun e : ↥C ≃ ↥B => (e ⟨i,hi⟩).val) eq).trans (pts h ⟨i,hi⟩).symm)
  have onto : Function.Surjective b := by
    intro e
    obtain ⟨f,hs,_,onC,pre⟩ := lift_frame_bijection m n full P comp e
    let t : T := ⟨f,hs,fun x => frame ▸ pre x⟩
    exact ⟨t,Equiv.ext fun i => Subtype.ext ((pts t i).symm.trans (onC i))⟩
  calc
    _ = Nat.card (↥C ≃ ↥B) := Nat.card_congr (Equiv.ofBijective b ⟨inj,onto⟩)
    _ = _ := by
      let e : ↥C ≃ ↥B := Fintype.equivOfCardEq (by simpa using size)
      rw [Nat.card_eq_fintype_card,Fintype.card_equiv e]; simp [size]
end Green51GirthFrame

namespace Green51GirthFrame
open Finset Green53ParityThreshold
open scoped Classical Pointwise
variable {G K : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]
  [AddCommGroup K] [Module F K] [DecidableEq K] [Fintype K]

/-- Every unlabelled circuit frame has one quotient map for each ordering of its reference circuit. -/
theorem count_frame_quotients (G : Type*) [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]
    {B : Finset K} (n : ShortestOddCircuit B B) (large : 5 ≤ B.card)
    (full : Submodule.span F (B : Set K) = ⊤) :
    (circuitFrames G B.card).card * B.card.factorial =
      Nat.card {f : G →ₗ[F] K // Function.Surjective f} := by
  classical
  let T := {f : G →ₗ[F] K // Function.Surjective f}
  let S := ↥(circuitFrames G B.card)
  let W (U : S) := {f : G →ₗ[F] K // Function.Surjective f ∧ ∀ x, f x ∈ B ↔ x ∈ U.val}
  let I (f : T) := univ.filter (fun x => f.val x ∈ B)
  have frame (f : T) : I f ∈ circuitFrames G B.card := by
    obtain ⟨C,m,size,comp,eq⟩ := surjective_frame n full f.val f.property
    exact mem_filter.mpr ⟨mem_univ _,C,m,size,f.val.ker,comp,eq⟩
  let e : T ≃ Σ U : S, W U := {
    toFun := fun f => ⟨⟨I f,frame f⟩,⟨f.val,f.property,fun x => by simp [I]⟩⟩
    invFun := fun v => ⟨v.2.val,v.2.property.1⟩
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨U,hU⟩,f,hs,pre⟩
      have eq : U = univ.filter (fun x => f x ∈ B) := by
        ext x; simpa using (pre x).symm
      subst U; rfl }
  let : Finite (G →ₗ[F] K) := Finite.of_injective (fun f : G →ₗ[F] K => (f : G → K)) DFunLike.coe_injective
  let : Fintype (G →ₗ[F] K) := Fintype.ofFinite _
  have same (U : S) : Fintype.card (W U) = B.card.factorial := by
    obtain ⟨C,m,size,P,comp,word⟩ := (mem_filter.mp U.property).2
    simpa only [W,Nat.card_eq_fintype_card] using frame_fiber_card m n large size full P comp word
  change _ = Nat.card T
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp [same,S]
end Green51GirthFrame
#print axioms Green51GirthFrame.count_frame_quotients
