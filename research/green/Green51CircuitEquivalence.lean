import Green51GeelenEquality

/-! # Linear equivalences between shortest circuits and their period spaces -/

namespace Green51MissingMasks
open Finset Green53ParityThreshold Green51GirthFrame Green51NearThreshold
open scoped Classical Pointwise
variable {G K : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]
  [AddCommGroup K] [Module F K] [DecidableEq K] [Fintype K]

omit [Fintype G] [Fintype K] in
private theorem extend_circuit_bijection {C D : Finset G} {B E : Finset K}
    (m : ShortestOddCircuit D C) (n : ShortestOddCircuit E B) (e : ↥C ≃ ↥B) :
    ∃ f : G →ₗ[F] K, ∀ x : C, f x = (e x).val := by
  classical
  let value (x : G) := if hx : x ∈ C then (e ⟨x,hx⟩).val else 0
  have val (x : C) : value x = (e x).val := dif_pos x.property
  have odd := m.2.1
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < C.card by rw [Nat.odd_iff] at odd; omega)
  obtain ⟨f, eq⟩ := extend_values (independent_erase m hp) value
  have sumValues : ∑ x ∈ C, value x = 0 := by
    apply Eq.trans _ n.2.2.1
    apply sum_bij (fun x hx => (e ⟨x,hx⟩).val)
    · exact fun x hx => (e ⟨x,hx⟩).property
    · intro x hx y hy he
      exact congrArg Subtype.val (e.injective (Subtype.ext he))
    · intro y hy
      exact ⟨_,(e.symm ⟨y,hy⟩).property,congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)⟩
    · intro x hx; exact val ⟨x,hx⟩
  have rest : (∑ x ∈ C.erase p, f x) = ∑ x ∈ C.erase p, value x := sum_congr rfl (fun x hx => eq x hx)
  have point : f p = value p := by
    apply add_left_cancel (a := ∑ x ∈ C.erase p, f x)
    calc
      _ = ∑ x ∈ C, f x := sum_erase_add C _ hp
      _ = 0 := by rw [←map_sum,m.2.2.1,map_zero]
      _ = (∑ x ∈ C.erase p, f x) + value p := by rw [rest,sum_erase_add C _ hp,sumValues]
  refine ⟨f, fun x => Eq.trans ?_ (val x)⟩
  by_cases h : x.val=p
  · exact h ▸ point
  · exact eq x (mem_erase.mpr ⟨h,x.property⟩)

omit [Fintype G] [Fintype K] in
theorem circuit_span_equiv {C D : Finset G} {B E : Finset K}
    (m : ShortestOddCircuit D C) (n : ShortestOddCircuit E B) (e : ↥C ≃ ↥B) :
    ∃ l : Submodule.span F (C : Set G) ≃ₗ[F] Submodule.span F (B : Set K),
      ∀ i : C, (l ⟨i.val,Submodule.subset_span i.property⟩).val = (e i).val := by
  classical
  let V := Submodule.span F (C : Set G)
  let W := Submodule.span F (B : Set K)
  obtain ⟨f, onC⟩ := extend_circuit_bijection m n e
  have image : f '' (C : Set G) = (B : Set K) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      rw [show f x = _ from onC ⟨x,hx⟩]; exact (e ⟨x,hx⟩).property
    · intro hy
      let v := e.symm ⟨y,hy⟩
      exact ⟨v.val,v.property,(onC v).trans (congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩))⟩
  have mv : V.map f = W := by dsimp only [V,W]; rw [LinearMap.map_span, image]
  let l : V →ₗ[F] W := (f.domRestrict V).codRestrict W (fun x => mv ▸ Submodule.mem_map_of_mem x.property)
  have surj : Function.Surjective l := by
    rintro ⟨y,hy⟩
    obtain ⟨x,hx,eq⟩ : y ∈ V.map f := mv.symm ▸ hy
    exact ⟨⟨x,hx⟩,Subtype.ext eq⟩
  have size : C.card = B.card := by simpa using Fintype.card_congr e
  have rC := circuit_rank m
  have rB := circuit_rank n
  have dims : Module.finrank F V = Module.finrank F W := by dsimp [V,W]; omega
  exact ⟨LinearEquiv.ofBijective l ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dims).mpr surj,surj⟩,
    fun i => onC i⟩

end Green51MissingMasks
#print axioms Green51MissingMasks.circuit_span_equiv

namespace Green51MissingMasks
open Finset Green53ParityThreshold Green51GirthFrame
open scoped Classical Pointwise
variable {G K : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]
  [AddCommGroup K] [Module F K] [DecidableEq K] [Fintype K]

theorem container_equiv {C D : Finset G} {B E : Finset K}
    (m : ShortestOddCircuit D C) (n : ShortestOddCircuit E B) (same : C.card=B.card)
    (P : Submodule F G) (Q : Submodule F K) (ranks : Module.finrank F P = Module.finrank F Q)
    (p : IsCompl P (Submodule.span F (C : Set G))) (q : IsCompl Q (Submodule.span F (B : Set K))) :
    ∃ l : G ≃ₗ[F] K, ((P : Set G).toFinset + C).map l.toEquiv.toEmbedding = (Q : Set K).toFinset + B := by
  classical
  let V := Submodule.span F (C : Set G)
  let W := Submodule.span F (B : Set K)
  let e : ↥C ≃ ↥B := Fintype.equivOfCardEq (by simpa using same)
  obtain ⟨f,onC⟩ := circuit_span_equiv m n e
  let u : P ≃ₗ[F] Q := LinearEquiv.ofFinrankEq P Q ranks
  let left := P.prodEquivOfIsCompl V p
  let right := Q.prodEquivOfIsCompl W q
  let l := (left.symm.trans (u.prodCongr f)).trans right
  have atPoint (t : P) (i : C) : l (t.val+i.val) = (u t).val+(e i).val := by
    let v : V := ⟨i.val,Submodule.subset_span i.property⟩
    change right ((u.prodCongr f) (left.symm (left (t,v)))) = _
    rw [left.symm_apply_apply]
    exact congrArg (fun y : K => (u t).val + y) (onC i)
  refine ⟨l, ?_⟩
  ext y; constructor
  · intro h
    obtain ⟨x,hx,rfl⟩ := mem_map.mp h
    obtain ⟨t,ht,i,hi,rfl⟩ := mem_add.mp hx
    let a : P := ⟨t, Set.mem_toFinset.mp ht⟩
    let b : C := ⟨i, hi⟩
    exact mem_add.mpr ⟨_,Set.mem_toFinset.mpr (u a).property,_,(e b).property,(atPoint a b).symm⟩
  · intro h
    obtain ⟨t,ht,i,hi,rfl⟩ := mem_add.mp h
    let a : Q := ⟨t, Set.mem_toFinset.mp ht⟩
    let b : B := ⟨i,hi⟩
    refine mem_map.mpr ⟨(u.symm a).val+(e.symm b).val, mem_add.mpr ⟨_,Set.mem_toFinset.mpr (u.symm a).property,_,
      (e.symm b).property,rfl⟩, ?_⟩
    simpa [a,b] using atPoint (u.symm a) (e.symm b)

end Green51MissingMasks
#print axioms Green51MissingMasks.container_equiv
