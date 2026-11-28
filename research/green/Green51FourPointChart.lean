import Green51FourFibreEquivalence
import Green51CircuitFrameCount

/-! # Product coordinates for an arbitrary four-point circuit frame -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51MissingMasks
open scoped Classical Pointwise
variable {G V : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]
  [AddCommGroup V] [Module F V] [DecidableEq V]

/-- Coordinates identify all fibre groups by one linear map and identify quotient labels by
a permutation of the circuit. -/
structure Chart (B : Finset V) (C : Finset G) (P : Submodule F G) where
  coord : (Four×V) ≃ₗ[F] G
  fibre : Four ≃ₗ[F] P
  label : ↥B ≃ ↥C
  atRow : ∀ (p : Four) (i : B), coord (p,i.val)=(fibre p).val+(label i).val

theorem chart_exists {B E : Finset V} (ref : ShortestOddCircuit E B)
    (full : Submodule.span F (B : Set V)=⊤) {C D : Finset G} (m : ShortestOddCircuit D C)
    (size : B.card=C.card) (P : Submodule F G) (rank : Module.finrank F P=2)
    (comp : IsCompl P (Submodule.span F (C : Set G))) : Nonempty (Chart B C P) := by
  classical
  let σ : ↥B ≃ ↥C := Fintype.equivOfCardEq (by simpa using size)
  let L := Submodule.span F (B : Set V)
  let R := Submodule.span F (C : Set G)
  let fromL : L ≃ₗ[F] V := LinearEquiv.ofBijective L.subtype ⟨Subtype.val_injective,fun x =>
    ⟨⟨x,by change x∈Submodule.span F (B : Set V);rw [full];trivial⟩,rfl⟩⟩
  obtain ⟨v,acts⟩ := circuit_span_equiv ref m σ
  let u : Four ≃ₗ[F] P := LinearEquiv.ofFinrankEq _ _ (by rw [rank];simp [Four,F,Module.finrank_prod])
  let e := (u.prodCongr (fromL.symm.trans v)).trans (P.prodEquivOfIsCompl R comp)
  refine ⟨⟨e,u,σ,fun p i => ?_⟩⟩
  let z : L := ⟨i.val,Submodule.subset_span i.property⟩
  change (u p).val+(v (fromL.symm (fromL z))).val=_
  rw [fromL.symm_apply_apply]
  exact congrArg ((u p).val+·) (acts i)

namespace Chart
variable {B : Finset V} {C : Finset G} {P : Submodule F G} (c : Chart B C P)

omit [DecidableEq V] in
/-- The whole product carrier maps onto the circuit cosets. -/
theorem carrier : ((univ : Finset Four) ×ˢ B).map c.coord.toEquiv.toEmbedding =
    (P : Set G).toFinset+C := by
  classical
  ext x;constructor
  · intro h
    obtain ⟨⟨p,i⟩,mem,rfl⟩ := mem_map.mp h
    let j : B := ⟨i,(mem_product.mp mem).2⟩
    exact mem_add.mpr ⟨_,Set.mem_toFinset.mpr (c.fibre p).property,_,(c.label j).property,(c.atRow p j).symm⟩
  · intro h
    obtain ⟨p,hp,i,hi,rfl⟩ := mem_add.mp h
    let a : P := ⟨p,Set.mem_toFinset.mp hp⟩
    let j := c.label.symm ⟨i,hi⟩
    refine mem_map.mpr ⟨(c.fibre.symm a,j.val),mem_product.mpr ⟨mem_univ _,j.property⟩,?_⟩
    exact (c.atRow _ j).trans (congrArg₂ (·+·) (congrArg Subtype.val (c.fibre.apply_symm_apply a))
      (congrArg Subtype.val (c.label.apply_symm_apply ⟨i,hi⟩)))

def readRow (D : Finset G) (i : V) : Finset Four := univ.filter (fun p => c.coord (p,i)∈D)

omit [Fintype G] [DecidableEq V] in
theorem read_occupied {D : Finset G} (sub : C ⊆ D) (i : V) (hi : i∈B) :
    (c.readRow D i).Nonempty := by
  refine ⟨0,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
  rw [c.atRow 0 ⟨i,hi⟩,map_zero]
  simpa only [Submodule.coe_zero,zero_add] using sub (c.label ⟨i,hi⟩).property

theorem read_mask {D : Finset G} (sub : D ⊆ (P : Set G).toFinset+C) :
    (layers B (c.readRow D)).map c.coord.toEquiv.toEmbedding=D := by
  ext x;constructor
  · intro h
    obtain ⟨⟨p,i⟩,mem,rfl⟩ := mem_map.mp h
    exact (mem_filter.mp ((mem_layers ..).mp mem).2).2
  · intro h
    have inside := sub h
    rw [←c.carrier] at inside
    obtain ⟨⟨p,i⟩,mem,rfl⟩ := mem_map.mp inside
    exact mem_map.mpr ⟨(p,i),(mem_layers ..).mpr ⟨(mem_product.mp mem).2,mem_filter.mpr ⟨mem_univ _,h⟩⟩,rfl⟩

theorem write_mask (row : V→Finset Four) :
    (layers B row).map c.coord.toEquiv.toEmbedding ⊆ (P : Set G).toFinset+C := by
  rw [←c.carrier]
  apply map_subset_map.mpr
  rintro ⟨p,i⟩ h
  exact mem_product.mpr ⟨mem_univ _,((mem_layers ..).mp h).1⟩

omit [DecidableEq G] [Fintype G] in
theorem write_hits (row : V→Finset Four) (live : ∀ i∈B,(row i).Nonempty) :
    ∀ x∈C, ∃ p∈P,p+x ∈ (layers B row).map c.coord.toEquiv.toEmbedding := by
  intro x hx
  let j := c.label.symm ⟨x,hx⟩
  obtain ⟨p,hp⟩ := live j.val j.property
  refine ⟨(c.fibre p).val,(c.fibre p).property,mem_map.mpr ⟨(p,j.val),(mem_layers ..).mpr ⟨j.property,hp⟩,?_⟩⟩
  exact (c.atRow p j).trans (congrArg ((c.fibre p).val+·) (congrArg Subtype.val (c.label.apply_symm_apply ⟨x,hx⟩)))

end Chart
end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.chart_exists
#print axioms Green51FrameIsomorphisms.Chart.carrier
#print axioms Green51FrameIsomorphisms.Chart.read_occupied
#print axioms Green51FrameIsomorphisms.Chart.read_mask
#print axioms Green51FrameIsomorphisms.Chart.write_mask
#print axioms Green51FrameIsomorphisms.Chart.write_hits
