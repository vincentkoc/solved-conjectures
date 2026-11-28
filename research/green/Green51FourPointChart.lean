import Green51FourFibreEquivalence
import Green51CircuitProductChart

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
  let u : Four ≃ₗ[F] P := LinearEquiv.ofFinrankEq _ _ (by rw [rank];simp [Four,F,Module.finrank_prod])
  obtain ⟨c⟩ := product_chart_exists ref full m size P u comp
  exact ⟨⟨c.coord,c.fibre,c.label,c.atRow⟩⟩

namespace Chart
variable {B : Finset V} {C : Finset G} {P : Submodule F G} (c : Chart B C P)

private def productChart : ProductChart Four B C P :=
  ⟨c.coord,c.fibre,c.label,c.atRow⟩

omit [DecidableEq V] in
/-- The whole product carrier maps onto the circuit cosets. -/
theorem carrier : ((univ : Finset Four) ×ˢ B).map c.coord.toEquiv.toEmbedding =
    (P : Set G).toFinset+C := c.productChart.carrier

def readRow (D : Finset G) (i : V) : Finset Four := univ.filter (fun p => c.coord (p,i)∈D)

omit [Fintype G] [DecidableEq V] in
theorem read_occupied {D : Finset G} (sub : C ⊆ D) (i : V) (hi : i∈B) :
    (c.readRow D i).Nonempty := c.productChart.read_occupied sub i hi

theorem read_mask {D : Finset G} (sub : D ⊆ (P : Set G).toFinset+C) :
    (layers B (c.readRow D)).map c.coord.toEquiv.toEmbedding=D := c.productChart.read_mask sub

theorem write_mask (row : V→Finset Four) :
    (layers B row).map c.coord.toEquiv.toEmbedding ⊆ (P : Set G).toFinset+C := c.productChart.write_mask row

omit [DecidableEq G] [Fintype G] in
theorem write_hits (row : V→Finset Four) (live : ∀ i∈B,(row i).Nonempty) :
    ∀ x∈C, ∃ p∈P,p+x ∈ (layers B row).map c.coord.toEquiv.toEmbedding :=
  c.productChart.write_hits row live

end Chart
end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.chart_exists
#print axioms Green51FrameIsomorphisms.Chart.carrier
#print axioms Green51FrameIsomorphisms.Chart.read_occupied
#print axioms Green51FrameIsomorphisms.Chart.read_mask
#print axioms Green51FrameIsomorphisms.Chart.write_mask
#print axioms Green51FrameIsomorphisms.Chart.write_hits
