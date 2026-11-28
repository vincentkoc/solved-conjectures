import Green51CircuitProductChart
import Green51CompleteSumsetCount
import Green51RealizableShifts

/-! # Presentations of the actual dense binary doubles by rows of arbitrary binary dimension -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51NearThreshold Green51GirthFrame Green51Hyperplane
open Green51MissingMasks Green51AffineEnumeration
open scoped Classical Pointwise

/-- A linear coordinate system takes the specified row mask to the missing set of the double. -/
def FibrePresents {s r : ℕ} (B : Finset (𝔽₂ (2*(s+1)))) (row : 𝔽₂ (2*(s+1)) → Finset (𝔽₂ r))
    (S : Finset (𝔽₂ (2*(s+1)+r))) : Prop :=
  ∃ e : (𝔽₂ r × 𝔽₂ (2*(s+1))) ≃ₗ[F] (𝔽₂ (2*(s+1)+r)),
    (layers B row).map e.toEquiv.toEmbedding=Sᶜ

theorem fibre_margin {s r k : ℕ}
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) :
    2^r*(2*s+3)+2*2^r < 2*k := by
  have lower : 4*(2*s+3+2) ≤ min (5*(2*s+3)+12) (4*(2*s+3)+20) := le_min (by omega) (by omega)
  have h := (Nat.mul_le_mul_right (2^r) lower).trans_lt near
  nlinarith only [h]

/-- Every double counted by the codimension-two predicate has occupied rows on any fixed
spanning reference circuit of the right size. -/
theorem present_counted_fibres {s r k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k)
    {B : Finset (𝔽₂ (2*(s+1)))} (ref : ShortestOddCircuit B B) (size : B.card=2*s+3)
    (full : Submodule.span F (B : Set (𝔽₂ (2*(s+1))))=⊤) {S : Finset (𝔽₂ (2*(s+1)+r))}
    (belongs : S ∈ countedDoubles (2*(s+1)+r) k (threshold (2*s))) :
    ∃ row, (∀ i∈B,(row i).Nonempty) ∧ (layers B row).card=k ∧ FibrePresents B row S := by
  classical
  have entry := belongs
  rw [← nonseparated_doubles hs k near] at entry
  have no := (mem_filter.mp entry).2
  obtain ⟨sz,_,A,add,ha⟩ := (mem_filter.mp belongs).2
  have realized : ∃ A : Finset (𝔽₂ (2*(s+1)+r)), (A+A)ᶜ=Sᶜ ∧ threshold (2*s)<(A.dens : ℝ) :=
    ⟨A,congrArg (fun T : Finset _ => Tᶜ) add,ha⟩
  obtain ⟨C,m,len,P,comp,sub,_,_⟩ := Green51OriginRecovery.frame_certificate hs no
    (by simpa only [sz] using near) realized
  have ambient : Module.finrank F (𝔽₂ (2*(s+1)+r))=2*(s+1)+r := by simp [𝔽₂,𝔽]
  have rankC := circuit_rank m
  have both := Submodule.finrank_add_eq_of_isCompl comp
  let u : 𝔽₂ r ≃ₗ[F] P := LinearEquiv.ofFinrankEq _ _ (by
    have dim : Module.finrank F (𝔽₂ r)=r := by simp [𝔽₂,𝔽]
    omega)
  obtain ⟨c⟩ := product_chart_exists ref full m (size.trans len.symm) P u comp
  have eq := c.read_mask sub
  exact ⟨c.readRow Sᶜ,c.read_occupied m.1,by simpa only [card_map,sz] using congrArg card eq,⟨c.coord,eq⟩⟩

/-- Conversely every occupied word of the prescribed size is the missing set of an actual
counted double, in suitable linear coordinates. -/
theorem realize_fibre_rows {s r k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k)
    {B : Finset (𝔽₂ (2*(s+1)))} (ref : ShortestOddCircuit B B) (size : B.card=2*s+3)
    (full : Submodule.span F (B : Set (𝔽₂ (2*(s+1))))=⊤) (row : 𝔽₂ (2*(s+1))→Finset (𝔽₂ r))
    (live : ∀ i∈B,(row i).Nonempty) (sz : (layers B row).card=k) :
    ∃ S ∈ countedDoubles (2*(s+1)+r) k (threshold (2*s)), FibrePresents B row S := by
  classical
  have gap : threshold (2*s)<threshold (2*(s+1)) := by
    apply sub_pos.mp
    rw [layer_step]
    exact div_pos (halfLayer_pos _) (by positivity)
  obtain ⟨A,ha,avoid,count⟩ := (sharp_missing (s := s) (r := r) (by omega) gap le_rfl).1
  obtain ⟨C,m,len,P,rank,comp,_⟩ := missing_circuit (s := s) (r := r) (by omega) A (gap.trans_le ha) avoid count.ge
  let u : 𝔽₂ r ≃ₗ[F] P := LinearEquiv.ofFinrankEq _ _ (by rw [rank];simp [𝔽₂,𝔽])
  obtain ⟨c⟩ := product_chart_exists ref full m (size.trans len.symm) P u comp
  let D := (layers B row).map c.coord.toEquiv.toEmbedding
  have sub := c.write_mask row
  obtain ⟨A',eq,den⟩ := realize_in_container hs m len P comp D sub
  have cardD : D.card=k := by simpa only [D,card_map] using sz
  have slots : Fintype.card (𝔽₂ r)=2^r := by simp [𝔽₂,𝔽]
  have big : ((P : Set _).toFinset+C).card<2*D.card := by
    rw [←c.carrier,card_map,card_product,card_univ,slots,size,cardD]
    have h := fibre_margin near
    omega
  have dim := majority_flat_dimension (by omega) m (by omega) P comp D sub big
  rw [if_pos (c.write_hits row live)] at dim
  refine ⟨Dᶜ,mem_filter.mpr ⟨mem_univ _,?_,dim,A',?_,den⟩,c.coord,?_⟩
  · simpa only [compl_compl] using cardD
  · simpa only [compl_compl] using congrArg (fun T : Finset _ => Tᶜ) eq
  · exact (compl_compl D).symm

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.present_counted_fibres
#print axioms Green51FrameIsomorphisms.realize_fibre_rows
