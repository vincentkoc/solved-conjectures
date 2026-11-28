import Erdos478FixedPointAverages
import Erdos478RationalWordOrbits

/-! # Mixed polynomial root moments as averages of Galois fixed-point counts -/

namespace Erdos478.FrobeniusCounts
open Finset MulAction Polynomial CollisionLaw RootMoments Filter Topology
noncomputable section
variable (K : Type*) [Field K] [Algebra ℚ K]

abbrev Aut := K ≃ₐ[ℚ] K
abbrev rootType (f : ℤ[X]) := (f.map (Int.castRingHom ℚ)).rootSet K

def fixed (f : ℤ[X]) (g : Aut K) := fixedCount (rootType K f) g

theorem fixed_le_degree (f : ℤ[X]) (g : Aut K) : fixed K f g≤f.natDegree := by
  let Y := rootType K f
  have h := Nat.card_le_card_of_injective (Subtype.val : fixedBy Y g → Y) Subtype.val_injective
  exact h.trans (((f.map (Int.castRingHom ℚ)).ncard_rootSet_le K).trans natDegree_map_le)

def fixedProduct (fs : List ℤ[X]) (g : Aut K) : ℝ :=
  (fs.map fun f => (fixed K f g : ℝ)).prod

variable [FiniteDimensional ℚ K] [Normal ℚ K]

/-- The fixed-point model uses one common finite normal field. The splitting
fields of the input polynomials may intersect arbitrarily. -/
theorem moment_eq_uniform (fs : List ℤ[X]) (good : ∀ f∈fs, Good f)
    (split : ∀ f∈fs, (f.map (Int.castRingHom K)).Splits) :
    (moment fs : ℝ)=uniform (Aut K) (fixedProduct K fs) := by
  classical
  let W := RationalWord fs K
  let Ω := orbitRel.Quotient (Aut K) W
  let : Fintype Ω := Fintype.ofFinite Ω
  let tag (w : W) : Ω := Quotient.mk _ w
  have label := moment_by_labels fs K good split tag Quotient.mk_surjective (by
    intro u v
    constructor
    · intro h
      obtain ⟨g,hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact h.symm))
      exact ⟨g,fun i => congrArg Subtype.val (congrFun hg i)⟩
    · rintro ⟨g,hg⟩
      exact (Quotient.sound (orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨g,funext fun i => Subtype.ext (hg i)⟩))).symm)
  have eq : fixedProduct K fs = fun g => ∏ i : Fin fs.length, (fixedCount (rootType K (fs.get i)) g : ℝ) := by
    funext g
    rw [← List.prod_ofFn]
    exact congrArg List.prod (List.ofFn_getElem_eq_map fs (fun f => (fixed K f g : ℝ))).symm
  rw [eq,uniform_product_fixed,label,Nat.card_eq_fintype_card]

#print axioms Aut
#print axioms rootType
#print axioms fixed
#print axioms fixed_le_degree
#print axioms fixedProduct
#print axioms moment_eq_uniform
end
end Erdos478.FrobeniusCounts
