import Erdos478TetrahedralVertexAction

/-! # Equivariant coordinates for the six edges of the tetrahedron of quartic roots -/

namespace Erdos478.TetrahedralGap
open Polynomial Finset Equiv MulAction FirstCollision BinaryGap FrobeniusCounts SplittingDensity
open scoped Classical
noncomputable section

private theorem pair_in_coordinates {L : Type*} [Field L] [CharZero L] {a b c x y : L}
    (hx : x∈vertices a b c) (hy : y∈vertices a b c) (hne : x≠y) :
    (10+(x+y))/4∈edgePoints a b c := by
  simp only [vertices,Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;> first
  | contradiction
  | (simp only [edgePoints,Set.mem_insert_iff,Set.mem_singleton_iff]
     first | (left; ring1) | (right; left; ring1) | (right; right; left; ring1) |
       (right; right; right; left; ring1) | (right; right; right; right; left; ring1) |
       (right; right; right; right; right; ring1))

variable (K : Type*) [Field K] [NumberField K]

private theorem pair_is_root (sp : ((rationalGap 6).map (algebraMap ℚ K)).Splits)
    (x y : Vertex K) (hne : x≠y) : (10+(x.val+y.val))/4∈(rationalGap 6).rootSet K := by
  let L := AlgebraicClosure ℚ
  let e : K →ₐ[ℚ] L := IsAlgClosed.lift
  have q := quartic_splits_of_sextic K sp
  have rat : (gapPoly 6).map (Int.castRingHom ℚ)=rationalGap 6 := by simp [gapPoly,rationalGap]
  obtain ⟨a,b,c,hv,he⟩ := coordinate_root_sets L
  rw [rat] at he
  have v (z : Vertex K) : e z.val∈vertices a b c := by
    rw [← hv,← q.image_rootSet e]
    exact ⟨z.val,z.prop,rfl⟩
  have h := pair_in_coordinates (v x) (v y) (fun eq => hne (Subtype.ext (e.injective eq)))
  rw [← he,← sp.image_rootSet e] at h
  obtain ⟨t,ht,eq⟩ := h
  have same : t=(10+(x.val+y.val))/4 := by
    apply e.injective
    change e t=e ((10+(x.val+y.val))/4)
    rw [map_div₀,map_add,map_add,map_ofNat,map_ofNat]
    exact eq
  exact same ▸ ht

abbrev VertexPair := ((univ : Finset (Vertex K)).powersetCard 2 : Finset (Finset (Vertex K)))

def edgeOfPair (sp : ((rationalGap 6).map (algebraMap ℚ K)).Splits)
    (s : VertexPair K) : GapRoots K 6 :=
  ⟨(10+∑ i∈s.val,i.val)/4,by
    obtain ⟨x,y,ne,eq⟩ := card_eq_two.mp (mem_powersetCard.mp s.prop).2
    simpa [eq,ne] using pair_is_root K sp x y ne⟩

def permutePair (g : Aut K) (s : VertexPair K) : VertexPair K :=
  ⟨s.val.map (vertexAction K g).toEmbedding,mem_powersetCard.mpr
    ⟨subset_univ _,(card_map _).trans (mem_powersetCard.mp s.prop).2⟩⟩

theorem permutePair_edge (sp : ((rationalGap 6).map (algebraMap ℚ K)).Splits) (g : Aut K) (s : VertexPair K) :
    edgeOfPair K sp (permutePair K g s)=g • edgeOfPair K sp s := by
  apply Subtype.ext
  change (10+∑ x∈s.val.map (vertexAction K g).toEmbedding,x.val)/4=g ((10+∑ x∈s.val,x.val)/4)
  simp only [map_div₀,map_add,map_ofNat,map_sum,Finset.sum_map]
  rfl

/-- In every common Galois splitting field the map from unordered pairs
of distinct vertices to actual sixth-gap roots is a bijection. -/
theorem edgeOfPair_bijective [IsGalois ℚ K] (sp : ((rationalGap 6).map (algebraMap ℚ K)).Splits) :
    Function.Bijective (edgeOfPair K sp) := by
  have qs := quartic_splits_of_sextic K sp
  have size : Fintype.card (VertexPair K)=6 := by
    rw [Fintype.card_coe,card_powersetCard,card_univ,vertex_card K qs]; decide
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_,size.trans (gap_card_of_pos K (by decide : 0<6) sp).symm⟩
  have nonempty := Fintype.card_pos_iff.mp (size ▸ (by decide : 0<6))
  obtain ⟨s⟩ := nonempty
  intro y
  let x := edgeOfPair K sp s
  have irr := GapFamilies.irreducible_gap_rat (by decide : 0<6)
  have ha := minpoly.eq_of_irreducible irr (mem_rootSet.mp x.prop).2
  have hb := minpoly.eq_of_irreducible irr (mem_rootSet.mp y.prop).2
  obtain ⟨g,hg⟩ := (Normal.minpoly_eq_iff_mem_orbit K).mp (hb.symm.trans ha)
  exact ⟨permutePair K g s,(permutePair_edge K sp g s).trans (Subtype.ext hg)⟩

#print axioms VertexPair
#print axioms edgeOfPair
#print axioms permutePair
#print axioms permutePair_edge
#print axioms edgeOfPair_bijective
end
end Erdos478.TetrahedralGap
