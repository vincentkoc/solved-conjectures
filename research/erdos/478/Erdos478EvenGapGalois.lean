import Erdos478PairingCentralizer
import Erdos478EvenGapReflection
import Erdos478GapSplittingDegrees

/-!
# Galois symmetries of the even factorial gaps

Every rational automorphism preserves the midpoint reflection on the roots.
The resulting embedding bounds the splitting degree by the order of the
centralizer of a fixed-point-free involution.
-/

namespace Erdos478.SplittingDensity
open Polynomial Finset

/-- The splitting field of the even gap of length `2*r` has degree at most
`2^r * r!`. No maximality of its Galois group is assumed. -/
theorem even_gap_field_degree {r : ℕ} (hr : 0 < r) :
    Module.finrank ℚ (SplitField (gapPoly (2*r))) ≤ 2^r * r.factorial := by
  classical
  let F := (gapPoly (2*r)).map (Int.castRingHom ℚ)
  let K := F.SplittingField
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := SplittingField.instNormal F }
  let : Fact ((F.map (algebraMap ℚ K)).Splits) := ⟨SplittingField.splits F⟩
  have hpos : 0 < 2*r := by omega
  have hs : F.Separable := by
    simpa [F,gapPoly] using (GapFamilies.irreducible_gap_rat hpos).separable
  have hmon : F.Monic := (gap_degree hpos).monic.map _
  have hmap : F.map (algebraMap ℚ K) = descPochhammer K (2*r)-1 := by
    simp [F,gapPoly,Polynomial.map_sub,descPochhammer_map]
  let R := F.rootSet K
  have hmem (x : K) : x ∈ R ↔ (descPochhammer K (2*r)-1).IsRoot x := by
    rw [← hmap,Polynomial.IsRoot.def,eval_map_algebraMap]
    exact hmon.mem_rootSet
  have hpair (x : R) := EffectiveResolvent.two_even_roots (K:=K) (by norm_num) r
    (hmap ▸ hs.map) ((hmem x).mp x.property)
  let flip (x : R) : R := ⟨((2*r:ℕ):K)-1-x,(hmem _).mpr (hpair x).2⟩
  have hi (x : R) : flip (flip x) = x := by
    apply Subtype.ext
    change _-1-(_-1-(x:K))=(x:K)
    ring
  let g : Equiv.Perm R := ⟨flip,flip,hi,hi⟩
  have hg : g^2=1 := by
    ext x
    exact congrArg Subtype.val (hi x)
  have hf (x : R) : g x ≠ x := fun e => (hpair x).1 (congrArg Subtype.val e).symm
  have hc : Fintype.card R=2*r := (card_rootSet_eq_natDegree hs (SplittingField.splits F)).trans
    ((gap_degree hpos).monic.natDegree_map _ |>.trans (gap_degree hpos).natDegree_eq)
  let A := Gal.galActionHom F K
  have hcomm (a : F.Gal) : A a ∈ Subgroup.centralizer {g} := by
    obtain ⟨b,rfl⟩ := Gal.restrict_surjective F K a
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change ((A (Gal.restrict F K b) (g x) : R) : K) =
      ((2*r:ℕ):K)-1-((A (Gal.restrict F K b) x : R) : K)
    rw [show ((A (Gal.restrict F K b) (g x) : R) : K) = b (g x : K) from Gal.galActionHom_restrict ..,
      show ((A (Gal.restrict F K b) x : R) : K) = b (x : K) from Gal.galActionHom_restrict ..]
    change b (((2*r:ℕ):K)-1-x)=_
    simp only [map_sub,map_one]
    rw [show b ((2*r:ℕ):K) = ((2*r:ℕ):K) from map_natCast b (2*r)]
  let embed (a : F.Gal) : Subgroup.centralizer {g} := ⟨A a,hcomm a⟩
  have hinj : Function.Injective embed := fun _ _ h =>
    Gal.galActionHom_injective F K (congrArg Subtype.val h)
  calc
    Module.finrank ℚ K = Nat.card F.Gal := (IsGalois.card_aut_eq_finrank ℚ K).symm
    _ ≤ Nat.card (Subgroup.centralizer {g}) := Nat.card_le_card_of_injective _ hinj
    _ = _ := card_pairing_centralizer g hg hf hc

#print axioms even_gap_field_degree
end Erdos478.SplittingDensity
