import Erdos478SexticEndpoints
import Erdos478SeparableRootMean
import Erdos478GapVariance

/-!
# Distinct positive endpoints from a finite family of prime gaps

Outside a finite resultant cutoff the endpoint sets are pairwise disjoint.
Their union therefore counts distinct nonminimal occurrences of factorial
residues in precisely the upstream interval.
-/

namespace Erdos478.GapBands
open Polynomial Finset SplittingDensity GapFamilies GapVariance
open scoped Classical
noncomputable section

def joined (s : Finset Nat.Primes) (p : ℕ) := s.biUnion fun i => endpoints i.val p

private def pairTest (k l : ℕ) := gapPoly k*gapPoly l
private def bad (k l : ℕ) := ((pairTest k l).resultant (pairTest k l).derivative).natAbs

private theorem endpoint_root {p k j : ℕ} (hp : p.Prime) (hj : j∈endpoints k p) :
    ((gapPoly k).map (Int.castRingHom (ZMod p))).IsRoot (j:ZMod p) := by
  rw [SexticGap.endpoints_eq_short_product hp] at hj
  have h : (j.descFactorial k : ZMod p)=1 := by
    have h₀ : j.descFactorial k%p=1%p := by
      simpa only [Nat.mod_eq_of_lt hp.one_lt] using (mem_filter.mp hj).2
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff' _ 1 p).mpr h₀
  simpa [gapPoly,IsRoot,descPochhammer_eval_eq_descFactorial,sub_eq_zero] using h

private theorem separated {p k l : ℕ} [hp : Fact p.Prime] (hk : 0<k) (hl : 0<l) (hkl : k≠l)
    (hbig : bad k l<p) : Disjoint (endpoints k p) (endpoints l p) := by
  have ms := (SplittingDensity.gap_degree hk).mul (SplittingDensity.gap_degree hl)
  have hdeg : (pairTest k l).natDegree≠0 := by simpa [pairTest,ms.natDegree_eq] using (show k+l≠0 by omega)
  have hs : ((pairTest k l).map (Int.castRingHom ℚ)).Separable := by
    have h := separable_gap_family ({k,l}:Finset ℕ) (by simpa using And.intro hk hl)
    simpa [pairTest,gapPoly,hkl] using h
  have modsep := separable_mod_above_resultant _ hdeg hs (p:=p) hbig
  rw [pairTest,Polynomial.map_mul] at modsep
  apply disjoint_left.mpr
  intro j hj hj'
  exact not_isUnit_X_sub_C (j:ZMod p) (isUnit_of_self_mul_dvd_separable modsep
    (mul_dvd_mul (dvd_iff_isRoot.mpr (endpoint_root hp.out hj)) (dvd_iff_isRoot.mpr (endpoint_root hp.out hj'))))

/-- For every fixed finite family the number of distinct endpoints agrees
with the sum of the modular root counts at all sufficiently large primes. -/
theorem eventual_endpoint_sum (s : Finset Nat.Primes) :
    ∃ B : ℕ, ∀ p>B, p.Prime →
      ((joined s p).card:ℝ)=∑ i ∈ s, observation i p := by
  classical
  let B := max (s.sup fun i => cutoff i.val) (s.sup fun i => s.sup fun j => bad i.val j.val)
  refine ⟨B,?_⟩
  intro p hbig hp
  let : Fact p.Prime := ⟨hp⟩
  have pairwise : (s : Set Nat.Primes).PairwiseDisjoint fun i => endpoints i.val p := by
    intro i hi j hj hn
    apply separated i.property.pos j.property.pos (fun e => hn (Subtype.ext e))
    exact (le_sup (f:=fun t : Nat.Primes => bad i.val t.val) hj).trans_lt
      ((le_sup (f:=fun t : Nat.Primes => s.sup fun u => bad t.val u.val) hi).trans_lt
        ((le_max_right ..).trans_lt hbig))
  rw [joined,card_biUnion pairwise,Nat.cast_sum]
  apply sum_congr rfl
  intro i hi
  have hc : cutoff i.val<p := (le_sup hi).trans_lt ((le_max_left ..).trans_lt hbig)
  have deg := SplittingDensity.gap_degree i.property.pos
  have sep := separable_mod_above_resultant (gapPoly i.val) (deg.natDegree_eq.trans_ne i.property.ne_zero)
    (by simpa [gapPoly] using (irreducible_gap_rat i.property.pos).separable) ((le_max_right ..).trans_lt hc)
  change ((endpoints i.val p).card:ℝ)=RootMoments.roots (gapPoly i.val) p
  rw [endpoint_count i.property.two_le hc,CollisionLaw.count_roots _ deg.monic p sep]

/-- Every counted endpoint can be deleted from the upstream factorial image. -/
theorem joined_deficit (s : Finset Nat.Primes) (p : ℕ) :
    ((Ico 1 p).image (fun j => j.factorial%p)).card+(joined s p).card≤p-1 := by
  classical
  let V := Ico 1 p
  let U := joined s p
  let f := fun j : ℕ => j.factorial%p
  have rep {j} (hj : j∈U) : j∈V ∧ ∃ k∈V, k<j ∧ f k=f j := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hj
    obtain ⟨hx,he⟩ := mem_filter.mp hi
    obtain ⟨hl,hu⟩ := mem_Ico.mp hx
    have hp := i.property.pos
    exact ⟨mem_Ico.mpr ⟨by omega,hu⟩,j-i.val,mem_Ico.mpr ⟨by omega,by omega⟩,by omega,he⟩
  have cover : V.image f⊆(V\U).image f := by
    intro y hy
    have hit : ∃ j, j∈V ∧ f j=y := mem_image.mp hy
    obtain ⟨hm,he⟩ := Nat.find_spec hit
    refine mem_image.mpr ⟨_,mem_sdiff.mpr ⟨hm,?_⟩,he⟩
    intro h
    obtain ⟨k,hk,hl,hf⟩ := (rep h).2
    exact Nat.find_min hit hl ⟨hk,hf.trans he⟩
  have sub : U⊆V := fun _ hj => (rep hj).1
  have hl := (card_le_card cover).trans card_image_le
  rw [card_sdiff_of_subset sub] at hl
  have := card_le_card sub
  have hc : V.card=p-1 := Nat.card_Ico _ _
  change (V.image f).card+U.card≤p-1
  omega

#print axioms eventual_endpoint_sum
#print axioms joined_deficit
end
end Erdos478.GapBands
