import Erdos478WilsonCyclotomicBijection
import Mathlib.Data.Finset.Prod

/-! # The exact cyclotomic collision count and its restriction to an arbitrary set -/

namespace Erdos478.CyclotomicProfiles
open Finset
open scoped Classical
noncomputable section
variable {F : Type*} [Field F]

/-- Ordered unequal arguments giving both multiplicative ratios in the specified set. -/
def offCollisions (A K : Finset F) := A.offDiag.filter fun xy =>
  (profileRatios xy.1 xy.2).1∈K ∧ (profileRatios xy.1 xy.2).2∈K

private def ratioMap (xy : F × F) := profileRatios xy.1 xy.2

private theorem ratio_injOn {A K : Finset F} (reg : ∀ x∈A, Regular x) :
    Set.InjOn (ratioMap (F:=F)) (↑(offCollisions A K) : Set (F × F)) := by
  rintro ⟨x,y⟩ h ⟨z,w⟩ h' eq
  obtain ⟨hx,hy,ne⟩ := mem_offDiag.mp (mem_filter.mp h).1
  have hw := (mem_offDiag.mp (mem_filter.mp h').1).2.1
  exact profile_injective (reg _ hx) (reg _ hy) (reg _ hw) ne eq

private theorem ratio_subset {A K : Finset F} (reg : ∀ x∈A, Regular x) :
    (offCollisions A K).image ratioMap ⊆ (K.erase 1).offDiag := by
  intro uv h
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := mem_image.mp h
  obtain ⟨hpair,hK⟩ := mem_filter.mp hxy
  obtain ⟨hx,hy,ne⟩ := mem_offDiag.mp hpair
  obtain ⟨hu,hv,neq⟩ := regular_ratios (reg _ hx) (reg _ hy) ne
  exact mem_offDiag.mpr ⟨mem_erase.mpr ⟨hu.2,hK.1⟩,mem_erase.mpr ⟨hv.2,hK.2⟩,neq⟩

theorem off_collision_bound {A K : Finset F} (reg : ∀ x∈A, Regular x) (one : (1:F)∈K) :
    (offCollisions A K).card ≤ (K.card-1)*(K.card-2) := by
  have bound := card_le_card (ratio_subset (K:=K) reg)
  rw [card_image_of_injOn (ratio_injOn reg),offDiag_card,card_erase_of_mem one] at bound
  rwa [← Nat.mul_sub_one,Nat.sub_sub] at bound

/-- Wilson's exact off-diagonal count. The set of allowed multipliers can be any set containing
one and avoiding zero. Being a subgroup is needed only for the interpretation as coset collisions. -/
theorem off_collision_exact [Fintype F] (K : Finset F) (one : (1:F)∈K) (nz : (0:F)∉K) :
    (offCollisions (univ.filter Regular) K).card=(K.card-1)*(K.card-2) := by
  let A : Finset F := univ.filter Regular
  have reg (x) (h : x∈A) := (mem_filter.mp h).2
  have equal : (offCollisions A K).image ratioMap=(K.erase 1).offDiag := by
    apply Subset.antisymm (ratio_subset reg)
    rintro ⟨u,v⟩ h
    obtain ⟨hu,hv,ne⟩ := mem_offDiag.mp h
    obtain ⟨u1,hu⟩ := mem_erase.mp hu
    obtain ⟨v1,hv⟩ := mem_erase.mp hv
    obtain ⟨x,y,rx,ry,xy,eq⟩ := profile_surjective (fun e => nz (e ▸ hu)) u1 (fun e => nz (e ▸ hv)) v1 ne
    apply mem_image.mpr
    refine ⟨(x,y),mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_filter.mpr ⟨mem_univ _,rx⟩,
      mem_filter.mpr ⟨mem_univ _,ry⟩,xy⟩,?_⟩,eq⟩
    change (profileRatios x y).1∈K ∧ (profileRatios x y).2∈K
    rw [eq]
    exact ⟨hu,hv⟩
  have count := congrArg Finset.card equal
  rw [card_image_of_injOn (ratio_injOn reg),offDiag_card,card_erase_of_mem one,← Nat.mul_sub_one,Nat.sub_sub] at count
  exact count

#print axioms offCollisions
#print axioms off_collision_bound
#print axioms off_collision_exact
end
end Erdos478.CyclotomicProfiles
