import Erdos478LowPermutationCertificates
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # A three-witness criterion for a full joint permutation action -/

namespace Erdos478.LowGapAction
open Equiv
variable {G : Type*} [Group G]

abbrev PairGroup (r : Perm (Fin 4)) := Subgroup.centralizer {r}

def jointAction (a : G →* Small) (b : G →* Perm (Fin 4)) (r : Perm (Fin 4))
    (comm : ∀ g, b g*r=r*b g) : G →* Small × PairGroup r :=
  a.prod (b.codRestrict (PairGroup r) fun g => Subgroup.mem_centralizer_singleton_iff.mpr (comm g))

/-- Surjectivity requires two witnesses fixing the quartic and a third fixing
exactly two quartic roots. Transitivity is required only on the quartic. -/
theorem joint_surjective (a : G →* Small) (b : G →* Perm (Fin 4)) (r : Perm (Fin 4))
    (inv : r*r=1) (free : pointCount r=0) (comm : ∀ g, b g*r=r*b g)
    (trans : ∀ x y : Fin 4, ∃ g, b g x=y)
    (hu : ∃ u, pointCount (a u).1=0 ∧ pointCount (a u).2=0 ∧ pointCount (b u)=4)
    (hv : ∃ v, pointCount (a v).2=1 ∧ pointCount (b v)=4)
    (hs : ∃ s, pointCount (b s)=2) : Function.Surjective (jointAction a b r comm) := by
  obtain ⟨u,q,c,cu⟩ := hu
  obtain ⟨v,m,cv⟩ := hv
  have trivialU := four_fixed _ cu
  have trivialV := four_fixed _ cv
  have pure (z : Small) : ∃ g, a g=z ∧ b g=1 := by
    obtain ⟨i,j,word⟩ := two_generators _ _ q c m z
    exact ⟨u^i.val*v^j.val,by simpa only [map_mul,map_pow] using word,
      by simp [trivialU,trivialV]⟩
  obtain ⟨s,two⟩ := hs
  obtain ⟨x,y,hx,hy⟩ := two_fixed_moved _ two
  obtain ⟨t,ht⟩ := trans x y
  rintro ⟨z,h⟩
  obtain ⟨i,j,k,word⟩ := pair_generators r (b s) (b t) inv free (comm _) (comm _) two
    ⟨x,hx,by rwa [ht]⟩ h.val (Subgroup.mem_centralizer_singleton_iff.mp h.prop)
  let g := s^i.val*(t*s*t⁻¹)^j.val*t^k.val
  have bh : b g=h.val := by simpa only [g,map_mul,map_pow,map_inv] using word
  obtain ⟨p,ap,bp⟩ := pure (z*(a g)⁻¹)
  refine ⟨p*g,Prod.ext ?_ (Subtype.ext ?_)⟩
  · change a (p*g)=z
    simp [ap]
  · change b (p*g)=h.val
    simp [bp,bh]

#print axioms PairGroup
#print axioms jointAction
#print axioms joint_surjective
end Erdos478.LowGapAction
