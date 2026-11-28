import Erdos722AffineTransversalGraphs

/-! # Transporting the affine stars under unrestricted point isomorphisms -/

namespace Erdos722.AffineStar
open Equiv Finset QuadCompletion FourPoint QuadSwitch
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]
variable {Q : Rule I} {P T : Rule (I × Fibre)} {M : Matching I}

/-- Coordinates recovered from an isomorphism of the two unlabelled block families. -/
structure FibreMap (Q : Rule I) (P T : Rule (I × Fibre)) (e : Perm (I × Fibre)) where
  base : Perm I
  fibre : I → Perm Fibre
  point (i x) : e (i,x)=(base i,fibre i x)
  projects (i j k) : base (Q.complete i j k)=Q.complete (base i) (base j) (base k)
  commutes (a b c) : e (P.complete a b c)=T.complete (e a) (e b) (e c)

theorem fibreMap_exists (src : Compatible Q M P) (dst : Compatible Q M T)
    (hyp : FibreHypotheses Q M) (e : Perm (I × Fibre))
    (iso : e.finsetCongr.finsetCongr P.blocks=T.blocks) : Nonempty (FibreMap Q P T e) := by
  obtain ⟨_,star⟩ := hyp.star
  have same (i j : I) (x y : Fibre) : i=j ↔ (e (i,x)).1=(e (j,y)).1 := by
    have eq := sameChecks_relabel e P.blocks (i,x) (j,y)
    rw [iso] at eq
    exact (sameChecks_four hyp.separates src star hyp.noFix _ _).symm.trans
      (eq.trans (sameChecks_four hyp.separates dst star hyp.noFix _ _))
  obtain ⟨b,f,coord⟩ := fibre_coordinates 0 e same
  have ec (p : I × Fibre) : e p=(b p.1,f p.1 p.2) := coord p.1 p.2
  have comm := completion_of_blocks P T e iso
  refine ⟨⟨b,f,coord,?_,comm⟩⟩
  intro i j k
  have eq := comm (i,0) (j,0) (k,0)
  rw [ec (P.complete ..),src.project,coord,coord,coord] at eq
  exact (congrArg Prod.fst eq).trans (dst.project ..)

variable {e : Perm (I × Fibre)}

def pull (c : FibreMap Q P T e) (g : I → Fibre) (i : I) : Fibre := (c.fibre i).symm (g (c.base i))

omit [DecidableEq I] [Fintype I] in
theorem pull_graph (c : FibreMap Q P T e) (i j k : I) (g : I → Fibre) :
    OnGraph Q P i j k (pull c g) ↔ OnGraph Q T (c.base i) (c.base j) (c.base k) g := by
  have ep (u : I) : e (u,pull c g u)=(c.base u,g (c.base u)) := by
    rw [c.point,pull,Equiv.apply_symm_apply]
  unfold OnGraph
  rw [← e.injective.eq_iff,c.commutes,ep,ep,ep,ep,c.projects]

omit [Fintype I] in
/-- Every affine star is sent to an affine star by the recovered base permutation. -/
theorem map_affine_star (c : FibreMap Q P T e) {o : I} (star : HasAffineStar Q P o) :
    HasAffineStar Q T (c.base o) := by
  intro i' j' k' ij ik jk mem
  obtain ⟨i,rfl⟩ := c.base.surjective i'
  obtain ⟨j,rfl⟩ := c.base.surjective j'
  obtain ⟨k,rfl⟩ := c.base.surjective k'
  have inside : o∈baseQuad Q i j k := by
    simpa only [baseQuad,← c.projects,mem_insert,mem_singleton,c.base.injective.eq_iff] using mem
  have H := star i j k (fun h => ij (congrArg _ h)) (fun h => ik (congrArg _ h))
    (fun h => jk (congrArg _ h)) inside
  intro f g h hf hg hh
  apply (pull_graph c i j k _).mp
  have eq : pull c (fun u => f u+g u+h u)=(fun u => pull c f u+pull c g u+pull c h u) :=
    funext fun u => fibre_mix_perm (c.fibre u).symm _ _ _
  rw [eq]
  exact H _ _ _ ((pull_graph ..).mpr hf) ((pull_graph ..).mpr hg) ((pull_graph ..).mpr hh)

#print axioms FibreMap
#print axioms fibreMap_exists
#print axioms pull
#print axioms pull_graph
#print axioms map_affine_star
end
end Erdos722.AffineStar
