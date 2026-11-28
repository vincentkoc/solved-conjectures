import Green51DualSections
import Green51ShortenedProfiles
import Green51ElevenRelations
import Green51FlatSections

/-! # A fifteen-point hyperplane section of every affine-flat avoiding eighteen-set -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open Green51ShortenedColumns Green51ShortenedProfiles Green51WeightTransform
open scoped Classical Pointwise
namespace Green51EighteenSection
local notation "F" => ZMod 2
local notation "V" => Cube 11

private theorem weight_three {A : Finset V} (size : A.card=18) (avoid : ¬∃ p, FlatAt A p)
    (D : Presentation A) : ∃ z ∈ dualWords D.P.ker, (supp z).card=3 := by
  classical
  have absent : Green51ShortenedProfiles.multiplicity D.P.ker 16=0 := by
    rw [Green51ShortenedProfiles.multiplicity,card_eq_zero,eq_empty_iff_forall_notMem]
    intro c hc
    have zero : syndrome (selected A c.val)=0 := congrArg Prod.snd ((D.eval c.val).symm.trans c.property)
    obtain ⟨p,hp⟩ := Green51ElevenRelations.affine_of_sixteen_sum (selected A c.val)
      ((selected_card A c.val).trans (mem_filter.mp hc).2) zero
    exact avoid ⟨p,Green51FlatSections.flat_mono (selected_sub A c.val) hp⟩
  have h := profile D.P.ker (by omega) (by omega) (le_of_eq D.rank.symm) D.allowed
  rw [absent] at h
  generalize a : Green51ShortenedProfiles.multiplicity D.P.ker 8=k at h
  generalize b : Green51ShortenedProfiles.multiplicity D.P.ker 12=j at h
  generalize d : ((dualWords D.P.ker).filter fun z => (supp z).card=3).card=m at h
  have six : m=6 := by
    simp only [size,profiles,mem_insert,mem_singleton,Prod.mk.injEq] at h
    omega
  have pos : 0<((dualWords D.P.ker).filter fun z => (supp z).card=3).card := by omega
  obtain ⟨z,hz⟩ := card_pos.mp pos
  exact ⟨z,(mem_filter.mp hz).1,(mem_filter.mp hz).2⟩

private theorem unit_column {A : Finset V} (D : Presentation A) (i : Fin A.card) :
    D.P (Pi.single i 1)=(1,(A.equivFin.symm i).val) := by
  have hs : supp (Pi.single i (1:F))={i} := by
    ext t
    by_cases eq:t=i <;> simp [supp,Pi.single_apply,eq]
  rw [D.eval]
  simp [selected,syndrome,hs]
  rfl

/-- A hyperplane contains exactly fifteen of the eighteen labels whenever
their double has no affine three-space. Its parallel mate contains the remaining three. -/
theorem hyperplane (A : Finset V) (size : A.card=18) (avoid : ¬∃ p, FlatAt A p) :
    ∃ (L : V →ₗ[F] F) (c:F), L≠0 ∧ (A.filter (fun x => L x=c)).card=15 := by
  classical
  obtain ⟨D⟩ := presentation (by omega) (by omega) (fun h => avoid ⟨0,h⟩)
  obtain ⟨z,dual,weight⟩ := weight_three size avoid D
  obtain ⟨L,c,nz,count⟩ := Green51DualSections.level D.P D.onto (unit_column D) dual (by omega) (by omega)
  exact ⟨L,c,nz,by omega⟩

end Green51EighteenSection
#print axioms Green51EighteenSection.hyperplane
