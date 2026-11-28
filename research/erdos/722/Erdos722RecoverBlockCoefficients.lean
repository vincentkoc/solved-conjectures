import Erdos722WeightedBlockTranslations

/-! # Recovering normalized linear coefficients from a transversal block relation -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch Equiv
open scoped Classical
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I] {Q : Rule I}

/-- Put any chosen input and output point of a base block in their specified positions. -/
theorem pointed_block_triple (B : Q.blocks) {i l : I} (hi : i∈B.val) (hl : l∈B.val) (il : i≠l) :
    ∃ j k, i≠j ∧ i≠k ∧ j≠k ∧ baseQuad Q i j k=B.val ∧ Q.complete i j k=l := by
  have prop := (Q.mem_blocks B.val).mp B.prop
  let S := (B.val.erase l).erase i
  have size : S.card=2 := by
    rw [show S=(B.val.erase l).erase i from rfl,card_erase_of_mem (mem_erase.mpr ⟨il,hi⟩),
      card_erase_of_mem hl,prop.1]
  obtain ⟨j,k,jk,eq⟩ := card_eq_two.mp size
  have mj : j∈S := by rw [eq]; simp
  have mk : k∈S := by rw [eq]; simp
  obtain ⟨ji,restj⟩ := mem_erase.mp mj
  obtain ⟨jl,inJ⟩ := mem_erase.mp restj
  obtain ⟨ki,restk⟩ := mem_erase.mp mk
  obtain ⟨kl,inK⟩ := mem_erase.mp restk
  have small : baseQuad Q i j k=B.val := by
    apply eq_of_subset_of_card_le
    · exact insert_subset (prop.2 i hi j inJ k inK) (insert_subset hi (insert_subset inJ (singleton_subset_iff.mpr inK)))
    · rw [prop.1]
      exact ((Q.mem_blocks _).mp (completed_block Q ji.symm ki.symm jk)).1.ge
  have locate : l∈baseQuad Q i j k := small ▸ hl
  simp only [baseQuad,mem_insert,mem_singleton,Ne.symm il,Ne.symm jl,Ne.symm kl,or_false] at locate
  exact ⟨j,k,ji.symm,ki.symm,jk,small,locate.symm⟩

/-- Agreement at an anchor on a block identifies its other coefficient maps
from two fillings with the same block set, even when their offsets differ. -/
theorem recover_coefficient (M : Matching I) (C D : IncidenceColours Q) (u v : BlockOffsets Q)
    (same : (colouredRule Q M C u).blocks=(colouredRule Q M D v).blocks)
    (B : Q.blocks) {l i : I} (hl : l∈B.val) (hi : i∈B.val) (anchor : C B l=D B l) :
    C B i=D B i := by
  by_cases il : i=l
  · simpa only [il] using anchor
  obtain ⟨j,k,ij,ik,jk,eq,last⟩ := pointed_block_triple B hi hl il
  let P := colouredRule Q M C u
  let T := colouredRule Q M D v
  have law (A : IncidenceColours Q) (w : BlockOffsets Q) (x : Fibre) :
      move (A B l) (((colouredRule Q M A w).complete (i,x) (j,0) (k,0)).2)=move (A B i) x+w B := by
    let b : Q.blocks := ⟨_,completed_block Q ij ik jk⟩
    have ident : b=B := Subtype.ext eq
    have h := blockwise_transversal Q M w (linearCoordinates A) ij ik jk x 0 0
    change move (A b (Q.complete i j k)) _=move (A b i) x+move (A b j) 0+move (A b k) 0+w b at h
    simpa only [ident,last,move_zero,add_zero] using h
  have test (x : Fibre) : move (C B i) x+u B=move (D B i) x+v B := by
    have eqv := completion_determined P T same (i,x) (j,0) (k,0)
    have left := law C u x
    change move (C B l) ((P.complete (i,x) (j,0) (k,0)).2)=_ at left
    rw [eqv,anchor] at left
    exact left.symm.trans (law D v x)
  have equal : u B=v B := by simpa only [move_zero,zero_add] using test 0
  apply Equiv.ext
  intro z
  have vEq := test (vector z)
  rw [equal,add_left_inj,move_vector,move_vector] at vEq
  simpa only [direction_vector] using congrArg direction vEq

#print axioms pointed_block_triple
#print axioms recover_coefficient
end
end Erdos722.FourPoint
