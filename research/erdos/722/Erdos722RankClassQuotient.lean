import Erdos722WholeRankStratum
import Erdos722BinaryOrbitEstimate

/-! # Unrestricted isomorphism classes of the full next-rank stratum -/

namespace Erdos722.QuadSwitch
open Finset Equiv
open scoped Classical
noncomputable section

abbrev DesignClass (V : Type*) := Quotient (designIsoSetoid V)
def classOf {V : Type*} (D : Finset (Finset V)) : DesignClass V := Quotient.mk _ D

theorem class_eq_iff {V : Type*} {D E : Finset (Finset V)} : classOf D=classOf E ↔ Isomorphic D E :=
  ⟨Quotient.exact,fun h => @Quotient.sound _ (designIsoSetoid V) D E h⟩

private theorem forward_iso {V W : Type*} (e : V ≃ W) {D E : Finset (Finset V)} (iso : Isomorphic D E) :
    Isomorphic (e.finsetCongr.finsetCongr D) (e.finsetCongr.finsetCongr E) := by
  obtain ⟨σ,he⟩ := iso
  refine ⟨e.permCongr σ,?_⟩
  rw [Equiv.permCongr_def,← Equiv.finsetCongr_trans,← Equiv.finsetCongr_trans,
    ← Equiv.finsetCongr_trans,← Equiv.finsetCongr_trans]
  simp only [Equiv.trans_apply,← Equiv.finsetCongr_symm,Equiv.symm_apply_apply,he]

theorem relabel_iso_iff {V W : Type*} (e : V ≃ W) {D E : Finset (Finset V)} :
    Isomorphic (e.finsetCongr.finsetCongr D) (e.finsetCongr.finsetCongr E) ↔ Isomorphic D E := by
  refine ⟨fun h => ?_,forward_iso e⟩
  simpa only [← Equiv.finsetCongr_symm,Equiv.symm_apply_apply] using forward_iso e.symm h

abbrev RankPoints (d : ℕ) := Fin (2^(d+1))
abbrev Switches (d : ℕ) := (binaryBase d).val → Bool

def nextRankSystems (d : ℕ) : Finset (Finset (Finset (RankPoints d))) :=
  univ.filter fun D => D.IsBlockDesign 3 4 ∧ (binaryIncidence D).rank=2^(d+1)-(d+1)
def nextRankClasses (d : ℕ) := (nextRankSystems d).image classOf
def switchClassImage (d : ℕ) := univ.image (fun s : Switches d => classOf (binaryDouble d s))
def affineClass (d : ℕ) := classOf (binaryDouble d (fun _ => false))

theorem next_class_mem {d : ℕ} (C : DesignClass (RankPoints d)) :
    C∈nextRankClasses d ↔ ∃ s : Switches d, ¬Coboundary s ∧ classOf (binaryDouble d s)=C := by
  constructor
  · intro h
    obtain ⟨D,hD,rfl⟩ := mem_image.mp h
    obtain ⟨s,ng,iso⟩ := (next_rank_iff_switch d D).mp (mem_filter.mp hD).2
    exact ⟨s,ng,(class_eq_iff.mpr iso).symm⟩
  · rintro ⟨s,ng,rfl⟩
    exact mem_image.mpr ⟨_,mem_filter.mpr ⟨mem_univ _,binaryDouble_design d s,(binaryDouble_next_rank d s).mpr ng⟩,rfl⟩

theorem affine_not_next (d : ℕ) : affineClass d∉nextRankClasses d := by
  intro h
  obtain ⟨s,ng,eq⟩ := (next_class_mem _).mp h
  have iso := class_eq_iff.mp eq
  have cz : Coboundary (H:=(binaryBase d).val) (fun _ => false) :=
    ⟨fun _ => 0,fun i => by simp [bitValue,blockSum]⟩
  exact ng ((isomorphic_coboundary (binaryBase d).prop (binaryBase_separates d)
    ((relabel_iso_iff (binaryStepLabels d)).mp iso)).mpr cz)

theorem class_image_split (d : ℕ) : switchClassImage d=insert (affineClass d) (nextRankClasses d) := by
  ext C
  constructor
  · intro h
    obtain ⟨s,_,rfl⟩ := mem_image.mp h
    by_cases cs : Coboundary s
    · exact mem_insert.mpr (.inl (class_eq_iff.mpr (forward_iso (binaryStepLabels d)
        (coboundary_zero_iso (binaryBase d).prop cs))))
    · exact mem_insert_of_mem ((next_class_mem _).mpr ⟨s,cs,rfl⟩)
  · intro h
    rcases mem_insert.mp h with rfl|v
    · exact mem_image.mpr ⟨_,mem_univ _,rfl⟩
    · obtain ⟨s,_,rfl⟩ := (next_class_mem _).mp v
      exact mem_image.mpr ⟨s,mem_univ _,rfl⟩

/-- All switched classes consist of exactly one minimum-rank affine class and
the unrestricted classes of *all* systems at the next binary rank. -/
theorem whole_rank_class_count (d : ℕ) :
    Nat.card (SwitchClasses (binaryBase d).prop)=(nextRankClasses d).card+1 := by
  classical
  let F (s : Switches d) : switchClassImage d := ⟨_,mem_image.mpr ⟨s,mem_univ _,rfl⟩⟩
  let g : SwitchClasses (binaryBase d).prop → switchClassImage d :=
    Quotient.lift F (fun x y h => Subtype.ext (class_eq_iff.mpr (forward_iso (binaryStepLabels d) h)))
  have bij : Function.Bijective g := by
    constructor
    · intro x y
      induction x using Quotient.inductionOn with | _ s =>
        induction y using Quotient.inductionOn with | _ t =>
          intro he
          exact Quotient.sound ((relabel_iso_iff (binaryStepLabels d)).mp
            (class_eq_iff.mp (congrArg Subtype.val he)))
    · rintro ⟨C,hC⟩
      obtain ⟨s,_,rfl⟩ := mem_image.mp hC
      exact ⟨Quotient.mk _ s,rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective g bij),Nat.card_eq_finsetCard,class_image_split,card_insert_of_notMem (affine_not_next d)]

#print axioms DesignClass
#print axioms classOf
#print axioms class_eq_iff
#print axioms relabel_iso_iff
#print axioms RankPoints
#print axioms Switches
#print axioms nextRankSystems
#print axioms nextRankClasses
#print axioms switchClassImage
#print axioms affineClass
#print axioms next_class_mem
#print axioms affine_not_next
#print axioms class_image_split
#print axioms whole_rank_class_count
end
end Erdos722.QuadSwitch
