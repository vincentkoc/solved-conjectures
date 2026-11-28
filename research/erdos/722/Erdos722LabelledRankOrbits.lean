import Erdos722GlobalRankSymmetry

/-! # Counts of labelled systems in an unrestricted rank class -/

namespace Erdos722.QuadSwitch
open Finset Equiv MulAction
open scoped Classical
noncomputable section

def binaryCheckCoordinates (d : ℕ) :
    Multiplicative (checkGroup (binaryBase d).val) ≃* Multiplicative (Fin (d+1) → ZMod 2) := by
  let S := AddSubgroup.toZModSubmodule 2 (checkGroup (binaryBase d).val)
  have card : Nat.card S=2^(d+1) := binaryBase_checks d
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=S)] at card
  have dim : Module.finrank (ZMod 2) S=d+1 :=
    Nat.pow_right_injective (by decide : 2≤2) (by simpa [Nat.card_eq_fintype_card] using card)
  let L : S ≃ₗ[ZMod 2] (Fin (d+1) → ZMod 2) :=
    (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by simpa using dim)).some
  exact L.toAddEquiv.toMultiplicative

theorem standard_group_coordinates (d : ℕ) (D : Finset (Finset (RankPoints d))) :
    standardRankGroup d (classOf D) ↔ Nonempty (Multiplicative (Fin (d+1) → ZMod 2) ≃* automorphisms D) := by
  rw [standard_group_iff]
  exact ⟨fun ⟨e⟩ => ⟨(binaryCheckCoordinates d).symm.trans e⟩,fun ⟨e⟩ => ⟨(binaryCheckCoordinates d).trans e⟩⟩

@[instance_reducible] private def permutationAction (V : Type*) : MulAction (Perm V) (Finset (Finset V)) where
  smul e D := e.finsetCongr.finsetCongr D
  one_smul _ := by change (Equiv.refl V).finsetCongr.finsetCongr _=_; simp
  mul_smul e f D := by
    change (f.trans e).finsetCongr.finsetCongr D=e.finsetCongr.finsetCongr (f.finsetCongr.finsetCongr D)
    rw [← Equiv.finsetCongr_trans,← Equiv.finsetCongr_trans,Equiv.trans_apply]

def rankClassLabels (d : ℕ) (C : DesignClass (RankPoints d)) :=
  (nextRankSystems d).filter (fun D => classOf D=C)

theorem rank_label_stabilizer (d : ℕ) {D : Finset (Finset (RankPoints d))} (hD : D∈nextRankSystems d) :
    (rankClassLabels d (classOf D)).card*Nat.card (automorphisms D)=(2^(d+1)).factorial := by
  classical
  let _ := permutationAction (RankPoints d)
  let G := Perm (RankPoints d)
  have iff' (E : Finset (Finset (RankPoints d))) : E∈rankClassLabels d (classOf D) ↔ E∈orbit G D := by
    constructor
    · intro he
      have iso := class_eq_iff.mp (mem_filter.mp he).2
      exact (designIsoSetoid _).iseqv.symm (x:=E) (y:=D) iso
    · rintro ⟨g,rfl⟩
      have iso : Isomorphic D (g • D) := ⟨g,rfl⟩
      obtain ⟨design,rank⟩ := (mem_filter.mp hD).2
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,relabel_quadruples g design,(iso_incidence_rank iso).symm.trans rank⟩,
        (class_eq_iff.mpr iso).symm⟩
  let e : rankClassLabels d (classOf D) ≃ orbit G D := (Equiv.refl _).subtypeEquiv iff'
  have card := Nat.card_congr (orbitProdStabilizerEquivGroup G D)
  rw [Nat.card_prod,← Nat.card_congr e,Nat.card_eq_finsetCard] at card
  exact card.trans (by simp [G,RankPoints,Nat.card_eq_fintype_card,Fintype.card_perm])

theorem label_switch_weight (d : ℕ) {C : DesignClass (RankPoints d)} (hC : C∈nextRankClasses d) :
    (rankClassLabels d C).card*liftOrder d=(classFibre d C).card*(2^(d+1)).factorial := by
  obtain ⟨s,ng,rfl⟩ := (next_class_mem _).mp hC
  let H := binaryBase d
  let D := binaryDouble d s
  have member : D∈nextRankSystems d := mem_filter.mpr ⟨mem_univ _,binaryDouble_design d s,(binaryDouble_next_rank d s).mpr ng⟩
  have aut : Nat.card (SwitchStabilizer H.prop s)=Nat.card (automorphisms D) :=
    Nat.card_congr ((nongaugeStabilizerAut H.prop (binaryBase_separates d) s ng).trans (automorphismRelabel (binaryStepLabels d) _)).toEquiv
  have h := (class_fibre_stabilizer d s).trans (binary_lift_card d)
  rw [aut] at h
  rw [← h,← rank_label_stabilizer d member]
  ring

#print axioms binaryCheckCoordinates
#print axioms standard_group_coordinates
#print axioms rankClassLabels
#print axioms rank_label_stabilizer
#print axioms label_switch_weight
end
end Erdos722.QuadSwitch
