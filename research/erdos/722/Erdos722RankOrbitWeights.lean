import Erdos722RankClassStabilizers

/-! # Orbit sizes and the cost of a larger full automorphism group -/

namespace Erdos722.QuadSwitch
open Finset Equiv MulAction
open scoped Classical
noncomputable section

def standardRankGroup (d : ℕ) (C : DesignClass (RankPoints d)) : Prop :=
  ∃ D : Finset (Finset (RankPoints d)), classOf D=C ∧
    Nonempty (Multiplicative (checkGroup (binaryBase d).val) ≃* automorphisms D)

theorem standard_group_iff (d : ℕ) (D : Finset (Finset (RankPoints d))) :
    standardRankGroup d (classOf D) ↔ Nonempty (Multiplicative (checkGroup (binaryBase d).val) ≃* automorphisms D) := by
  refine ⟨?_,fun h => ⟨D,rfl,h⟩⟩
  rintro ⟨E,eq,⟨f⟩⟩
  obtain ⟨e,rfl⟩ := class_eq_iff.mp eq
  exact ⟨f.trans (automorphismRelabel e E)⟩

def exceptionalRankClasses (d : ℕ) := (nextRankClasses d).filter (fun C => ¬standardRankGroup d C)
def classFibre (d : ℕ) (C : DesignClass (RankPoints d)) :=
  univ.filter fun s : Switches d => classOf (binaryDouble d s)=C

theorem class_fibre_stabilizer (d : ℕ) (s : Switches d) :
    (classFibre d (classOf (binaryDouble d s))).card*Nat.card (SwitchStabilizer (binaryBase d).prop s)=
      Nat.card (liftGroup (binaryBase d).val) := by
  classical
  let H := binaryBase d
  let _ := switchAction H.prop
  let G := liftGroup H.val
  have eq (t : Switches d) : classOf (binaryDouble d t)=classOf (binaryDouble d s) ↔ t∈orbit G s := by
    rw [class_eq_iff]
    change Isomorphic ((binaryStepLabels d).finsetCongr.finsetCongr _) ((binaryStepLabels d).finsetCongr.finsetCongr _) ↔ _
    rw [relabel_iso_iff]
    constructor
    · intro iso
      have inv := (designIsoSetoid _).iseqv.symm (x:=doubling H.prop t) (y:=doubling H.prop s) iso
      obtain ⟨σ,f,hm⟩ := (isomorphic_iff_matches H.prop (binaryBase_separates d) s t).mp inv
      let g := liftCoordinates H.val (⟨σ,matches_preserves hm⟩,f)
      exact ⟨g,doubling_injective H.prop ((act_relabels H.prop g s).symm.trans ((maps_doubling_iff ..).mpr hm))⟩
    · rintro ⟨g,rfl⟩
      exact (designIsoSetoid _).iseqv.symm (x:=doubling H.prop s) (y:=doubling H.prop (g • s)) ⟨g.val,act_relabels H.prop g s⟩
  let e : classFibre d (classOf (binaryDouble d s)) ≃ orbit G s :=
    (Equiv.refl _).subtypeEquiv fun t => by simpa [classFibre] using eq t
  have card := Nat.card_congr (orbitProdStabilizerEquivGroup G s)
  rw [Nat.card_prod,← Nat.card_congr e,Nat.card_eq_finsetCard] at card
  exact card

theorem bad_stabilizer_twice (d : ℕ) (s : Switches d) (h : classOf (binaryDouble d s)∈exceptionalRankClasses d) :
    2*2^(d+1)≤Nat.card (SwitchStabilizer (binaryBase d).prop s) := by
  let H := binaryBase d
  obtain ⟨next,bad⟩ := mem_filter.mp h
  have ng : ¬Coboundary s := by
    obtain ⟨t,nt,eq⟩ := (next_class_mem _).mp next
    exact fun cs => nt ((isomorphic_coboundary H.prop (binaryBase_separates d)
      ((relabel_iso_iff (binaryStepLabels d)).mp (class_eq_iff.mp eq))).mpr cs)
  have ne : Nat.card (SwitchStabilizer H.prop s)≠Nat.card (Checks H.val) := by
    intro eq
    obtain ⟨g⟩ := smallest_stabilizer_group H.prop s eq
    exact bad ((standard_group_iff d _).mpr ⟨(g.trans (nongaugeStabilizerAut H.prop (binaryBase_separates d) s ng)).trans
      (automorphismRelabel (binaryStepLabels d) _)⟩)
  obtain ⟨k,hk⟩ := checks_dvd_stabilizer H.prop s
  have nz : 0<Nat.card (SwitchStabilizer H.prop s) := Nat.card_pos
  have two : 2≤k := by
    by_contra! low
    interval_cases k <;> simp_all
  have bc : Nat.card (Checks H.val)=2^(d+1) := binaryBase_checks d
  rw [hk,bc,mul_comm]
  exact Nat.mul_le_mul_left _ two

#print axioms standardRankGroup
#print axioms standard_group_iff
#print axioms exceptionalRankClasses
#print axioms classFibre
#print axioms class_fibre_stabilizer
#print axioms bad_stabilizer_twice
end
end Erdos722.QuadSwitch
