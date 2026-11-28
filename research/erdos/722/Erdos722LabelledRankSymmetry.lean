import Erdos722LabelledRankMass

/-! # Uniform labelled sampling inside the next binary rank -/

namespace Erdos722.QuadSwitch
open Finset
open scoped Classical
noncomputable section

def exceptionalRankSystems (d : ℕ) :=
  (nextRankSystems d).filter fun D => classOf D∈exceptionalRankClasses d

private theorem label_weights (d : ℕ) {C : DesignClass (RankPoints d)} (hC : C∈nextRankClasses d) :
    let c := 2^(d+1)
    let L := (rankClassLabels d C).card
    (C∈exceptionalRankClasses d → 2*c*L≤c.factorial) ∧ (C∉exceptionalRankClasses d → c*L=c.factorial) := by
  obtain ⟨s,ng,rfl⟩ := (next_class_mem _).mp hC
  let H := binaryBase d
  let D := binaryDouble d s
  have hD : D∈nextRankSystems d := mem_filter.mpr ⟨mem_univ _,binaryDouble_design d s,(binaryDouble_next_rank d s).mpr ng⟩
  have mass := rank_label_stabilizer d hD
  constructor
  · intro bad
    have lower := bad_stabilizer_twice d s bad
    have aut : Nat.card (SwitchStabilizer H.prop s)=Nat.card (automorphisms D) :=
      Nat.card_congr ((nongaugeStabilizerAut H.prop (binaryBase_separates d) s ng).trans (automorphismRelabel (binaryStepLabels d) _)).toEquiv
    rw [aut] at lower
    exact (Nat.mul_le_mul_right _ lower).trans_eq ((Nat.mul_comm ..).trans mass)
  · intro good
    have standard : standardRankGroup d (classOf D) := by
      by_contra bad
      exact good (mem_filter.mpr ⟨hC,bad⟩)
    obtain ⟨e⟩ := (standard_group_iff d D).mp standard
    have count : Nat.card (automorphisms D)=2^(d+1) := (Nat.card_congr e.toEquiv).symm.trans (binaryBase_checks d)
    rw [count] at mass
    exact (Nat.mul_comm ..).trans mass

/-- Weighting each isomorphism class by its number of labellings further
reduces the exceptional proportion. Both sides are integers. -/
theorem labelled_rank_symmetry (d : ℕ) (hd : 7≤d) :
    (exceptionalRankSystems d).card*(2*(2^d*2^((2^d)^3/1024))-1)≤(nextRankSystems d).card := by
  classical
  let N := nextRankClasses d
  let B := exceptionalRankClasses d
  let I := N \ B
  let S := nextRankSystems d
  let T := exceptionalRankSystems d
  let c := 2^(d+1)
  let R := 2^d*2^((2^d)^3/1024)
  let L (C : DesignClass (RankPoints d)) := (rankClassLabels d C).card
  have sub : B⊆N := fun _ h => (mem_filter.mp h).1
  have cnt := global_rank_symmetry d hd
  have cost : B.card*R≤N.card := by simpa only [R,← Nat.mul_assoc] using cnt
  have nr : 1≤R := by change 0<2^d*2^((2^d)^3/1024); positivity
  have extra : B.card*(R-1)≤I.card := by
    have eq : R-1+1=R := Nat.sub_add_cancel nr
    rw [← eq,Nat.mul_add,Nat.mul_one] at cost
    change _≤(N \ B).card
    rw [card_sdiff_of_subset sub]
    omega
  have badSum : ∑ C∈B,L C=T.card := sum_card_fiberwise_eq_card_filter S B classOf
  have allSum : ∑ C∈N,L C=S.card := (card_eq_sum_card_image classOf S).symm
  have split : (∑ C∈I,L C)+T.card=S.card := by rw [← badSum,← allSum]; exact sum_sdiff sub
  have badMass : 2*c*T.card≤B.card*c.factorial := by
    rw [← badSum,Finset.mul_sum]
    calc
      _ ≤ ∑ _∈B,c.factorial := sum_le_sum fun C h => (label_weights d (sub h)).1 h
      _ = _ := by simp
  have goodMass : c*(∑ C∈I,L C)=I.card*c.factorial := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ _∈I,c.factorial := sum_congr rfl fun C h => (label_weights d (mem_sdiff.mp h).1).2 (mem_sdiff.mp h).2
      _ = _ := by simp
  have scaled : (2*T.card*(R-1))*c≤(∑ C∈I,L C)*c := calc
    _ = (2*c*T.card)*(R-1) := by ring
    _ ≤ (B.card*c.factorial)*(R-1) := Nat.mul_le_mul_right _ badMass
    _ = (B.card*(R-1))*c.factorial := by ring
    _ ≤ I.card*c.factorial := Nat.mul_le_mul_right _ extra
    _ = _ := goodMass.symm.trans (Nat.mul_comm ..)
  have raw := Nat.le_of_mul_le_mul_right scaled (show 0<c by dsimp [c]; positivity)
  change T.card*(2*R-1)≤S.card
  rw [show 2*R-1=2*(R-1)+1 by omega,Nat.mul_add,Nat.mul_one]
  nlinarith only [raw,split]

#print axioms exceptionalRankSystems
#print axioms labelled_rank_symmetry
end
end Erdos722.QuadSwitch
