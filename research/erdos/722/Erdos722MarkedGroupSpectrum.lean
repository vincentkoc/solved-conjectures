import Erdos722MarkedClassCounts

/-! # Elementary abelian point groups at one binary rank of Steiner quadruple systems -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

private theorem small_dimension {k : ℕ} (hk : k≤2) : ∃ s : Colour, fixedDimension s=k := by
  interval_cases k
  · exact ⟨threeCycle,by decide +kernel⟩
  · exact ⟨Equiv.swap 0 1,by decide +kernel⟩
  · exact ⟨1,by decide +kernel⟩

private theorem distribute {A : Type*} [DecidableEq A] (S : Finset A) (j : ℕ) (hj : j≤2*S.card) :
    ∃ c : A → Colour, ∑ i ∈ S, fixedDimension (c i)=j := by
  induction S using Finset.induction_on generalizing j with
  | empty =>
    simp only [card_empty,mul_zero,Nat.le_zero] at hj
    exact ⟨fun _ => threeCycle,by simp [hj]⟩
  | @insert a S ha ih =>
    rw [card_insert_of_notMem ha] at hj
    let k := min 2 j
    have bound : j-k≤2*S.card := by dsimp [k]; omega
    obtain ⟨old,sum⟩ := ih (j-k) bound
    obtain ⟨s,hs⟩ := small_dimension (min_le_left 2 j)
    let c (i : A) := if i=a then s else old i
    refine ⟨c,?_⟩
    have oldSum : ∑ i ∈ S, fixedDimension (c i)=∑ i ∈ S, fixedDimension (old i) := by
      apply sum_congr rfl
      rintro i hi
      simp only [c,if_neg (show i≠a by rintro rfl; exact ha hi)]
    rw [sum_insert ha,oldSum,sum,show c a=s by simp [c],hs]
    dsimp [k]
    omega

theorem groupDimension_range (d : ℕ) {j : ℕ} (hj : j≤2*(d+1)) :
    ∃ c : affineBasisMarks d → Colour, groupDimension d c=j :=
  distribute univ j (by simpa only [card_univ,Fintype.card_coe,basis_mark_count] using hj)

theorem marked_elementary (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) (u : CubeOffsets d)
    (a b : automorphisms (markedDesign d hd c u)) : a*b=b*a ∧ a*a=1 := by
  let e := markedPointGroup d hd c u
  obtain ⟨x,rfl⟩ := e.surjective a
  obtain ⟨y,rfl⟩ := e.surjective b
  refine ⟨by rw [← map_mul,← map_mul,mul_comm x y],?_⟩
  have xx : x*x=1 := by
    apply Multiplicative.toAdd.injective
    exact Subtype.ext (funext fun i => fibre_double (x.toAdd.val i))
  rw [← map_mul,xx,map_one]

/-- For each power of two in the indicated range a single fixed coefficient pattern
has this exact number of unrestricted classes, all with the prescribed full group. -/
theorem marked_group_spectrum (d : ℕ) (hd : 6≤d) (j : ℕ) (hj : j≤2*(d+1)) :
    ∃ c : affineBasisMarks d → Colour,
      (markedClasses d hd c).card=4^(blockNumber (2^d)-2^d)*2^j ∧
      ∀ u : CubeOffsets d, let D := markedDesign d hd c u
        D.IsBlockDesign 3 4 ∧ (binaryIncidence D).rank+(d+1)=4*2^d ∧
        Nat.card (automorphisms D)=2^j ∧ ∀ a b : automorphisms D, a*b=b*a ∧ a*a=1 := by
  obtain ⟨c,hc⟩ := groupDimension_range d hj
  refine ⟨c,by rw [marked_class_count,hc],fun u => ?_⟩
  obtain ⟨design,rank⟩ := marked_design_rank d hd c u
  exact ⟨design,rank,by rw [marked_group_card,hc],marked_elementary d hd c u⟩

/-- Every offset of the all-three-cycle pattern gives a point-asymmetric host design. -/
theorem asymmetric_marked_family (d : ℕ) (hd : 6≤d) :
    let c : affineBasisMarks d → Colour := fun _ => threeCycle
    (markedClasses d hd c).card=4^(blockNumber (2^d)-2^d) ∧
      ∀ u : CubeOffsets d, let D := markedDesign d hd c u
        D.IsBlockDesign 3 4 ∧ (binaryIncidence D).rank+(d+1)=4*2^d ∧ ∀ e : automorphisms D, e=1 := by
  let c : affineBasisMarks d → Colour := fun _ => threeCycle
  have dim : groupDimension d c=0 := by simp [groupDimension,c,show fixedDimension threeCycle=0 by decide +kernel]
  refine ⟨by rw [marked_class_count,dim,pow_zero,mul_one],fun u => ?_⟩
  obtain ⟨design,rank⟩ := marked_design_rank d hd c u
  have card := marked_group_card d hd c u
  rw [dim,pow_zero] at card
  exact ⟨design,rank,fun e => (Nat.card_eq_one_iff_unique.mp card).1.elim e 1⟩

theorem asymmetric_256_classes : (markedClasses 6 (by decide) (fun _ => threeCycle)).card=4^10352 := by
  rw [(asymmetric_marked_family 6 (by decide)).1]
  congr 1

#print axioms groupDimension_range
#print axioms marked_elementary
#print axioms marked_group_spectrum
#print axioms asymmetric_marked_family
#print axioms asymmetric_256_classes
end
end Erdos722.FourPoint
