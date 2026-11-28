import Erdos722SwitchOrbitAction
import Erdos722CubicSwitchBound

/-! # Unrestricted isomorphism classes and a fixed-point mass formula -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

def fixedSwitches (σ : automorphisms H) (f : V → Bool) : Finset (H → Bool) :=
  solutions (blockPerm σ.val σ.prop) (fun i => blockSum (bitValue ∘ f) i.val)

theorem mem_fixedSwitches (hH : H.IsBlockDesign 3 4) (σ : automorphisms H) (f : V → Bool) (s : H → Bool) :
    s∈fixedSwitches σ f ↔ (fibrePerm σ.val f).finsetCongr.finsetCongr (doubling hH s)=doubling hH s := by
  rw [maps_doubling_iff,matches_iff_equations _ _ _ _ σ.prop]
  simp [fixedSwitches,solutions]

/-- Count unrestricted isomorphism classes by summing fixed switches over the base permutations
and point flips. This includes the zero-switch class, whose automorphisms can mix fibres. -/
theorem switch_mass_formula [Nonempty V] (hH : H.IsBlockDesign 3 4) (sep : Separates H) :
    Nat.card (SwitchClasses hH)*(Nat.card (automorphisms H)*2^Fintype.card V)=
      ∑ σ : automorphisms H, ∑ f : V → Bool, (fixedSwitches σ f).card := by
  classical
  let _ := switchAction hH
  let G := liftGroup H
  let X := H → Bool
  let Q := Quotient (MulAction.orbitRel G X)
  have equiv (p : automorphisms H × (V → Bool)) :
      MulAction.fixedBy X (liftCoordinates H p) ≃ (fixedSwitches p.1 p.2) := by
    apply (Equiv.refl X).subtypeEquiv
    intro s
    change actOnSwitch (liftCoordinates H p) s=s ↔ s∈fixedSwitches p.1 p.2
    rw [mem_fixedSwitches hH,← liftCoordinates_val p,act_relabels]
    exact doubling_injective hH |>.eq_iff.symm
  have burn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have gcard : Fintype.card G=Nat.card (automorphisms H)*2^Fintype.card V := by
    rw [← Fintype.card_congr (liftCoordinates H)]
    simp [Nat.card_eq_fintype_card]
  have qcard : Nat.card (SwitchClasses hH)=Fintype.card Q :=
    (class_orbits hH sep).trans Nat.card_eq_fintype_card
  rw [qcard,← gcard,← burn,← (liftCoordinates H).sum_comp,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro σ _
  apply sum_congr rfl
  intro f _
  exact (Fintype.card_congr (equiv (σ,f))).trans (Fintype.card_coe _)

def checkBits (H : Finset (Finset V)) :=
  (univ : Finset (V → Bool)).filter fun f => Check H (bitValue ∘ f)

theorem card_checkBits : (checkBits H).card=Nat.card (Checks H) := by
  classical
  let F (f : checkBits H) : Checks H := ⟨bitValue ∘ f.val,(mem_filter.mp f.prop).2⟩
  have bij : Bijective F := by
    constructor
    · intro f g he
      exact Subtype.ext (funext fun x => (show Injective bitValue by decide) (congrFun (congrArg Subtype.val he) x))
    · intro u
      have eq : bitValue ∘ (flipBit ∘ u.val)=u.val := funext fun x => flipBit_decode _
      exact ⟨⟨flipBit ∘ u.val,mem_filter.mpr ⟨mem_univ _,eq.symm ▸ u.prop⟩⟩,Subtype.ext eq⟩
  exact (Nat.card_eq_finsetCard _).symm.trans (Nat.card_congr (Equiv.ofBijective F bij))

theorem identity_switch_mass (hH : H.IsBlockDesign 3 4) :
    (∑ f : V → Bool, (fixedSwitches (1 : automorphisms H) f).card)=Nat.card (Checks H)*2^H.card := by
  have row (f : V → Bool) : fixedSwitches (1 : automorphisms H) f=
      if f∈checkBits H then univ else ∅ := by
    ext s
    rw [mem_fixedSwitches hH]
    change (fibrePerm (Equiv.refl _) f).finsetCongr.finsetCongr _=_ ↔ _
    rw [vertical_iff_check]
    by_cases c : Check H (bitValue ∘ f) <;> simp [checkBits,c]
  simp only [row,apply_ite Finset.card,card_empty,card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_coe]
  rw [← sum_filter]
  simp [card_checkBits]

/-- With q forced binary equalities for each moving base automorphism, the
normalized count differs from the full contribution of the vertical checks by at most |Aut(H)|2^v 2^(b-q). -/
theorem switch_mass_bounds [Nonempty V] (hH : H.IsBlockDesign 3 4) (sep : Separates H) (q : ℕ)
    (motion : ∀ (σ : Perm V) (hp : σ.finsetCongr.finsetCongr H=H), σ≠Equiv.refl V →
      2*q≤(blockPerm σ hp).support.card) :
    let N := Nat.card (SwitchClasses hH)
    let g := Nat.card (automorphisms H)*2^Fintype.card V
    let m := Nat.card (Checks H)*2^H.card
    m≤N*g ∧ N*g≤m+g*2^(H.card-q) := by
  classical
  dsimp only
  rw [switch_mass_formula hH sep,← identity_switch_mass hH]
  let A := (univ : Finset (automorphisms H)).erase 1
  let row (σ : automorphisms H) := ∑ f : V → Bool,(fixedSwitches σ f).card
  have split : (∑ σ, row σ)=(∑ σ∈A,row σ)+row 1 := (sum_erase_add _ _ (mem_univ _)).symm
  change row 1≤(∑ σ,row σ) ∧ (∑ σ,row σ)≤row 1+_
  rw [split]
  refine ⟨by omega,?_⟩
  have localCap (σ : automorphisms H) (hs : σ∈A) (f : V → Bool) :
      (fixedSwitches σ f).card≤2^(H.card-q) := by
    apply (solutions_cycles ..).trans
    apply Nat.pow_le_pow_right (by decide)
    have ne : σ.val≠Equiv.refl V := fun he => (mem_erase.mp hs).1 (Subtype.ext he)
    have mot := motion σ.val σ.prop ne
    have cap := cycle_budget (blockPerm σ.val σ.prop)
    rw [Fintype.card_coe] at cap
    omega
  have rowCap (σ : automorphisms H) (h : σ∈A) : row σ≤2^Fintype.card V*2^(H.card-q) := by
    simpa [row] using sum_le_sum (fun f (_ : f∈univ) => localCap σ h f)
  have total := sum_le_sum rowCap
  simp only [sum_const,nsmul_eq_mul] at total
  have size : A.card≤Nat.card (automorphisms H) := (card_le_univ A).trans_eq Nat.card_eq_fintype_card.symm
  have cap := total.trans (Nat.mul_le_mul_right _ size)
  rw [← mul_assoc] at cap
  omega

#print axioms fixedSwitches
#print axioms mem_fixedSwitches
#print axioms switch_mass_formula
#print axioms checkBits
#print axioms card_checkBits
#print axioms identity_switch_mass
#print axioms switch_mass_bounds
end
end Erdos722.QuadSwitch
