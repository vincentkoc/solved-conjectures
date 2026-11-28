import Erdos722SwitchMassFormula
import Erdos722BinaryDoubleSymmetry
import Erdos722AffineCheckModel

/-! # Effective unrestricted class count for switched binary quadruple systems -/

namespace Erdos722.QuadSwitch
open Finset Equiv
noncomputable section

/-- For a separating base on n=2^d points the normalized unrestricted class count
has main term c 2^b, where c is the check count. The additive error is at most 2^(b−⌊n³/1024⌋). -/
theorem cubic_class_estimate (d : ℕ) (hd : 7≤d) {H : Finset (Finset (Fin (2^d)))}
    (hH : H.IsBlockDesign 3 4) (sep : Separates H) :
    let n := 2^d
    let E := n^3/1024
    let g := Nat.card (automorphisms H)*2^n
    let m := Nat.card (Checks H)*2^H.card
    m≤Nat.card (SwitchClasses hH)*g ∧
      (Nat.card (SwitchClasses hH)*g-m)*2^E≤2^H.card := by
  classical
  let n := 2^d
  let E := n^3/1024
  let g := Nat.card (automorphisms H)*2^n
  let m := Nat.card (Checks H)*2^H.card
  have ⟨budget,enough,expCap⟩ := binary_motion_budget d hd hH
  change 192*E≤n*(n-2)*(n-4) at budget
  change 2*E≤H.card at enough
  change d*n+n+1≤E at expCap
  have bounds := switch_mass_bounds hH sep (2*E) (fun σ hp ne => by
    have motion := quadruple_block_motion hH σ hp ne
    change n*(n-2)*(n-4)≤48*_ at motion
    omega)
  simp only [Fintype.card_fin] at bounds
  change m≤Nat.card (SwitchClasses hH)*g ∧ Nat.card (SwitchClasses hH)*g≤m+g*2^(H.card-2*E) at bounds
  have sub : Nat.card (automorphisms H)≤n.factorial := by
    have inj := Nat.card_le_card_of_injective (fun a : automorphisms H => a.val) Subtype.val_injective
    simpa [Nat.card_eq_fintype_card,Fintype.card_perm,n] using inj
  have factorial : n.factorial≤2^(d*n) := n.factorial_le_pow.trans_eq (pow_mul 2 d n).symm
  have group : g≤2^(d*n+n) := by
    rw [pow_add]; exact Nat.mul_le_mul_right _ (sub.trans factorial)
  have remain : Nat.card (SwitchClasses hH)*g-m≤g*2^(H.card-2*E) := by omega
  refine ⟨bounds.1,(Nat.mul_le_mul_right _ remain).trans ?_⟩
  apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ group)).trans
  simp only [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  change d*n+n+(H.card-2*E)+E≤H.card
  omega

/-- In the concrete binary family c=2^(d+1) and b=binom(2^d,3)/4.
The count identifies switches by arbitrary permutations of the doubled point set. -/
theorem binary_class_estimate (d : ℕ) (hd : 7≤d) :
    let H := binaryBase d
    let n := 2^d
    let m := 2^(d+1)*2^(blockNumber n)
    let g := Nat.card (automorphisms H.val)*2^n
    m≤Nat.card (SwitchClasses H.prop)*g ∧
      (Nat.card (SwitchClasses H.prop)*g-m)*2^(n^3/1024)≤2^(blockNumber n) := by
  have h := cubic_class_estimate d hd (binaryBase d).prop (binaryBase_separates d)
  dsimp only at h ⊢
  have bc : (binaryBase d).val.card=blockNumber (2^d) := by
    simpa [blockNumber] using base_block_count (binaryBase d).prop
  rwa [binaryBase_checks,bc] at h

#print axioms cubic_class_estimate
#print axioms binary_class_estimate
end
end Erdos722.QuadSwitch
