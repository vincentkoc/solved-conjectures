import Erdos722VerticalAutomorphismGroup
import Erdos722CubicSwitchBound

/-! # Canonically labelled quadruple systems with prescribed full automorphism group -/

namespace Erdos722.QuadSwitch
open Finset Function
noncomputable section

def binaryDouble (d : ℕ) (s : (binaryBase d).val → Bool) : Finset (Finset (Fin (2^(d+1)))) :=
  (binaryStepLabels d).finsetCongr.finsetCongr (doubling (binaryBase d).prop s)

theorem binaryDouble_design (d : ℕ) (s : (binaryBase d).val → Bool) : (binaryDouble d s).IsBlockDesign 3 4 :=
  relabel_quadruples _ (doubling_design _ _)

theorem binaryDouble_injective (d : ℕ) : Injective (binaryDouble d) :=
  fun _ _ he => doubling_injective _ ((binaryStepLabels d).finsetCongr.finsetCongr.injective he)

/-- On the actual finite host labels the full automorphism group is isomorphic
to the additive binary check group of the base for each nonexceptional switch. -/
def binaryDouble_group (d : ℕ) (s : (binaryBase d).val → Bool) (hs : s∉exceptional (binaryBase d).prop) :
    Multiplicative (checkGroup (binaryBase d).val) ≃* automorphisms (binaryDouble d s) :=
  (verticalGroupEquiv _ s hs).trans (automorphismRelabel _ _)

theorem binaryDouble_order (d : ℕ) (s : (binaryBase d).val → Bool) (hs : s∉exceptional (binaryBase d).prop) :
    Nat.card (automorphisms (binaryDouble d s))=2^(d+1) :=
  (Nat.card_congr (binaryDouble_group d s hs).toEquiv).symm.trans (binaryBase_checks d)

/-- Distinct ordinary labelled systems on 2n points, n=2^d, whose full group is
elementary abelian of order 2n. The fraction refers to the fixed base's complete switch cube. -/
theorem abundant_binary_symmetry (d : ℕ) (hd : 7≤d) :
    ∃ G : Finset (Finset (Finset (Fin (2^(d+1))))),
      (∀ D∈G, D.IsBlockDesign 3 4 ∧ Nat.card (automorphisms D)=2^(d+1) ∧
        Nonempty (Multiplicative (checkGroup (binaryBase d).val) ≃* automorphisms D)) ∧
      2^(blockNumber (2^d))*(2^((2^d)^3/1024)-1) ≤ G.card*2^((2^d)^3/1024) := by
  classical
  let H := binaryBase d
  let E := exceptional H.prop
  let G := Eᶜ.image (binaryDouble d)
  refine ⟨G,?_,?_⟩
  · intro D hD
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hD
    have good := mem_compl.mp hs
    exact ⟨binaryDouble_design d s,binaryDouble_order d s good,⟨binaryDouble_group d s good⟩⟩
  · have cardG : G.card=2^H.val.card-E.card := by
      rw [show G=Eᶜ.image (binaryDouble d) from rfl,card_image_of_injective _ (binaryDouble_injective d),card_compl]
      simp [H]
    have bound := cubic_exceptional_bound d hd H.prop (binaryBase_separates d)
    let C := 2^((2^d)^3/1024)
    change E.card*C≤2^H.val.card at bound
    have pos : 0<C := by dsimp [C]; positivity
    have size : E.card≤2^H.val.card := by simpa using card_le_univ E
    have bc : H.val.card=blockNumber (2^d) := by simpa [blockNumber] using base_block_count H.prop
    rw [← bc,cardG]
    change 2^H.val.card*(C-1)≤(2^H.val.card-E.card)*C
    rw [Nat.mul_sub,Nat.sub_mul,Nat.mul_one]
    omega

#print axioms binaryDouble
#print axioms binaryDouble_design
#print axioms binaryDouble_injective
#print axioms binaryDouble_group
#print axioms binaryDouble_order
#print axioms abundant_binary_symmetry
end
end Erdos722.QuadSwitch
