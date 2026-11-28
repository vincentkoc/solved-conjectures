import Erdos722MarkedPointGroup

/-! # Evaluating affine translations at the marks and counting the fixed values -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch Equiv
noncomputable section

theorem basis_mark_count (d : ℕ) : (affineBasisMarks d).card=d+1 := by
  unfold affineBasisMarks
  rw [card_insert_of_notMem,card_image_of_injective _ (Pi.basisFun (ZMod 2) (Fin d)).injective,
    card_univ,Fintype.card_fin]
  rintro h
  obtain ⟨i,_,eq⟩ := mem_image.mp h
  exact (Pi.basisFun (ZMod 2) (Fin d)).ne_zero i eq

attribute [local instance] cubeOrder cubeDec

private def basisValue (d : ℕ) (t : shifts (cubeRule d)) (q : affineBasisMarks d) : Fibre := t.val q

private theorem basis_bijective (d : ℕ) : Function.Bijective (basisValue d) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro t v eq
    have law : Offset (cubeRule d) (t.val-v.val) := (t-v).prop
    apply Subtype.ext
    apply sub_eq_zero.mp
    exact offset_zero_on_basis law fun i hi => sub_eq_zero.mpr (congrFun eq ⟨i,hi⟩)
  · rw [← Nat.card_eq_fintype_card,shifts_card,cube_checks_card,Fintype.card_fun,Fintype.card_coe,basis_mark_count]
    change (2^(d+1))^2=4^(d+1)
    rw [← Nat.pow_mul,Nat.mul_comm, Nat.pow_mul]

def fixedDimension (s : Colour) : ℕ := if s=1 then 2 else if s*s=1 then 1 else 0

theorem fibre_fixed_count : ∀ s : Colour, Fintype.card {x : Fibre // move s x=x}=2^fixedDimension s := by
  decide +kernel

/-- Independent fixed-vector choices at the affine basis determine exactly one translation. -/
def markedKernelValues (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) :
    (markedGradient d hd c).ker ≃ ((q : affineBasisMarks d) → {x : Fibre // move (c q) x=x}) := by
  let existsPoint := common_unmarked_point d hd (Equiv.refl _)
  have out := existsPoint.choose_spec.1
  let law (t : Cube d → Fibre) := marked_kernel_iff (cubePrivateBlocks_injective d hd)
    (cubePrivateBlocks_incident d hd) c out t
  let f (t : (markedGradient d hd c).ker) (q : affineBasisMarks d) :
      {x : Fibre // move (c q) x=x} := ⟨t.val q,((law t.val).mp t.prop).2 q⟩
  apply Equiv.ofBijective f
  constructor
  · intro t v eq
    have same := (basis_bijective d).injective (a₁:=⟨t.val,((law _).mp t.prop).1⟩)
      (a₂:=⟨v.val,((law _).mp v.prop).1⟩) (funext fun q => congrArg Subtype.val (congrFun eq q))
    exact Subtype.ext (congrArg (fun v : shifts (cubeRule d) => v.val) same)
  · intro x
    obtain ⟨t,ht⟩ := (basis_bijective d).surjective fun q => (x q).val
    have val (q : affineBasisMarks d) : t.val q=(x q).val := congrFun ht q
    have ker : markedGradient d hd c t.val=0 := (law _).mpr ⟨t.prop,fun q => by rw [val]; exact (x q).prop⟩
    exact ⟨⟨t.val,ker⟩,funext fun q => Subtype.ext (val q)⟩

def groupDimension (d : ℕ) (c : affineBasisMarks d → Colour) := ∑ q, fixedDimension (c q)

theorem marked_kernel_card (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) :
    Nat.card (markedGradient d hd c).ker=2^groupDimension d c := by
  rw [Nat.card_congr (markedKernelValues d hd c),Nat.card_pi]
  simp only [Nat.card_eq_fintype_card,fibre_fixed_count]
  exact prod_pow_eq_pow_sum ..

theorem marked_group_card (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) (u : CubeOffsets d) :
    Nat.card (automorphisms (markedDesign d hd c u))=2^groupDimension d c := by
  rw [← Nat.card_congr (markedPointGroup d hd c u).toEquiv]
  exact marked_kernel_card d hd c

#print axioms basis_mark_count
#print axioms fixedDimension
#print axioms fibre_fixed_count
#print axioms markedKernelValues
#print axioms groupDimension
#print axioms marked_kernel_card
#print axioms marked_group_card
end
end Erdos722.FourPoint
