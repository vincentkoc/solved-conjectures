import Erdos722CosetDesignIsomorphisms

/-! # Counting asymmetric Steiner quadruple systems with freely chosen coset coefficients -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

abbrev CosetParameters (d : ℕ) := CosetPattern d × CubeOffsets (d+2)

def cosetClass (d : ℕ) (hd : 6≤d) (a : CosetParameters d) := classOf (cosetDesign d hd a.1 a.2)

def cosetClasses (d : ℕ) (hd : 6≤d) := univ.image (cosetClass d hd)

/-- A fibre of the map to unrestricted isomorphism classes consists of one
translation for every independent choice of a shift at each base point. -/
theorem coset_class_fibre (d : ℕ) (hd : 6≤d) (a : CosetParameters d) :
    (univ.filter (fun x => cosetClass d hd x=cosetClass d hd a)).card=4^(2^(d+2)) := by
  let G := cosetGradient d hd a.1
  let g (t : Cube (d+2) → Fibre) : CosetParameters d := (a.1,a.2+G t)
  have inj : Function.Injective g := by
    intro t v eq
    exact coset_gradient_injective d hd a.1 (add_left_cancel (congrArg Prod.snd eq))
  have setEq : univ.filter (fun x => cosetClass d hd x=cosetClass d hd a)=univ.image g := by
    ext x
    simp only [mem_filter,mem_univ,true_and,mem_image]
    constructor
    · intro h
      obtain ⟨pat,t,off⟩ := (coset_class_iff d hd a.1 x.1 a.2 x.2).mp h.symm
      exact ⟨t,Prod.ext pat off.symm⟩
    · rintro ⟨t,rfl⟩
      exact ((coset_class_iff d hd ..).mpr ⟨rfl,t,rfl⟩).symm
  rw [setEq,card_image_of_injective _ inj,card_univ]
  simp [Fibre,Cube]

/-- All coefficients on three of the four points of each coset block are
independent. The remaining global identifications are exactly fibre translations. -/
theorem coset_class_count (d : ℕ) (hd : 6≤d) :
    (cosetClasses d hd).card=216^(blockNumber (2^d))*4^(blockNumber (2^(d+2))-2^(d+2)) := by
  have count := card_eq_sum_card_fiberwise (s:=(univ : Finset (CosetParameters d))) (t:=cosetClasses d hd)
    (f:=cosetClass d hd) (fun x hx => mem_image_of_mem _ hx)
  have each (y) (hy : y∈cosetClasses d hd) :
      (univ.filter (fun x => cosetClass d hd x=y)).card=4^(2^(d+2)) := by
    obtain ⟨a,_,rfl⟩ := mem_image.mp hy
    exact coset_class_fibre d hd a
  rw [sum_congr rfl each,sum_const,smul_eq_mul,card_univ,Fintype.card_prod,coset_pattern_card,
    ← Nat.card_eq_fintype_card (α:=CubeOffsets (d+2)),cube_offsets_card] at count
  have c : CosetPattern d := fun _ _ => 1
  have le := Nat.card_le_card_of_injective _ (coset_gradient_injective d hd c)
  rw [show Nat.card (Cube (d+2) → Fibre)=4^(2^(d+2)) by simp [Nat.card_eq_fintype_card,Fibre,Cube],cube_offsets_card] at le
  have expo := (Nat.pow_le_pow_iff_right (by decide : 1<4)).mp le
  apply Nat.eq_of_mul_eq_mul_right (by positivity : 0<4^(2^(d+2)))
  rwa [mul_assoc,← pow_add,Nat.sub_add_cancel expo,eq_comm]

theorem every_coset_class_asymmetric (d : ℕ) (hd : 6≤d) :
    ∀ y∈cosetClasses d hd, ∃ D : Finset (Finset (Fin (4*2^(d+2)))),
      classOf D=y ∧ D.IsBlockDesign 3 4 ∧ (binaryIncidence D).rank+(d+3)=4*2^(d+2) ∧
      ∀ e : automorphisms D, e=1 := by
  intro y hy
  obtain ⟨a,_,rfl⟩ := mem_image.mp hy
  exact ⟨cosetDesign d hd a.1 a.2,rfl,(coset_design_rank d hd ..).1,(coset_design_rank d hd ..).2,
    coset_asymmetric d hd a.1 a.2⟩

theorem asymmetric_1024_class_count :
    (cosetClasses 6 (by decide)).card=216^10416*4^690624 := by
  rw [coset_class_count]
  have small : blockNumber (2^6)=10416 := by rw [blockNumber_formula]; decide +kernel
  have large : blockNumber (2^(6+2))-2^(6+2)=690624 := by rw [blockNumber_formula]; decide +kernel
  rw [small,large]

#print axioms asymmetric_1024_class_count
#print axioms CosetParameters
#print axioms cosetClass
#print axioms cosetClasses
#print axioms coset_class_fibre
#print axioms coset_class_count
#print axioms every_coset_class_asymmetric
end
end Erdos722.FourPoint
