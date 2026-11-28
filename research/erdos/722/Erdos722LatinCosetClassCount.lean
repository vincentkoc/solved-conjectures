import Erdos722LatinTranslationClasses

/-! # Counting asymmetric Steiner quadruple systems with all order-four Latin fillings -/

namespace Erdos722.LatinFillings
open Finset QuadCompletion FourPoint QuadSwitch
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

def latinClass (d : ℕ) (hd : 6≤d) (a : Parameters d) := classOf (latinDesign d hd a)
def latinClasses (d : ℕ) (hd : 6≤d) := univ.image (latinClass d hd)

theorem parameter_count (d : ℕ) : Fintype.card (Parameters d)=
    13824^blockNumber (2^d)*4^blockNumber (2^(d+2)) := by
  have blocks : ((cubeRule (d+2)).blocks).card=blockNumber (2^(d+2)) := by
    rw [base_block_count (cubeRule (d+2)).isBlockDesign]
    simp [blockNumber,Cube]
  have less := card_le_card (region_sub d)
  rw [region_card,blocks] at less
  have number : Fintype.card Quasigroup=55296 := by rw [← Nat.card_eq_fintype_card,latin_cube_count]
  have fc : Fintype.card Fibre=4 := by simp [Fibre]
  rw [show Fintype.card (Parameters d)=Fintype.card (Fillings d)*Fintype.card (OutsideOffsets d) from Fintype.card_prod ..]
  simp only [Fillings,OutsideOffsets,Fintype.card_fun,Fintype.card_coe,number,fc,region_card,outside_card]
  rw [show 55296=13824*4 by decide,mul_pow,mul_assoc,← pow_add]
  rw [Nat.add_sub_of_le less]

theorem class_fibre_count (d : ℕ) (hd : 6≤d) (a : Parameters d) :
    (univ.filter (fun b => latinClass d hd b=latinClass d hd a)).card=4^(2^(d+2)) := by
  have eq : univ.filter (fun b => latinClass d hd b=latinClass d hd a)=univ.image (shiftParameters d hd a) := by
    ext b
    simp only [mem_filter,mem_univ,true_and,mem_image]
    change classOf (latinDesign d hd b)=classOf (latinDesign d hd a) ↔ _
    rw [eq_comm,latin_class_iff]
  rw [eq,card_image_of_injective _ (shift_injective d hd a),card_univ]
  simp [Base,Fibre,Cube]

/-- All local ternary quasigroups are allowed. The unrestricted full point
isomorphism classes have a common fibre of 4^n labelled parameters. -/
theorem latin_class_count (d : ℕ) (hd : 6≤d) :
    (latinClasses d hd).card =
      13824^blockNumber (2^d)*4^(blockNumber (2^(d+2))-2^(d+2)) := by
  have sum := card_eq_sum_card_fiberwise (s:=(univ : Finset (Parameters d))) (t:=latinClasses d hd)
    (f:=latinClass d hd) (fun a _ => mem_image_of_mem _ (mem_univ a))
  have each (y) (hy : y∈latinClasses d hd) :
      (univ.filter (fun x => latinClass d hd x=y)).card=4^(2^(d+2)) := by
    obtain ⟨a,_,rfl⟩ := mem_image.mp hy
    exact class_fibre_count d hd a
  rw [sum_congr rfl each,sum_const,smul_eq_mul,card_univ,parameter_count] at sum
  have le := Nat.card_le_card_of_injective _ (cycle_gradient_injective (d+2) (by omega))
  rw [show Nat.card (Cube (d+2) → Fibre)=4^(2^(d+2)) by simp [Nat.card_eq_fintype_card,Fibre,Cube],
    cube_offsets_card] at le
  have expo := (Nat.pow_le_pow_iff_right (by decide : 1<4)).mp le
  apply Nat.eq_of_mul_eq_mul_right (by positivity : 0<4^(2^(d+2)))
  rwa [mul_assoc,← pow_add,Nat.sub_add_cancel expo,eq_comm]

theorem members (d : ℕ) (hd : 6≤d) (y) (hy : y∈latinClasses d hd) :
    ∃ D : Finset (Finset (Fin (4*2^(d+2)))), classOf D=y ∧ D.IsBlockDesign 3 4 ∧
      (binaryIncidence D).rank+(d+3)=4*2^(d+2) ∧ ∀ e : automorphisms D, e=1 := by
  obtain ⟨a,_,rfl⟩ := mem_image.mp hy
  exact ⟨latinDesign d hd a,rfl,(latin_design_rank d hd a).1,(latin_design_rank d hd a).2,
    latin_asymmetric d hd a⟩

theorem latin_1024_classes :
    (latinClasses 6 (by decide)).card=13824^10416*4^690624 := by
  rw [latin_class_count]
  have a : blockNumber (2^6)=10416 := by rw [blockNumber_formula]; decide +kernel
  have b : blockNumber (2^(6+2))-2^(6+2)=690624 := by rw [blockNumber_formula]; decide +kernel
  rw [a,b]

#print axioms latinClass
#print axioms latinClasses
#print axioms parameter_count
#print axioms class_fibre_count
#print axioms latin_class_count
#print axioms members
#print axioms latin_1024_classes
end
end Erdos722.LatinFillings
