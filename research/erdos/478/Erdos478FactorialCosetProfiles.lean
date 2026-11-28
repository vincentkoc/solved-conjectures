import Erdos478CyclotomicProfileEnergy
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-! # Two successive factorial quotients as a cyclotomic profile -/

namespace Erdos478.CyclotomicProfiles
open Finset
open scoped Classical
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def factorialLabel (H : Subgroup (ZMod p)ˣ) (i : ℕ) := label H (i.factorial : ZMod p)

/-- The quotient label at the next factorial differs by the label of the next integer. -/
theorem next_label (H : Subgroup (ZMod p)ˣ) {i : ℕ} (hi : i+1<p) :
    factorialLabel H (i+1)/factorialLabel H i=label H ((i+1:ℕ):ZMod p) := by
  have fi : (i.factorial : ZMod p)≠0 := by
    rw [Ne,ZMod.natCast_eq_zero_iff,hp.out.dvd_factorial]; omega
  have fs : ((i+1).factorial : ZMod p)≠0 := by
    rw [Ne,ZMod.natCast_eq_zero_iff,hp.out.dvd_factorial]; omega
  have nxt : ((i+1:ℕ):ZMod p)≠0 := by
    rw [Ne,ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) hi
  simp only [factorialLabel,label,dif_neg fi,dif_neg fs,dif_neg nxt]
  let u := Units.mk0 (i.factorial : ZMod p) fi
  let v := Units.mk0 ((i+1:ℕ):ZMod p) nxt
  have fact : Units.mk0 ((i+1).factorial : ZMod p) fs=v*u := by
    apply Units.ext
    simp only [Units.val_mk0,Units.val_mul,v,u,Nat.factorial_succ,Nat.cast_mul]
  rw [fact]
  change QuotientGroup.mk' H (v*u)/QuotientGroup.mk' H u=QuotientGroup.mk' H v
  rw [map_mul,mul_div_cancel_right]

/-- The relative coset labels appearing in ordered triples of a set of occupied cosets. -/
def relativeTriples {G : Type*} [CommGroup G] [DecidableEq G] (S : Finset G) :=
  (S ×ˢ (S ×ˢ S)).image fun xyz => (xyz.2.1/xyz.1,xyz.2.2/xyz.2.1)

theorem relative_card {G : Type*} [CommGroup G] [DecidableEq G] (S : Finset G) : (relativeTriples S).card≤S.card^3 := by
  exact card_image_le.trans_eq (by simp only [card_product]; ring)

theorem factorial_profiles (H : Subgroup (ZMod p)ˣ) (A : Finset ℕ) (S : Finset ((ZMod p)ˣ ⧸ H))
    (valid : ∀ i∈A,i+2<p)
    (hit : ∀ i∈A,factorialLabel H i∈S ∧ factorialLabel H (i+1)∈S ∧ factorialLabel H (i+2)∈S) :
    A.card^2 ≤ (relativeTriples S).card*(A.card+(Nat.card H-1)*(Nat.card H-2)) := by
  let pos (i : ℕ) : ZMod p := (i+1 : ℕ)
  have succ (i : ℕ) : pos i+1=((i+2:ℕ):ZMod p) := (Nat.cast_succ (i+1)).symm
  let V := A.image pos
  have regular (i) (h : i∈A) : Regular (pos i) := by
    have lt := valid i h
    have nz (j : ℕ) (jp : 0<j) (jl : j<p) : (j:ZMod p)≠0 := by
      rw [Ne,ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt jp jl
    refine ⟨nz (i+1) (by omega) (by omega),?_⟩
    rw [succ]
    exact nz (i+2) (by omega) lt
  have reg (x) (hx : x∈V) : Regular x := by
    obtain ⟨i,h,rfl⟩ := mem_image.mp hx
    exact regular i h
  have card : V.card=A.card := by
    apply card_image_of_injOn
    intro i hi j hj h
    have eq := (ZMod.natCast_eq_natCast_iff' ..).mp (show ((i+1:ℕ):ZMod p)=((j+1:ℕ):ZMod p) from h)
    have il := valid i hi
    have jl := valid j hj
    rw [Nat.mod_eq_of_lt (by omega : i+1<p),Nat.mod_eq_of_lt (by omega : j+1<p)] at eq
    omega
  have sub : V.image (labelPair H) ⊆ relativeTriples S := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨i,h,rfl⟩ := mem_image.mp hx
    obtain ⟨h0,h1,h2⟩ := hit i h
    have lt := valid i h
    refine mem_image.mpr ⟨(factorialLabel H i,factorialLabel H (i+1),factorialLabel H (i+2)),
      mem_product.mpr ⟨h0,mem_product.mpr ⟨h1,h2⟩⟩,?_⟩
    apply Prod.ext
    · exact next_label H (by omega)
    · change factorialLabel H (i+2)/factorialLabel H (i+1)=label H (pos i+1)
      rw [succ]
      exact next_label H (i:=i+1) lt
  have cs := profile_occupation H V reg
  rw [card] at cs
  exact cs.trans (Nat.mul_le_mul_right _ (card_le_card sub))

#print axioms factorialLabel
#print axioms next_label
#print axioms relativeTriples
#print axioms relative_card
#print axioms factorial_profiles
end
end Erdos478.CyclotomicProfiles
