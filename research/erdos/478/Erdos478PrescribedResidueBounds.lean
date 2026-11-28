import Erdos478FactorialReturnConcentration

/-! # Anti-concentration on prescribed residue sets in the pinned positive factorial domain -/

namespace Erdos478.ReturnConcentration
open Finset
open scoped Classical
noncomputable section

/-- The integer residues and both endpoints use the pinned factorial convention. -/
def selected (p a b : ℕ) (S : Finset ℕ) :=
  (Icc a b).filter (fun i => i.factorial % p ∈ S)

theorem represented_card {p : ℕ} (hp : p.Prime) (A : Finset ℕ) :
    (A.image (value p)).card = (A.image fun i => i.factorial%p).card := by
  let : Fact p.Prime := ⟨hp⟩
  rw [← card_image_of_injective (A.image (value p)) (ZMod.val_injective p),image_image]
  simp only [Function.comp_def,value,ZMod.val_natCast]

private theorem represented_le {p a b : ℕ} (hp : p.Prime) (S : Finset ℕ) :
    ((selected p a b S).image (value p)).card ≤ S.card := by
  rw [represented_card hp]
  apply card_le_card
  exact image_subset_iff.mpr fun i hi => (mem_filter.mp hi).2

private theorem selected_domain {p a b : ℕ} (ha : 1≤a) (hb : b<p) (S : Finset ℕ) :
    selected p a b S ⊆ Ico 1 p := by
  intro i hi
  obtain ⟨lo,up⟩ := mem_Icc.mp (mem_filter.mp hi).1
  exact mem_Ico.mpr ⟨ha.trans lo,up.trans_lt hb⟩

theorem prescribed_set_bound {p a b : ℕ} (hp : p.Prime) (ha : 1≤a) (hb : b<p) (S : Finset ℕ) :
    8*((selected p a b S).card-S.card+1)^3 ≤ 9*(S.card*(b-a)+1)^2 := by
  let A := selected p a b S
  have hK := represented_le (p:=p) (a:=a) (b:=b) hp S
  have hW := (totalWidth_le (value p) (show A ⊆ Icc a b from filter_subset ..)).trans
    (Nat.mul_le_mul_right (b-a) hK)
  have bnd := factorial_cubic hp (selected_domain ha hb S)
  exact (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (by omega) 3)).trans
    (bnd.trans (Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left (Nat.add_le_add_right hW 1) 2)))

theorem prescribed_separated_bound {p a b : ℕ} (hp : p.Prime) (ha : 1≤a) (hb : b<p)
    (S : Finset ℕ) (hs : ∀ x ∈ S, ∀ y ∈ S,
      (x:ZMod p)*y ≠ 1 ∧ (x:ZMod p)*y ≠ -1) :
    32*((selected p a b S).card-S.card)^3 ≤ 27*(S.card*(b-a)+1)^2 := by
  let A := selected p a b S
  have sep : separated p A := by
    intro i hi j hj
    have h := hs _ (mem_filter.mp hi).2 _ (mem_filter.mp hj).2
    simpa [value,ZMod.natCast_mod] using h
  have hK := represented_le (p:=p) (a:=a) (b:=b) hp S
  have hW := (totalWidth_le (value p) (show A ⊆ Icc a b from filter_subset ..)).trans
    (Nat.mul_le_mul_right (b-a) hK)
  have bnd := separated_factorial_cubic hp (selected_domain ha hb S) sep
  exact (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (by omega) 3)).trans
    (bnd.trans (Nat.mul_le_mul_left 27 (Nat.pow_le_pow_left (Nat.add_le_add_right hW 1) 2)))

/-- A single colour qualifies for the reflection improvement unless it is a fourth root of unity. -/
theorem prescribed_residue_bound {p a b x : ℕ} (hp : p.Prime) (ha : 1≤a) (hb : b<p)
    (hx : (x:ZMod p)^4 ≠ 1) :
    32*(((Icc a b).filter (fun i => i.factorial%p=x)).card-1)^3 ≤ 27*(b-a+1)^2 := by
  have sep (y : ℕ) (hy : y ∈ ({x} : Finset ℕ)) (z : ℕ) (hz : z ∈ ({x} : Finset ℕ)) :
      (y:ZMod p)*z ≠ 1 ∧ (y:ZMod p)*z ≠ -1 := by
    have hyx := mem_singleton.mp hy
    have hzx := mem_singleton.mp hz
    subst y
    subst z
    constructor <;> intro h <;> apply hx <;>
      calc
        _ = ((x:ZMod p)*x)^2 := by ring
        _ = _ := by simp [h]
  simpa [selected] using prescribed_separated_bound hp ha hb {x} sep

/-- At most four field elements fail the singleton hypothesis. -/
theorem exceptional_residue_count (p : ℕ) [Fact p.Prime] :
    (univ.filter (fun x : ZMod p => x^4=1)).card ≤ 4 := by
  classical
  let T := Polynomial.nthRoots 4 (1 : ZMod p)
  have eq : univ.filter (fun x : ZMod p => x^4=1) = T.toFinset := by
    ext x
    simp [T,Polynomial.mem_nthRoots (by decide : 0<4)]
  rw [eq]
  exact T.toFinset_card_le.trans (Polynomial.card_nthRoots ..)

#print axioms exceptional_residue_count
#print axioms selected
#print axioms represented_card
#print axioms prescribed_set_bound
#print axioms prescribed_separated_bound
#print axioms prescribed_residue_bound
end
end Erdos478.ReturnConcentration
