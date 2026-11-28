import Erdos478WindowPairIncidence
import Erdos478ReflectedParityValues
import Erdos478ColouredReturnWidths

/-! # Wilson reflection doubles the roots used by selected even gaps -/

namespace Erdos478.ReturnConcentration
open Finset WindowAverage
open scoped Classical
noncomputable section

def value (p i : ℕ) : ZMod p := i.factorial

/-- Selected factorial values avoid both products allowed by Wilson reflection. -/
def separated (p : ℕ) (A : Finset ℕ) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, value p i * value p j ≠ 1 ∧ value p i * value p j ≠ -1

def startsIn (p k : ℕ) (A : Finset ℕ) :=
  (equalStarts p k 0 k).filter fun i => i ∈ A ∧ i+k ∈ A

private theorem valid {p k i : ℕ} {A : Finset ℕ} (h : i ∈ startsIn p k A) :
    1 ≤ i ∧ i+k < p ∧ i ∈ A ∧ i+k ∈ A ∧ value p i = value p (i+k) := by
  obtain ⟨hh,hi,hj⟩ := mem_filter.mp h
  obtain ⟨hv,eq⟩ := mem_filter.mp hh
  obtain ⟨lo,up⟩ := mem_starts.mp hv
  exact ⟨lo,up,hi,hj,(ZMod.natCast_eq_natCast_iff' ..).mpr (by simpa using eq)⟩

theorem startsIn_card_le {p k : ℕ} (hp : p.Prime) (hk : 0<k) (A : Finset ℕ) :
    (startsIn p k A).card ≤ k :=
  (card_le_card (filter_subset ..)).trans (by simpa using equalStarts_card_le hp hk (le_refl k))

/-- Even gap lengths preserve the sign in the two Wilson products. Both
reflected endpoints have positive indices because a separated set excludes −1. -/
theorem twice_startsIn_card_le {p k : ℕ} (hp : p.Prime) (hk : 0<k) (even : Even k)
    {A : Finset ℕ} (hs : separated p A) : 2*(startsIn p k A).card ≤ k := by
  let : Fact p.Prime := ⟨hp⟩
  let B := startsIn p k A
  let f (i : ℕ) := p-1-(i+k)
  have top : p-1 ∉ A := by
    intro h
    have ne := (hs _ h _ h).1
    simp [value,ZMod.wilsons_lemma] at ne
  have mapped {i} (hi : i ∈ B) : f i ∈ equalStarts p k 0 k := by
    obtain ⟨lo,up,_,hj,eq⟩ := valid hi
    have strict : i+k < p-1 := by
      have ne : i+k ≠ p-1 := fun e => top (e ▸ hj)
      omega
    have flip : f i + k = p-1-i := by dsimp [f]; omega
    have r := ParityProducts.reflected_factorials (p:=p) i (by omega)
    have s := ParityProducts.reflected_factorials (p:=p) (i+k) up
    change (i.factorial : ZMod p) = ((i+k).factorial : ZMod p) at eq
    have nz : (i.factorial : ZMod p) ≠ 0 := by
      rw [Ne,ZMod.natCast_eq_zero_iff,hp.dvd_factorial]; omega
    have poweq : (-1:ZMod p)^(i+k+1)=(-1:ZMod p)^(i+1) := by
      rw [show i+k+1=i+1+k by omega,pow_add,even.neg_one_pow,mul_one]
    rw [← eq,poweq] at s
    have same := mul_left_cancel₀ nz (s.trans r.symm)
    apply mem_filter.mpr
    refine ⟨mem_starts.mpr ⟨by dsimp [f]; omega,by omega⟩,?_⟩
    rw [Nat.add_zero,flip]
    exact (ZMod.natCast_eq_natCast_iff' ..).mp same
  have inj : Set.InjOn f B := by
    intro i hi j hj ee
    have vi := (valid hi).2.1
    have vj := (valid hj).2.1
    dsimp [f] at ee
    omega
  have dis : Disjoint B (B.image f) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j,hB,rfl⟩ := mem_image.mp hj
    have vi := valid hi
    have vj := valid hB
    have both := hs (j+k) vj.2.2.2.1 (f j) vi.2.2.1
    have r := ParityProducts.reflected_factorials (p:=p) (j+k) vj.2.1
    change value p (j+k)*value p (f j)=_ at r
    rcases Nat.even_or_odd (j+k+1) with he | ho
    · exact both.1 (r.trans he.neg_one_pow)
    · exact both.2 (r.trans ho.neg_one_pow)
  have sub : B ∪ B.image f ⊆ equalStarts p k 0 k := by
    refine union_subset (filter_subset ..) ?_
    exact image_subset_iff.mpr fun _ h => mapped h
  have bound := (card_le_card sub).trans (equalStarts_card_le hp hk (le_refl k))
  rw [card_union_of_disjoint dis,card_image_of_injOn inj] at bound
  simpa [two_mul,B] using bound

#print axioms value
#print axioms separated
#print axioms startsIn
#print axioms startsIn_card_le
#print axioms twice_startsIn_card_le
end
end Erdos478.ReturnConcentration
