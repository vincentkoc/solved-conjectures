import Mathlib

/-! Counting reduced cofactor residues inside one fixed index progression. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset

def sievePrimes (L Y : ℕ) := Y.primesLE.filter (fun p => ¬p ∣ L)
def roughProduct (L Y : ℕ) := ∏ p ∈ sievePrimes L Y, p

lemma roughProduct_pos (L Y : ℕ) : 0 < roughProduct L Y := by
  apply prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).pos

lemma coprime_roughProduct (L Y : ℕ) : L.Coprime (roughProduct L Y) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨mem,avoid⟩ := mem_filter.mp hp
  exact ((Nat.prime_of_mem_primesLE mem).coprime_iff_not_dvd.mpr avoid).symm

lemma small_prime_dvd_rough {L Y p : ℕ} (hp : p.Prime) (lo : p≤Y) :
    p ∣ L ∨ p ∣ roughProduct L Y := by
  by_cases h : p ∣ L
  · exact Or.inl h
  · exact Or.inr (Finset.dvd_prod_of_mem id (mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨lo,hp⟩,h⟩))

lemma roughProduct_primeFactors (L Y : ℕ) : (roughProduct L Y).primeFactors ⊆ Y.primesLE := by
  intro p hp
  obtain ⟨pr,dv,_⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨q,hq,pq⟩ := (pr.prime.dvd_finsetProd_iff (fun n : ℕ => n)).mp dv
  have mem := (mem_filter.mp hq).1
  obtain rfl := (Nat.prime_dvd_prime_iff_eq pr (Nat.prime_of_mem_primesLE mem)).mp pq
  exact mem

/-- Choose the cofactor in the residue h modulo L and in each unit residue modulo P. -/
def roughResidues (g h L P : ℕ) (co : L.Coprime P) : Finset ℕ :=
  ((range P).filter (fun i => P.Coprime i)).image
    (fun i => g*(Nat.chineseRemainder co h i).val)

lemma roughResidues_card {g h L P : ℕ} (gp : 0 < g) (co : L.Coprime P) :
    (roughResidues g h L P co).card = P.totient := by
  unfold roughResidues Nat.totient
  apply card_image_of_injOn
  intro i hi j hj same
  have eq : (Nat.chineseRemainder co h i).val=(Nat.chineseRemainder co h j).val :=
    Nat.eq_of_mul_eq_mul_left gp same
  have cl := (Nat.chineseRemainder co h i).property.2.symm
  rw [eq] at cl
  exact (cl.trans (Nat.chineseRemainder co h j).property.2).eq_of_lt_of_lt
    (mem_range.mp (mem_filter.mp hi).1) (mem_range.mp (mem_filter.mp hj).1)

lemma roughResidues_lt {g h L P r : ℕ} (gp : 0 < g) (lp : 0 < L) (pp : 0 < P) (co : L.Coprime P)
    (hr : r∈roughResidues g h L P co) : r < (g*L)*P := by
  obtain ⟨i,_,rfl⟩ := mem_image.mp hr
  rw [Nat.mul_assoc]
  exact Nat.mul_lt_mul_of_pos_left (Nat.chineseRemainder_lt_mul co h i lp.ne' pp.ne') gp

/-- Unfolding a selected residue gives an integer cofactor in its original class and
coprime to P, including at every later period. -/
lemma cofactor_of_rough_residue {g h L P n : ℕ} (co : L.Coprime P)
    (hit : n%((g*L)*P)∈roughResidues g h L P co) :
    ∃ q, n=g*q ∧ q ≡ h [MOD L] ∧ q.Coprime P := by
  let D := (g*L)*P
  obtain ⟨i,hi,eq⟩ := mem_image.mp hit
  let c := (Nat.chineseRemainder co h i).val
  change g*c=n%D at eq
  let j := n/D
  let q := c+(L*P)*j
  have split : n=g*q := by
    calc n = n%D+D*j := (Nat.mod_add_div ..).symm
         _ = g*q := by rw [←eq]; dsimp [D,q]; ring
  have eqL : q ≡ c [MOD L] := by
    dsimp [q,Nat.ModEq]
    rw [Nat.mul_assoc,Nat.add_mul_mod_self_left]
  have eqP : q ≡ c [MOD P] := by
    dsimp [q,Nat.ModEq]
    rw [Nat.mul_comm L P,Nat.mul_assoc,Nat.add_mul_mod_self_left]
  have ci := (Nat.chineseRemainder co h i).property
  exact ⟨q,split,eqL.trans ci.1,(eqP.trans ci.2).gcd_eq.trans (mem_filter.mp hi).2.symm⟩

#print axioms roughResidues_card
#print axioms cofactor_of_rough_residue

end Arxiv.«2211.10788».IndexDivisors
