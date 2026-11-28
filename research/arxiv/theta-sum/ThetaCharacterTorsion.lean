import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Counting characters of prescribed bounded exponent at odd moduli. -/
namespace Arxiv.«2501.03234».ThetaCharacterTorsion
open Finset
noncomputable section

def roots (G : Type*) [Group G] (k : ℕ) := Nat.card {x : G // x^k=1}

private lemma transport {G H : Type*} [Group G] [Group H] (e : G ≃* H) (k : ℕ) :
    roots G k=roots H k := by
  apply Nat.card_congr
  exact e.toEquiv.subtypeEquiv (fun x => by change x^k=1 ↔ e x^k=1; rw [←map_pow,←e.map_one,e.injective.eq_iff])

private lemma product (G H : Type*) [Group G] [Group H] (k : ℕ) :
    roots (G×H) k=roots G k*roots H k := by
  let e : {x : G×H // x^k=1} ≃ {x:G // x^k=1}×{x:H // x^k=1} :=
    { toFun := fun x => (⟨x.1.1,congrArg Prod.fst x.2⟩,⟨x.1.2,congrArg Prod.snd x.2⟩)
      invFun := fun x => ⟨(x.1.1,x.2.1),Prod.ext x.1.2 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_prod _ _)

private theorem cyclic (G : Type*) [Group G] [Fintype G] [IsCyclic G] {k : ℕ} (hk : 0< k) :
    roots G k≤ k := by
  classical
  simpa [roots,Nat.card_eq_fintype_card,Fintype.card_subtype] using (IsCyclic.card_pow_eq_one_le (α:=G) hk)

private theorem units_bound {q k : ℕ} (hk : 0< k) (ho : Odd q) :
    roots (ZMod q)ˣ k≤ k^q.primeFactors.card := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => exact False.elim (Nat.not_odd_zero ho)
  | one =>
    have hcard : roots (ZMod 1)ˣ k≤ 1 := by
      classical
      exact (Nat.card_of_subsingleton (⟨1,one_pow k⟩ : {x : (ZMod 1)ˣ // x^k=1})).le
    simpa using hcard
  | prime_pow p n hp hn =>
    let : NeZero (p^n) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hpo := ho.of_dvd_nat (dvd_pow_self p hn.ne')
    let : IsCyclic (ZMod (p^n))ˣ := ZMod.isCyclic_units_of_prime_pow p hp (hpo.ne_two_of_dvd_nat dvd_rfl) n
    simpa [Nat.primeFactors_pow _ hn.ne',hp.primeFactors] using cyclic (ZMod (p^n))ˣ hk
  | coprime a b ha hb hab ia ib =>
    have h := (transport ((Units.mapEquiv (ZMod.chineseRemainder hab).toMulEquiv).trans .prodUnits) k).trans (product _ _ k)
    rw [h,Nat.primeFactors_mul (by omega) (by omega),card_union_of_disjoint hab.disjoint_primeFactors,pow_add]
    exact Nat.mul_le_mul (ia (ho.of_dvd_nat (dvd_mul_right ..))) (ib (ho.of_dvd_nat (dvd_mul_left ..)))

theorem count {q k : ℕ} [NeZero q] (hk : 0< k) (ho : Odd q) :
    roots (DirichletCharacter ℂ q) k≤ k^q.primeFactors.card :=
  (transport (MulChar.mulEquiv_units (ZMod q) ℂ).some k).le.trans (units_bound hk ho)

#print axioms count
end
end Arxiv.«2501.03234».ThetaCharacterTorsion
