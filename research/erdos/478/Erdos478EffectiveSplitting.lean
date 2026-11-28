import Erdos478BoundedSchurPrime
import Erdos478ResolventHeight
import Erdos478ResolventFrobenius

/-!
# An elementary upper bound for a separable splitting prime

Exclude the two nonzero resultants for the original polynomial and its
permutation resolvent. A prime divisor of one integer value of the resolvent
then gives complete splitting of the original polynomial.
-/

namespace Erdos478.EffectiveResolvent
open Finset Polynomial
open scoped Polynomial

def tagBound (n U : ℕ) := n*U*(n*n.factorial^2+1)^n
def exceptionalBound (n U : ℕ) := (2*U)^(n^2)*(2*tagBound n U)^(n.factorial^2)
def splitBound (n U : ℕ) := schurBound n.factorial (tagBound n U) (exceptionalBound n U)

private theorem separable_at_good_prime (f : ℤ[X]) (hd : f.natDegree ≠ 0) (p : ℕ) [Fact p.Prime]
    (he : ¬p ∣ (bad f).natAbs) : (f.map (Int.castRingHom (ZMod p))).Separable := by
  let φ := Int.castRingHom (ZMod p)
  have hφ : φ (bad f) ≠ 0 := fun h => he (Int.ofNat_dvd_left.mp ((CharP.intCast_eq_zero_iff _ p _).mp h))
  obtain ⟨u,v,_,_,huv⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative le_rfl le_rfl (Or.inl hd)
  have hh := congrArg (Polynomial.map φ) huv
  change (f * u + f.derivative * v).map φ = (C (bad f)).map φ at hh
  simp only [Polynomial.map_add,Polynomial.map_mul,map_C,← derivative_map] at hh
  refine ⟨C (φ (bad f))⁻¹ * u.map φ,C (φ (bad f))⁻¹ * v.map φ,?_⟩
  calc
    _ = C (φ (bad f))⁻¹ * (f.map φ * u.map φ + (f.map φ).derivative * v.map φ) := by ring
    _ = 1 := by rw [hh,← C_mul,inv_mul_cancel₀ hφ,C_1]

/-- A monic separable integer polynomial of positive degree, all of whose
complex roots have norm at most `U`, has a separable splitting prime at
most `splitBound n U`. -/
theorem bounded_splitting_prime (f : ℤ[X]) (hm : f.Monic) {n U : ℕ} (hn : f.natDegree=n)
    (hn₀ : 0<n) (hU : 0<U) (hs : (f.map (Int.castRingHom ℂ)).Separable)
    (hrad : ∀ z : ℂ, (f.map (Int.castRingHom ℂ)).IsRoot z → ‖z‖ ≤ U) :
    ∃ p ≤ splitBound n U, p.Prime ∧ (f.map (Int.castRingHom (ZMod p))).Splits ∧
      (f.map (Int.castRingHom (ZMod p))).Separable := by
  classical
  obtain ⟨a,ha⟩ := enumerate_roots _ (hm.map _) (IsAlgClosed.splits _) hs ((hm.natDegree_map _).trans hn)
  have hroot (i : Fin n) : ‖a i‖ ≤ U := by
    apply hrad
    rw [ha]
    simp only [IsRoot.def,eval_prod,eval_sub,eval_X,eval_C]
    exact prod_eq_zero (mem_univ i) (sub_self _)
  obtain ⟨M,hM,hsep⟩ := exists_separator hn₀ a
  let c : Equiv.Perm (Fin n) ↪ ℂ := ⟨fun σ => tag a σ (M:ℂ),hsep⟩
  let R := resolvent n M f
  have hR : R.map (Int.castRingHom ℂ) = ∏ i, (X-C (c i)) := resolvent_factors a f ha M
  have hRM : R.Monic := (Function.Injective.monic_map_iff (f := Int.castRingHom ℂ)
    (by exact Int.cast_injective)).mpr (hR.symm ▸ monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (c i)))
  have hRD : R.natDegree = n.factorial := by
    rw [← hRM.natDegree_map (Int.castRingHom ℂ),hR,natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (c i))]
    simp [Fintype.card_perm]
  have hc (i) : ‖c i‖ ≤ tagBound n U := by
    refine (tag_norm a hroot i).trans ?_
    exact_mod_cast (by dsimp [tagBound]; gcongr : n*U*(M+1)^n ≤ tagBound n U)
  have hc₀ : 0 < tagBound n U := by dsimp [tagBound]; positivity
  have ⟨hf₁,hf₂⟩ := bad_bound f a ha U hU hroot
  have ⟨hr₁,hr₂⟩ := bad_bound R c hR (tagBound n U) hc₀ hc
  simp only [Fintype.card_fin,Fintype.card_perm] at hf₂ hr₂
  let B := (bad f).natAbs * (bad R).natAbs
  have hb : B ≤ exceptionalBound n U := Nat.mul_le_mul hf₂ hr₂
  obtain ⟨p,hp,hprime,havoid,hr⟩ := bounded_prime_root R c hR (tagBound n U) B (Nat.mul_pos hf₁ hr₁) hc
  let : Fact p.Prime := ⟨hprime⟩
  have hf := separable_at_good_prime f (by omega) p (fun h => havoid (dvd_mul_of_dvd_left h _))
  have hrr := separable_at_good_prime R (by rw [hRD]; exact Nat.factorial_ne_zero _) p
    (fun h => havoid (dvd_mul_of_dvd_right h _))
  refine ⟨p,?_,hprime,split_of_resolvent_root f hm M p hf (hn ▸ hrr) (hn ▸ hr),hf⟩
  simp only [Fintype.card_perm,Fintype.card_fin] at hp
  apply hp.trans
  dsimp [splitBound,schurBound]
  gcongr

#print axioms bounded_splitting_prime
end Erdos478.EffectiveResolvent
