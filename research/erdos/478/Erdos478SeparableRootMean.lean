import Erdos478GapSplittingTest

/-!
# Prime mean of a separable polynomial root count

Peeling off integral monic lifts of irreducible rational factors gives the
number of factors as the limiting mean. Coprimality after reduction is
needed only away from the derivative resultant of the whole polynomial.
-/

namespace Erdos478.CollisionLaw
noncomputable section
open Polynomial Finset Filter Topology RootPairs RootMoments UniqueFactorizationMonoid

def factorCount (f : ℤ[X]) := (normalizedFactors (f.map (Int.castRingHom ℚ))).card

theorem count_roots (f : ℤ[X]) (hm : f.Monic) (p : ℕ) [Fact p.Prime]
    (hs : (f.map (Int.castRingHom (ZMod p))).Separable) :
    roots f p = (((f.map (Int.castRingHom (ZMod p))).roots.card : ℕ) : ℝ) := by
  classical
  let F := f.map (Int.castRingHom (ZMod p))
  let e : solutions f (ZMod p) ≃ F.roots.toFinset :=
    Equiv.subtypeEquivRight fun x => by simp [F,mem_roots (hm.map _).ne_zero,IsRoot,eval_map]
  change (Nat.card _ : ℝ)=(F.roots.card : ℝ)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,
    Multiset.toFinset_card_of_nodup (nodup_roots hs)]

theorem mean_of_change (A : PrimeAverage) {a b : ℕ → ℝ} {c : ℝ}
    (B : ℕ) (eq : ∀ p>B, p.Prime → a p=b p)
    (lim : Tendsto (fun X => A.avg X b) atTop (𝓝 c)) :
    Tendsto (fun X => A.avg X a) atTop (𝓝 c) := by
  simpa only [sub_add_cancel,zero_add] using (A.finite_change B eq).add lim

/-- The mean of the root count is the number of irreducible rational factors. -/
theorem polynomial_mean (A : PrimeAverage) (f : ℤ[X]) (hm : f.Monic)
    (hs : (f.map (Int.castRingHom ℚ)).Separable) :
    Tendsto (fun X => A.avg X (roots f)) atTop (𝓝 (factorCount f : ℝ)) := by
  classical
  by_cases hz : f.natDegree=0
  · have he := hm.natDegree_eq_zero.mp hz
    subst f
    simp only [factorCount,Polynomial.map_one,normalizedFactors_one,Multiset.card_zero,Nat.cast_zero]
    apply mean_of_change A (b:=0) 0
    · intro p _ h
      let : Fact p.Prime := ⟨h⟩
      rw [count_roots 1 monic_one p (by simp)]
      simp
    · simp
  let φ := Int.castRingHom ℚ
  have hnon : ¬IsUnit (f.map φ) := not_isUnit_of_natDegree_pos _ (by rw [hm.natDegree_map]; omega)
  obtain ⟨G,hGm,hGI,hdiv⟩ := exists_monic_irreducible_factor (f.map φ) hnon
  obtain ⟨g,hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hm hdiv
  have hgE : g.map φ=G := by simpa [hGm.leadingCoeff] using hg
  have hgm : g.Monic := (Function.Injective.monic_map_iff (f:=φ) (by exact Int.cast_injective)).mpr (hgE ▸ hGm)
  have hgi : Irreducible (g.map φ) := hgE ▸ hGI
  have hd : g∣f := (map_dvd_map φ (by exact Int.cast_injective) hgm).mp (hgE ▸ hdiv)
  obtain ⟨h,hfh⟩ := hd
  have hhm : h.Monic := hgm.of_mul_monic_left (hfh ▸ hm)
  have hsep : (h.map φ).Separable := hs.of_dvd (map_dvd φ (hfh ▸ dvd_mul_left h g))
  have hgd : 0<g.natDegree := (hgm.natDegree_map φ) ▸ hgi.natDegree_pos
  have hhd : h.natDegree<f.natDegree := by rw [hfh,natDegree_mul hgm.ne_zero hhm.ne_zero]; omega
  have ih := polynomial_mean A h hhm hsep
  have ig := first_mean A g hgm hgi
  have hf : factorCount f=1+factorCount h := by
    unfold factorCount
    rw [hfh,Polynomial.map_mul,normalizedFactors_mul (hgm.map _).ne_zero (hhm.map _).ne_zero,
      Multiset.card_add,normalizedFactors_irreducible hgi,Multiset.card_singleton]
  rw [hf,Nat.cast_add,Nat.cast_one]
  apply mean_of_change A (b:=RootMoments.roots g+RootMoments.roots h) (f.resultant f.derivative).natAbs
  · intro p hp hpr
    let : Fact p.Prime := ⟨hpr⟩
    let j := Int.castRingHom (ZMod p)
    have sp := GapFamilies.separable_mod_above_resultant f hz hs hp
    have sc : (g.map j*h.map j).Separable := by simpa [hfh,Polynomial.map_mul,j] using sp
    rw [Pi.add_apply,count_roots f hm p sp,count_roots g hgm p sc.of_mul_left,
      count_roots h hhm p sc.of_mul_right,hfh,Polynomial.map_mul,
      roots_mul (mul_ne_zero (hgm.map _).ne_zero (hhm.map _).ne_zero),Multiset.card_add,Nat.cast_add]
  · simpa only [map_add] using ig.add ih
termination_by f.natDegree

#print axioms count_roots
#print axioms mean_of_change
#print axioms polynomial_mean
end
end Erdos478.CollisionLaw
