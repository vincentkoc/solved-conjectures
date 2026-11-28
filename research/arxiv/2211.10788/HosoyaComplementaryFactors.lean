import HosoyaSparseFactorMass

/-! The complementary divisor retains every prime power outside the excluded set. -/

namespace Arxiv.«2211.10788».FactorMass

open Finset Real

def cofactor (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p∈n.primeFactors \ S, p^n.factorization p

theorem cofactor_dvd (S : Finset ℕ) {n : ℕ} (hn : n ≠ 0) : cofactor S n ∣ n := by
  unfold cofactor
  exact (prod_dvd_prod_of_subset _ _ _ sdiff_subset).trans
    (dvd_of_eq (Nat.prod_primeFactors_pow_factorization hn).symm)

theorem prime_outside {p n : ℕ} {S : Finset ℕ} (hp : p.Prime) (h : p ∣ cofactor S n) :
    p ∈ n.primeFactors \ S := by
  obtain ⟨q,hq,dv⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
  have eq := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hq).1)).mp
    (hp.dvd_of_dvd_pow dv)
  exact eq ▸ hq

theorem log_cofactor (S : Finset ℕ) (n : ℕ) : log (cofactor S n) + logPart S n = log n := by
  classical
  let w (p : ℕ) := (n.factorization p:ℝ)*log p
  have outside : log (cofactor S n) = ∑ p∈n.primeFactors \ S, w p := by
    unfold cofactor
    push_cast
    rw [log_prod]
    · simp [w,log_pow]
    · intro p hp
      exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1).ne_zero)
  have inside : logPart S n = ∑ p∈n.primeFactors ∩ S, w p := by
    apply (sum_subset inter_subset_right _).symm
    intro p mem miss
    have no : p∉n.factorization.support := fun h => miss (mem_inter.mpr ⟨h,mem⟩)
    simp [Finsupp.notMem_support_iff.mp no]
  rw [outside,inside,log_nat_eq_sum_factorization]
  have union : (n.primeFactors \ S) ∪ (n.primeFactors ∩ S) = n.primeFactors := by
    ext; simp; tauto
  rw [←sum_union (Finset.disjoint_left.mpr (fun p h k => (mem_sdiff.mp h).2 (mem_inter.mp k).2)),union]
  rfl

theorem large_cofactor_of_share_le {S : Finset ℕ} {n : ℕ} {ε : ℝ} (h : share S n ≤ ε) :
    (1-ε)*log n ≤ log (cofactor S n) := by
  have hlog := log_natCast_nonneg n
  have split := log_cofactor S n
  rcases eq_or_lt_of_le hlog with h0|hp
  · have hl := logPart_le S n
    rw [←h0] at *
    linarith
  · have bound := (div_le_iff₀ hp).mp h
    linarith

#print axioms cofactor_dvd
#print axioms prime_outside
#print axioms log_cofactor
#print axioms large_cofactor_of_share_le

end Arxiv.«2211.10788».FactorMass
