import Green51FixedKernelCount
import Green51RestrictedOrbitCount

/-! # Translation classes with arbitrary missing cardinality -/

namespace Green51PeriodQuotients
open Finset Green53ParityThreshold Green51MissingMasks Green51OriginRecovery
open scoped Classical Pointwise

/-- For any specified subspace of periods, the fixed-output count equals the count in the
quotient dimension. Nondivisible missing cardinalities give zero fixed outputs. -/
theorem fixed_subspace_count {n h : ℕ} (dim : 3 ≤ n) (P : Submodule F (𝔽₂ (n+h)))
    (rank : Module.finrank F P=h) (k : ℕ) (α : ℝ) :
    ((countedDoubles (n+h) k α).filter (fun S => ∀ t∈P, Green51OriginRecovery.translate S t=S)).card =
      if 2^h ∣ k then (countedDoubles n (k/2^h) α).card else 0 := by
  classical
  obtain ⟨f,onto,ker⟩ := projection_with_kernel P rank
  have rk : Module.finrank F f.ker=h := ker ▸ rank
  by_cases dvd : 2^h ∣ k
  · rw [if_pos dvd]
    conv_lhs => rw [← Nat.mul_div_cancel' dvd, ← ker]
    exact fixed_kernel_count dim f onto rk α
  · rw [if_neg dvd,card_eq_zero,eq_empty_iff_forall_notMem]
    rintro S hS
    obtain ⟨inF,stable⟩ := mem_filter.mp hS
    have sz := (mem_filter.mp inF).2.1
    apply dvd
    simpa only [rk,sz] using period_divides_missing f onto S (ker ▸ stable)

/-- In a binary cube all nonzero translations have the same number of fixed outputs. -/
theorem fixed_nonzero_count {n : ℕ} (dim : 3 ≤ n) (t : 𝔽₂ (n+1)) (ht : t≠0)
    (k : ℕ) (α : ℝ) :
    ((countedDoubles (n+1) k α).filter (fun S => Green51OriginRecovery.translate S t=S)).card =
      if 2 ∣ k then (countedDoubles n (k/2) α).card else 0 := by
  classical
  have eq := fixed_subspace_count dim (h := 1) (F ∙ t) (finrank_span_singleton ht) k α
  simpa only [pow_one,fixed_line_iff] using eq

/-- Burnside's count for a family with a fixed number of admissible shifts. -/
theorem translation_count {n : ℕ} (dim : 3 ≤ n) (k : ℕ) (α : ℝ) (m : ℕ)
    (allowed : ∀ S∈countedDoubles (n+1) k α,
      (univ.filter fun t => Green51OriginRecovery.translate S t∈countedDoubles (n+1) k α).card=m) :
    ((countedDoubles (n+1) k α).image translationClass).card*m =
      (countedDoubles (n+1) k α).card +
        (2^(n+1)-1)*(if 2 ∣ k then (countedDoubles n (k/2) α).card else 0) := by
  classical
  let family := countedDoubles (n+1) k α
  let f (t : 𝔽₂ (n+1)) := (family.filter fun S => Green51OriginRecovery.translate S t=S).card
  have zero : f 0=family.card := by simp [f,Green51OriginRecovery.translate_zero]
  have eq := restricted_orbit_count family m allowed
  change _=∑ t : 𝔽₂ (n+1), f t at eq
  rw [←Finset.sum_erase_add _ _ (mem_univ (0 : 𝔽₂ (n+1))),zero,Nat.add_comm (∑ t∈univ.erase (0 : 𝔽₂ (n+1)), f t) family.card] at eq
  rw [eq]
  apply congrArg (family.card+·)
  rw [sum_congr rfl (fun t ht => fixed_nonzero_count dim t (ne_of_mem_erase ht) k α),
    sum_const,smul_eq_mul,card_erase_of_mem (mem_univ _)]
  simp [𝔽₂,𝔽]

open Green51Hyperplane

private theorem count_at_dimension {n k m : ℕ} (dim : 4 ≤ n) (α : ℝ)
    (allowed : ∀ S∈countedDoubles n k α,
      (univ.filter fun t => Green51OriginRecovery.translate S t∈countedDoubles n k α).card=m) :
    ((countedDoubles n k α).image translationClass).card*m=(countedDoubles n k α).card+
      (2^n-1)*(if 2 ∣ k then (countedDoubles (n-1) (k/2) α).card else 0) := by
  cases n with
  | zero => omega
  | succ n => exact translation_count (by omega) k α m allowed

/-- The even correction counts the doubles fixed by a one-dimensional period. This formula
also includes the case when the family is empty. -/
theorem all_class_counts {s r k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) :
    let n := 2*(s+1)+r
    let α := threshold (2*s)
    ((countedDoubles n k α).image translationClass).card*2^r=(countedDoubles n k α).card+
      (2^n-1)*(if 2 ∣ k then (countedDoubles (n-1) (k/2) α).card else 0) := by
  classical
  dsimp only
  apply count_at_dimension (by omega)
  intro S hS
  obtain ⟨P,sz,good⟩ := counted_translations hs near hS
  rw [←sz]
  congr 1
  ext t
  simpa only [mem_filter,mem_univ,true_and,Set.mem_toFinset,SetLike.mem_coe] using (good t).2.1

end Green51PeriodQuotients
#print axioms Green51PeriodQuotients.fixed_subspace_count
#print axioms Green51PeriodQuotients.fixed_nonzero_count
#print axioms Green51PeriodQuotients.translation_count
#print axioms Green51PeriodQuotients.all_class_counts
