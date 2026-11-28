import Green51PeriodSubspaces
import Green51PeriodClassCount

/-! # Exact incidence equations for the dimensions of period spaces -/

namespace Green51PeriodQuotients
open Finset Green53ParityThreshold Green51MissingMasks Green51OriginRecovery
open scoped Classical Pointwise

/-- The labelled period-dimension distribution has these Gaussian-binomial moments.
Each right-hand side uses just one lower-dimensional dense-sumset count. -/
theorem period_spectrum {n h : ℕ} (dim : 3 ≤ n) (k : ℕ) (α : ℝ) :
    ∑ S ∈ countedDoubles (n+h) k α, gaussian (Module.finrank F (periodSpace S)) h =
      gaussian (n+h) h *
        (if 2^h ∣ k then (countedDoubles n (k/2^h) α).card else 0) := by
  classical
  let A := countedDoubles (n+h) k α
  let B := subspaces (n+h) h
  have col (P) (hP : P∈B) :
      (A.filter fun S => P≤periodSpace S).card=
        if 2^h ∣ k then (countedDoubles n (k/2^h) α).card else 0 := by
    have equiv (S : Finset (𝔽₂ (n+h))) : P≤periodSpace S ↔ ∀ t∈P, Green51OriginRecovery.translate S t=S :=
      ⟨fun h t ht => h ht,fun h t ht => h t ht⟩
    rw [filter_congr (fun S _ => equiv S)]
    exact fixed_subspace_count dim P (mem_filter.mp hP).2 k α
  have row (S : Finset (𝔽₂ (n+h))) :
      (B.filter fun P => P≤periodSpace S).card=gaussian (Module.finrank F (periodSpace S)) h :=
    inside_subspace_count (periodSpace S) h
  calc
    _ = ∑ S∈A, (B.filter fun P => P≤periodSpace S).card := sum_congr rfl fun S _ => (row S).symm
    _ = ∑ P∈B, (A.filter fun S => P≤periodSpace S).card := by simp only [card_filter]; rw [sum_comm]
    _ = _ := by rw [sum_congr rfl col,sum_const,smul_eq_mul]; rfl

/-- All actual periods of a counted output lie in the admissible-shift space. -/
theorem period_dimension_bound {s r k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k)
    {S : Finset (𝔽₂ (2*(s+1)+r))}
    (hS : S∈countedDoubles (2*(s+1)+r) k (Green51Hyperplane.threshold (2*s))) :
    Module.finrank F (periodSpace S) ≤ r := by
  classical
  obtain ⟨P,sz,hP⟩ := counted_translations hs near hS
  have inc : periodSpace S≤P := by
    intro b hb
    change Green51OriginRecovery.translate S b=S at hb
    exact (hP b).2.1.mp (hb.symm ▸ hS)
  have rank := Submodule.finrank_mono inc
  have size : (P : Set (𝔽₂ (2*(s+1)+r))).toFinset.card=2^(Module.finrank F P) := by
    rw [Set.toFinset_card]
    change Fintype.card P=_
    rw [Module.card_eq_pow_finrank (K := F),ZMod.card]
  have dim := Nat.pow_right_injective (by decide : 2 ≤ 2) (size.symm.trans sz)
  exact rank.trans_eq dim

/-- The stabilizer order divides the number of missing points, for every binary set. -/
theorem stabilizer_divides {n : ℕ} (S : Finset (𝔽₂ n)) :
    2^(Module.finrank F (periodSpace S)) ∣ Sᶜ.card := by
  classical
  let P := periodSpace S
  let f := P.mkQ
  let : Fintype ((𝔽₂ n) ⧸ P) := Fintype.ofFinite _
  let : DecidableEq ((𝔽₂ n) ⧸ P) := Classical.decEq _
  have stable : ∀ t∈f.ker, Green51OriginRecovery.translate S t=S := by
    intro t ht
    have ht' : t∈P := P.ker_mkQ ▸ ht
    exact ht'
  have div := period_divides_missing f P.mkQ_surjective S stable
  have rk : Module.finrank F f.ker=Module.finrank F P :=
    congrArg (fun Q : Submodule F (𝔽₂ n) => Module.finrank F Q) P.ker_mkQ
  rw [rk] at div
  exact div

/-- The stabilizer dimension gives the exact number of representatives meeting the density
and affine-dimension restrictions. -/
theorem period_fiber {s r k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k)
    {S : Finset (𝔽₂ (2*(s+1)+r))}
    (hS : S∈countedDoubles (2*(s+1)+r) k (Green51Hyperplane.threshold (2*s))) :
    ((countedDoubles (2*(s+1)+r) k (Green51Hyperplane.threshold (2*s))).filter
      fun T => translationClass T=translationClass S).card *
        2^(Module.finrank F (periodSpace S))=2^r := by
  classical
  have val := restricted_fiber_size
    (countedDoubles (2*(s+1)+r) k (Green51Hyperplane.threshold (2*s))) S
  have eq : (periods S)=(periodSpace S : Set (𝔽₂ (2*(s+1)+r))).toFinset := by
    ext b
    simp only [periods,mem_filter,mem_univ,true_and,Set.mem_toFinset]
    rfl
  obtain ⟨P,sz,good⟩ := counted_translations hs near hS
  have allowed : (univ.filter fun t => Green51OriginRecovery.translate S t ∈
      countedDoubles (2*(s+1)+r) k (Green51Hyperplane.threshold (2*s))) =
        (P : Set (𝔽₂ (2*(s+1)+r))).toFinset := by
    ext t
    simpa only [mem_filter,mem_univ,true_and,Set.mem_toFinset,SetLike.mem_coe] using (good t).2.1
  rw [eq,Set.toFinset_card,allowed,sz] at val
  change _ * Fintype.card (periodSpace S)=_ at val
  rwa [Module.card_eq_pow_finrank (K := F),ZMod.card] at val

end Green51PeriodQuotients
#print axioms Green51PeriodQuotients.period_spectrum
#print axioms Green51PeriodQuotients.period_dimension_bound
#print axioms Green51PeriodQuotients.stabilizer_divides
#print axioms Green51PeriodQuotients.period_fiber
