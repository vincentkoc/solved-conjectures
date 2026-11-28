import Green51GeelenGirth
import Green51LogDensityWindow
import Green51ThresholdExample

/-! # The sharp number of missing directions when the double avoids hyperplanes -/

open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff

namespace Green51GirthFrame
open Green51Hyperplane

/-- The double of `A` contains no nonempty affine subspace of codimension at most one. -/
def AvoidsAffineHyperplanes (A : Finset (𝔽₂ n)) : Prop :=
  ∀ S : AffineSubspace F (𝔽₂ n), (∃ x, x ∈ S) →
    (∀ x ∈ S, x ∈ A + A) → Module.finrank F S.direction + 1 < n


/-- The hyperplane condition written using Green's pinned affine-dimension function. -/
theorem avoids_iff_maxCosetDim {n : ℕ} (hn : 2 ≤ n) (A : Finset (𝔽₂ n)) :
    AvoidsAffineHyperplanes A ↔ maxCosetDim F (𝔽₂ n) ↑(A + A) ≤ n - 2 := by
  constructor
  · intro avoids
    apply csSup_le
    · exact ⟨0, ⊥, by simp, by simp⟩
    · rintro _ ⟨S, sub, rfl⟩
      by_cases nonempty : ∃ x, x ∈ S
      · have bound : Module.finrank F S.direction + 1 < n := avoids S nonempty (fun _ hx => sub hx)
        exact Nat.le_sub_of_add_le bound
      · have bot : S = ⊥ := by
          ext x
          simp only [AffineSubspace.notMem_bot, iff_false]
          exact fun hx => nonempty ⟨x, hx⟩
        rw [bot, AffineSubspace.direction_bot]
        simp
  · intro bound S _ sub
    have le : Module.finrank F S.direction ≤ maxCosetDim F (𝔽₂ n) ↑(A + A) := by
      apply le_csSup
      · refine ⟨n, ?_⟩
        rintro _ ⟨T, _, rfl⟩
        simpa [𝔽₂, 𝔽] using Submodule.finrank_le T.direction
      · exact ⟨S, fun _ hx => sub _ hx, rfl⟩
    omega

/-- When the double avoids hyperplanes, its missing directions are nonaffine. -/
theorem missing_nonaffine {n : ℕ} {A : Finset (𝔽₂ n)} (avoids : AvoidsAffineHyperplanes A) :
    ¬∃ f : (𝔽₂ n) →ₗ[F] F, ∀ x ∈ (A + A)ᶜ, f x = 1 := by
  classical
  rintro ⟨f, one⟩
  have sub (x) (hx : x ∈ f.ker) : x ∈ A + A := by
    by_contra notmem
    exact one_ne_zero ((one x (Finset.mem_compl.mpr notmem)).symm.trans (LinearMap.mem_ker.mp hx))
  have low := avoids f.ker.toAffineSubspace ⟨0, f.ker.zero_mem⟩ (fun x hx => sub x hx)
  rw [Submodule.toAffineSubspace_direction] at low
  have eq := f.finrank_range_add_finrank_ker
  have r := Submodule.finrank_le f.range
  simp [𝔽₂, 𝔽] at eq r
  omega

/-- A density threshold bounds the number of directions missed by a double without a hyperplane. -/
theorem missing_bound {s n : ℕ} (hs : 0 < s) (A : Finset (𝔽₂ n))
    (large : threshold (2 * s) < (A.dens : ℝ)) (avoids : AvoidsAffineHyperplanes A) :
    (A + A)ᶜ.card ≤ (2 * s + 3) * 2 ^ (n - 2 * (s + 1)) := by
  classical
  let D := (A + A)ᶜ
  have count := geelen_bound D (2 * (s + 1) + 1) (by omega) (girth_of_density A s large) (missing_nonaffine avoids)
  simpa [𝔽₂, 𝔽, D, show 2 * (s + 1) + 1 = 2 * s + 3 by omega, show n + 1 - (2 * s + 3) = n - 2 * (s + 1) by omega] using count

/-- Hamming cylinders attain the largest possible number of missing directions throughout the interval. -/
theorem sharp_missing {s r : ℕ} (hs : 0 < s) {α : ℝ}
    (low : threshold (2 * s)< α) (high : α ≤ threshold (2 * (s + 1))) :
    IsGreatest {k : ℕ | ∃ A : Finset (𝔽₂ (2 * (s + 1) + r)), α ≤ (A.dens : ℝ) ∧
      AvoidsAffineHyperplanes A ∧ (A + A)ᶜ.card = k} ((2 * s + 3) * 2 ^ r) := by
  constructor
  · obtain ⟨A, size, count, avoids⟩ := hamming_cylinder (s + 1) r
    refine ⟨A, high.trans ?_, avoids, ?_⟩
    · have eq : (2 : ℝ) * A.card + 2 ^ r * ((2 * (s + 1)).choose (s + 1) : ℝ) = 2 ^ (2 * (s + 1) + r) := by exact_mod_cast size
      rw [threshold, Nat.mul_div_cancel_left _ (by decide : 0 < 2), nnratCast_dens]
      unfold halfLayer
      simp only [𝔽₂, 𝔽, Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
      rw [pow_add] at eq ⊢
      apply le_of_eq
      apply (eq_div_iff (by positivity)).mpr
      field_simp
      nlinarith [eq]
    · rw [count]; ring
  · rintro k ⟨A, ha, avoid, rfl⟩
    simpa using missing_bound hs A (low.trans_le ha) avoid

/-- The sharp missing count for the exact affine-dimension predicate in Green 51. -/
theorem sharp_missing_cosetDim {s r : ℕ} (hs : 0 < s) {α : ℝ}
    (low : threshold (2 * s) < α) (high : α ≤ threshold (2 * (s + 1))) :
    IsGreatest {k : ℕ | ∃ A : Finset (𝔽₂ (2 * (s + 1) + r)), α ≤ (A.dens : ℝ) ∧
      maxCosetDim F (𝔽₂ (2 * (s + 1) + r)) ↑(A + A) ≤ 2 * s + r ∧ (A + A)ᶜ.card = k}
      ((2 * s + 3) * 2 ^ r) := by
  have threshold_dim : 2 * (s + 1) + r - 2 = 2 * s + r := by omega
  simpa only [avoids_iff_maxCosetDim (by omega : 2 ≤ 2 * (s + 1) + r), threshold_dim] using
    (sharp_missing (r := r) hs low high)

end Green51GirthFrame
#print axioms Green51GirthFrame.avoids_iff_maxCosetDim
#print axioms Green51GirthFrame.missing_nonaffine
#print axioms Green51GirthFrame.missing_bound
#print axioms Green51GirthFrame.sharp_missing
#print axioms Green51GirthFrame.sharp_missing_cosetDim
