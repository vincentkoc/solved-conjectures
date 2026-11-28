import Green51GeelenEquality
import Green51MissingCount

/-! # Periods and affine dimension for extremal doubles -/

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold Green51Hyperplane
open scoped Classical Pointwise symmDiff

/-- A double attaining the sharp missing count misses all cosets of one shortest odd circuit. -/
theorem missing_circuit {s r : ℕ} (hs : 0 < s) (A : Finset (𝔽₂ (2 * (s + 1) + r)))
    (large : threshold (2 * s) < (A.dens : ℝ)) (avoid : AvoidsAffineHyperplanes A)
    (equality : (2 * s + 3) * 2 ^ r ≤ (A + A)ᶜ.card) :
    ∃ C, ShortestOddCircuit (A + A)ᶜ C ∧ C.card = 2 * s + 3 ∧ ∃ P : Submodule F (𝔽₂ (2 * (s + 1) + r)),
      Module.finrank F P = r ∧ IsCompl P (Submodule.span F (C : Set _)) ∧
      ∀ x, x ∈ (A + A)ᶜ ↔ ∃ t ∈ P, ∃ i ∈ C, x = t + i := by
  let D := (A + A)ᶜ
  have ambient : Module.finrank F (𝔽₂ (2 * (s + 1) + r)) = 2 * (s + 1) + r := by simp [𝔽₂, 𝔽]
  obtain ⟨C, m, g, P, compl, full⟩ := geelen_equality D (2 * (s + 1) + 1) (by omega)
    (girth_of_density A s large) (missing_nonaffine avoid) (by
      rw [ambient, show 2 * (s + 1) + r + 1 - (2 * (s + 1) + 1) = r by omega]
      simpa [show 2 * (s + 1) + 1 = 2 * s + 3 by omega] using equality)
  have rc := circuit_rank m
  have rp := Submodule.finrank_add_eq_of_isCompl compl
  rw [ambient] at rp
  exact ⟨C, m, by omega, P, by omega, compl, full⟩

/-- An extremal double has affine dimension exactly two below the ambient dimension. -/
theorem flat_dimension_at_equality {s r : ℕ} (hs : 0 < s) (A : Finset (𝔽₂ (2 * (s + 1) + r)))
    (large : threshold (2 * s) < (A.dens : ℝ)) (avoid : AvoidsAffineHyperplanes A)
    (equality : (2 * s + 3) * 2 ^ r ≤ (A + A)ᶜ.card) :
    maxCosetDim F (𝔽₂ (2 * (s + 1) + r)) ↑(A + A) = 2 * s + r := by
  let n := 2 * (s + 1) + r
  obtain ⟨C, m, g, P, _, compl, full⟩ := missing_circuit hs A large avoid equality
  obtain ⟨f, nz⟩ := extremal_coordinates m (by omega) compl full
  have ambient : Module.finrank F (𝔽₂ n) = n := by simp [𝔽₂, 𝔽]
  have lo : Module.finrank F f.ker ≤ maxCosetDim F (𝔽₂ n) ↑(A + A) := by
    apply le_csSup
    · refine ⟨n, ?_⟩
      rintro _ ⟨S, _, rfl⟩; exact (Submodule.finrank_le S.direction).trans_eq ambient
    · refine ⟨f.ker.toAffineSubspace, ?_, by rw [Submodule.toAffineSubspace_direction]⟩
      intro x hx; by_contra bad
      exact nz x (Finset.mem_compl.mpr bad) (LinearMap.mem_ker.mp hx)
  have dim := f.finrank_range_add_finrank_ker
  have range := Submodule.finrank_le f.range
  simp only [Module.finrank_prod, Module.finrank_self] at range
  rw [ambient] at dim
  have hi := (avoids_iff_maxCosetDim (by omega) A).mp avoid
  dsimp only [n] at lo dim
  omega

variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]

/-- Filling the period cosets of an input preserves its double. -/
theorem fill_periods (A C : Finset G) (P : Submodule F G)
    (full : ∀ x, x ∈ (A + A)ᶜ ↔ ∃ t ∈ P, ∃ i ∈ C, x = t + i) :
    A ⊆ A + (P : Set G).toFinset ∧
    (A + (P : Set G).toFinset) + (A + (P : Set G).toFinset) = A + A := by
  classical
  have sub : A ⊆ A + (P : Set G).toFinset :=
    fun a ha => mem_add.mpr ⟨a, ha, 0, Set.mem_toFinset.mpr P.zero_mem, add_zero _⟩
  have invariant {x t : G} (hx : x ∈ A + A) (ht : t ∈ P) : x + t ∈ A + A := by
    by_contra absent
    obtain ⟨u, hu, i, hi, eq⟩ := (full _).mp (mem_compl.mpr absent)
    have pre : x ∈ (A + A)ᶜ := (full _).mpr ⟨u + t, P.add_mem hu ht, i, hi, by
      calc
        x = (x + t) + t := by rw [add_assoc, ZModModule.add_self, add_zero]
        _ = (u + t) + i := by rw [eq, add_right_comm]⟩
    exact (mem_compl.mp pre) hx
  refine ⟨sub, Subset.antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    obtain ⟨a, ha, t, ht, rfl⟩ := mem_add.mp hx
    obtain ⟨b, hb, u, hu, rfl⟩ := mem_add.mp hy
    rw [add_add_add_comm]
    exact invariant (mem_add.mpr ⟨a, ha, b, hb, rfl⟩) (P.add_mem (Set.mem_toFinset.mp ht) (Set.mem_toFinset.mp hu))
  · intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hz
    exact mem_add.mpr ⟨a, sub ha, b, sub hb, rfl⟩

private theorem fill_at_density {s n : ℕ} (A : Finset (𝔽₂ n)) {C : Finset (𝔽₂ n)}
    (m : ShortestOddCircuit (A + A)ᶜ C) (g : C.card = 2 * s + 3) (P : Submodule F (𝔽₂ n))
    (full : ∀ x, x ∈ (A + A)ᶜ ↔ ∃ t ∈ P, ∃ i ∈ C, x = t + i) :
    let B := A + (P : Set _).toFinset
    A ⊆ B ∧ B + B = A + A ∧ (B.dens : ℝ) ≤ threshold (2 * (s + 1)) ∧
      (threshold (2 * (s + 1)) ≤ (A.dens : ℝ) → B = A) := by
  classical
  obtain ⟨sub, eq⟩ := fill_periods A C P full
  let B := A + (P : Set _).toFinset
  have cap : (B.dens : ℝ) ≤ threshold (2 * (s + 1)) := by
    by_contra! higher
    have circ : C ⊆ (B + B)ᶜ := by rw [show B + B = A + A from eq]; exact m.1
    have bigger := girth_of_density B (s + 1) higher C circ m.2.1 m.2.2.1
    omega
  refine ⟨sub, eq, cap, ?_⟩
  intro at_edge
  by_contra ne
  have strict := dens_lt_dens (show A ⊂ B from sub.ssubset_of_ne (Ne.symm ne))
  have : (A.dens : ℝ) < (B.dens : ℝ) := by exact_mod_cast strict
  linarith

/-- An extremal input extends to a periodic input of bounded density with exactly the same double. -/
theorem periodic_completion {s r : ℕ} (hs : 0 < s) (A : Finset (𝔽₂ (2 * (s + 1) + r)))
    (large : threshold (2 * s) < (A.dens : ℝ)) (avoid : AvoidsAffineHyperplanes A)
    (equality : (2 * s + 3) * 2 ^ r ≤ (A + A)ᶜ.card) :
    ∃ P : Submodule F (𝔽₂ (2 * (s + 1) + r)), Module.finrank F P = r ∧
      ∃ B : Finset (𝔽₂ (2 * (s + 1) + r)), B = A + (P : Set _).toFinset ∧ A ⊆ B ∧ B + B = A + A ∧
        (B.dens : ℝ) ≤ threshold (2 * (s + 1)) ∧
        (threshold (2 * (s + 1)) ≤ (A.dens : ℝ) → B = A) := by
  classical
  obtain ⟨C, m, g, P, rk, _, full⟩ := missing_circuit hs A large avoid equality
  exact ⟨P, rk, _, rfl, fill_at_density A m g P full⟩


/-- At the top density, the original input has a full period space of exactly the extra dimension. -/
theorem input_period_on_edge {s r : ℕ} (hs : 0 < s) (A : Finset (𝔽₂ (2 * (s + 1) + r)))
    (large : threshold (2 * s) < (A.dens : ℝ)) (avoid : AvoidsAffineHyperplanes A)
    (equality : (2 * s + 3) * 2 ^ r ≤ (A + A)ᶜ.card) (edge : threshold (2 * (s + 1)) ≤ (A.dens : ℝ)) :
    ∃ P : Submodule F (𝔽₂ (2 * (s + 1) + r)), Module.finrank F P = r ∧
      ∀ t, t ∈ P ↔ ∀ x ∈ A, x + t ∈ A := by
  classical
  obtain ⟨C, m, g, P, rk, compl, full⟩ := missing_circuit hs A large avoid equality
  have same := (fill_at_density A m g P full).2.2.2 edge
  refine ⟨P, rk, fun t => ⟨?_, ?_⟩⟩
  · intro ht x hx
    have subset : A + (P : Set _).toFinset ⊆ A := same.le
    apply subset
    exact mem_add.mpr ⟨x, hx, t, Set.mem_toFinset.mpr ht, rfl⟩
  · intro stable
    apply (periods_iff m (by omega) compl full t).mpr
    intro x hx
    apply mem_compl.mpr
    intro bad
    obtain ⟨a, ha, b, hb, eq⟩ := mem_add.mp bad
    have rep : (a + t) + b = x := by
      rw [add_right_comm, eq, add_assoc, ZModModule.add_self, add_zero]
    exact (mem_compl.mp hx) (mem_add.mpr ⟨a + t, stable a ha, b, hb, rep⟩)


/-- Every subset of an extremal input above the density threshold has the same double. -/
theorem stable_under_deletions {s r : ℕ} (hs : 0 < s) {A B : Finset (𝔽₂ (2 * (s + 1) + r))}
    (sub : A ⊆ B) (large : threshold (2 * s) < (A.dens : ℝ)) (avoid : AvoidsAffineHyperplanes B)
    (extremal : (2 * s + 3) * 2 ^ r ≤ (B + B)ᶜ.card) : A + A = B + B := by
  classical
  have sums : A + A ⊆ B + B := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hx
    exact mem_add.mpr ⟨a, sub ha, b, sub hb, rfl⟩
  have misses : (B + B)ᶜ ⊆ (A + A)ᶜ := fun _ hx => mem_compl.mpr (fun ha => mem_compl.mp hx (sums ha))
  have no : AvoidsAffineHyperplanes A := fun S nonempty inc => avoid S nonempty (fun x hx => sums (inc x hx))
  have upper := missing_bound hs A large no
  rw [show 2 * (s + 1) + r - 2 * (s + 1) = r by omega] at upper
  have same := eq_of_subset_of_card_le misses (upper.trans extremal)
  simpa only [compl_compl] using congrArg (fun W : Finset (𝔽₂ (2 * (s + 1) + r)) => Wᶜ) same.symm

end Green51GirthFrame

#print axioms Green51GirthFrame.missing_circuit
#print axioms Green51GirthFrame.flat_dimension_at_equality
#print axioms Green51GirthFrame.fill_periods
#print axioms Green51GirthFrame.periodic_completion
#print axioms Green51GirthFrame.input_period_on_edge
#print axioms Green51GirthFrame.stable_under_deletions
