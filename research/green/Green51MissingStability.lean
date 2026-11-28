import Green51GreatestExtension
import Green51MissingCount

/-! # Missing directions near the extremal count -/

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold Green51Hyperplane
open scoped Classical Pointwise symmDiff
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A circuit container avoids the kernel of a linear map to two binary coordinates. -/
theorem container_coordinates {C D : Finset G} (m : ShortestOddCircuit D C) (g : 5 ≤ C.card)
    {P : Submodule F G} (compl : IsCompl P (Submodule.span F (C : Set G)))
    (full : ∀ x ∈ D, ∃ t ∈ P, ∃ i ∈ C, x = t + i) :
    ∃ f : G →ₗ[F] F × F, ∀ x ∈ D, f x ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < C.card by omega)
  have er := card_erase_of_mem hp
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < (C.erase p).card by omega)
  have er2 := card_erase_of_mem hi
  obtain ⟨j, hj⟩ := card_pos.mp (show 0 < ((C.erase p).erase i).card by omega)
  obtain ⟨ji, jmem⟩ := mem_erase.mp hj
  have ind := independent_erase m hp
  obtain ⟨f, fi, _⟩ := coordinate_colour m hp (Subset.rfl : C.erase p ⊆ C.erase p) ind hi
  obtain ⟨h, hj, _⟩ := coordinate_colour m hp (Subset.rfl : C.erase p ⊆ C.erase p) ind jmem
  let V := Submodule.span F (C : Set G)
  let proj : G →ₗ[F] G := V.subtype.comp (V.projectionOnto P compl.symm)
  refine ⟨(f.prod h).comp proj, ?_⟩
  intro x hx
  obtain ⟨t, ht, a, ha, rfl⟩ := full x hx
  have ad : a ∈ V := Submodule.subset_span ha
  have t0 : proj t = 0 := by
    change ((V.projectionOnto P compl.symm t : V) : G) = 0
    rw [Submodule.projectionOnto_apply_of_mem_right compl.symm ht]; rfl
  have a0 : proj a = a := by
    change ((V.projectionOnto P compl.symm a : V) : G) = a
    rw [Submodule.projectionOnto_apply_of_mem_left compl.symm ad]
  change (f (proj (t + a)), h (proj (t + a))) ≠ 0
  rw [map_add, t0, a0, zero_add]
  intro eq
  by_cases ai : a = i
  · have z : h a = 0 := congrArg Prod.snd eq
    rw [hj a ha (by exact ai ▸ Ne.symm ji)] at z
    exact one_ne_zero z
  · have z : f a = 0 := congrArg Prod.fst eq
    exact one_ne_zero ((fi a ha ai).symm.trans z)

/-- In the stability range for missing directions, the largest affine subspace of the double has codimension two. -/
theorem flat_dimension_near_max {s r : ℕ} (hs : 0 < s) (A : Finset (𝔽₂ (2 * (s + 1) + r)))
    (large : threshold (2 * s) < (A.dens : ℝ)) (avoid : AvoidsAffineHyperplanes A)
    (near : min (5 * (2 * s + 3) + 12) (4 * (2 * s + 3) + 20) * 2 ^ r < 8 * (A + A)ᶜ.card) :
    maxCosetDim F (𝔽₂ (2 * (s + 1) + r)) ↑(A + A) = 2 * s + r := by
  let n := 2 * (s + 1) + r
  let D := (A + A)ᶜ
  have hdim : Module.finrank F (𝔽₂ (2 * (s + 1) + r)) = 2 * (s + 1) + r := by simp [𝔽₂, 𝔽]
  obtain ⟨C, m, g, P, compl, greatest, _⟩ := greatest_girth_extension D (2 * (s + 1) + 1) (by omega)
    ⟨s + 1, rfl⟩ (girth_of_density A s large) (missing_nonaffine avoid) (by
      rw [hdim, show 2 * (s + 1) + r + 1 - (2 * (s + 1) + 1) = r by omega]
      simpa [show 2 * (s + 1) + 1 = 2 * s + 3 by omega] using near)
  have inside (x : 𝔽₂ n) (hx : x ∈ D) : ∃ t ∈ P, ∃ i ∈ C, x = t+i := by
    obtain ⟨t, ht, i, hi, eq⟩ := Finset.mem_add.mp (greatest.1.1 hx)
    exact ⟨t, Set.mem_toFinset.mp ht, i, hi, eq.symm⟩
  obtain ⟨f, nz⟩ := container_coordinates m (by omega) compl inside
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

end Green51GirthFrame
#print axioms Green51GirthFrame.container_coordinates
#print axioms Green51GirthFrame.flat_dimension_near_max
