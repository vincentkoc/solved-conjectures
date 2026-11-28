import Green51FixedKernelCount

/-! # Counting subspaces of the translation stabilizer -/

namespace Green51PeriodQuotients
open Finset Green53ParityThreshold Green51OriginRecovery
open scoped Classical Pointwise

/-- A binary set's translation stabilizer, regarded as a linear subspace. -/
def periodSpace {n : ℕ} (S : Finset (𝔽₂ n)) : Submodule F (𝔽₂ n) where
  carrier := {t | Green51OriginRecovery.translate S t=S}
  zero_mem' := Green51OriginRecovery.translate_zero S
  add_mem' := by
    intro x y hx hy
    change Green51OriginRecovery.translate S (x+y)=S
    rw [←translate_twice,show Green51OriginRecovery.translate S x=S from hx]
    exact hy
  smul_mem' := by
    intro a x hx
    change Green51OriginRecovery.translate S x=S at hx
    change Green51OriginRecovery.translate S (a • x)=S
    have binary : ∀ i : F, i=0 ∨ i=1 := by decide
    rcases binary a with rfl | rfl
    · simpa only [zero_smul] using Green51OriginRecovery.translate_zero S
    · simpa only [one_smul] using hx

private noncomputable instance finiteSubspaces {n : ℕ} : Fintype (Submodule F (𝔽₂ n)) :=
  Fintype.ofInjective (fun P : Submodule F (𝔽₂ n) => (P : Set (𝔽₂ n))) SetLike.coe_injective

noncomputable def subspaces (n j : ℕ) : Finset (Submodule F (𝔽₂ n)) :=
  univ.filter fun P => Module.finrank F P=j

/-- The number of binary subspaces of dimension `j` in dimension `n`. -/
noncomputable def gaussian (n j : ℕ) := (subspaces n j).card

theorem gaussian_diagonal (n : ℕ) : gaussian n n=1 := by
  classical
  have amb : Module.finrank F (𝔽₂ n)=n := by simp [𝔽₂,𝔽]
  have eq : subspaces n n={⊤} := by
    ext P
    simp only [subspaces,mem_filter,mem_univ,true_and,mem_singleton]
    simpa only [amb] using (Submodule.eq_top_iff_finrank_eq (W := P)).symm
  simp [gaussian,eq]

theorem gaussian_above {n j : ℕ} (above : n<j) : gaussian n j=0 := by
  classical
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro P h
  have rk := (mem_filter.mp h).2
  have amb : Module.finrank F (𝔽₂ n)=n := by simp [𝔽₂,𝔽]
  have le := P.finrank_le
  omega

theorem inside_subspace_count {n : ℕ} (P : Submodule F (𝔽₂ n)) (j : ℕ) :
    ((subspaces n j).filter fun Q => Q≤P).card=gaussian (Module.finrank F P) j := by
  classical
  let d := Module.finrank F P
  let e : (𝔽₂ d) ≃ₗ[F] P := LinearEquiv.ofFinrankEq _ _ (by simp [𝔽₂,𝔽,d])
  let I := (Submodule.orderIsoMapComap e).trans (Submodule.MapSubtype.orderIso P)
  have rk (Q : Submodule F (𝔽₂ d)) : Module.finrank F (I Q).val=Module.finrank F Q :=
    (P.finrank_map_subtype_eq _).trans (e.finrank_map_eq Q)
  symm
  apply card_bij (fun Q _ => (I Q).val)
  · intro Q hQ
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (rk Q).trans (mem_filter.mp hQ).2⟩,
      (I Q).property⟩
  · intro Q _ R _ eq
    exact I.injective (Subtype.ext eq)
  · intro L hL
    obtain ⟨inGr,sub⟩ := mem_filter.mp hL
    obtain ⟨Q,hQ⟩ := I.surjective ⟨L,sub⟩
    have eq : (I Q).val=L := congrArg Subtype.val hQ
    exact ⟨Q,mem_filter.mpr ⟨mem_univ _,(rk Q).symm.trans (eq ▸ (mem_filter.mp inGr).2)⟩,eq⟩

end Green51PeriodQuotients
#print axioms Green51PeriodQuotients.gaussian_diagonal
#print axioms Green51PeriodQuotients.gaussian_above
#print axioms Green51PeriodQuotients.inside_subspace_count
