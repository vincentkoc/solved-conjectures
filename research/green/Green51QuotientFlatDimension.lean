import Green51DensePeriodQuotient

/-! # Largest affine subspace in the full inverse image of a nonempty set -/

namespace Green51PeriodQuotients
open Finset Green53ParityThreshold
open scoped Classical Pointwise
variable {G H : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
  [AddCommGroup H] [Module F H] [Fintype H] [DecidableEq H]

omit [DecidableEq G] in
private theorem flat_size (T : AffineSubspace F G) (a : T) :
    (T : Set G).toFinset.card=2^Module.finrank F T.direction := by
  classical
  have : Nonempty T := ⟨a⟩
  rw [Set.toFinset_card]
  change Fintype.card T=_
  rw [←Fintype.card_congr (Equiv.vaddConst a : T.direction ≃ T),
    Module.card_eq_pow_finrank (K := F),ZMod.card]

private theorem comap_rank (f : G →ₗ[F] H) (onto : Function.Surjective f)
    (T : AffineSubspace F H) (a : T) :
    Module.finrank F (T.comap f.toAffineMap).direction =
      Module.finrank F f.ker + Module.finrank F T.direction := by
  classical
  obtain ⟨x,hx⟩ := onto a.val
  have inT : x∈T.comap f.toAffineMap := AffineSubspace.mem_comap.mpr (by change f x∈T;rw [hx];exact a.property)
  have sets : ((T.comap f.toAffineMap : AffineSubspace F G) : Set G).toFinset=pull f (T : Set H).toFinset := by
    ext z; simp only [Set.mem_toFinset,mem_pull,SetLike.mem_coe,AffineSubspace.mem_comap];rfl
  have ker : (f.ker : Set G).toFinset.card=2^Module.finrank F f.ker := by
    rw [Set.toFinset_card];change Fintype.card f.ker=_
    rw [Module.card_eq_pow_finrank (K := F),ZMod.card]
  apply Nat.pow_right_injective (by decide : 2≤2)
  dsimp only
  rw [←flat_size _ ⟨x,inT⟩,sets,card_pull f onto,flat_size T a,ker,pow_add]

omit [DecidableEq G] in
private theorem attained_flat {S : Finset G} (pos : S.Nonempty) :
    ∃ (T : AffineSubspace F G), (T : Set G) ⊆ S ∧ Nonempty T ∧
      Module.finrank F T.direction=maxCosetDim F G ↑S := by
  classical
  let dims : Set ℕ := {Module.finrank F U.direction | (U : AffineSubspace F G) (_h : (U : Set G) ⊆ S)}
  have bd : BddAbove dims := ⟨Module.finrank F G,by rintro _ ⟨U,_,rfl⟩;exact Submodule.finrank_le U.direction⟩
  obtain ⟨T,hT,dim⟩ := Nat.sSup_mem (show dims.Nonempty from ⟨0,⊥,by simp,by simp⟩) bd
  by_cases h : Nonempty T
  · exact ⟨T,hT,h,dim⟩
  have bot : T=⊥ := by
    ext x; simp only [AffineSubspace.notMem_bot,iff_false];exact fun hx => h ⟨x,hx⟩
  rw [bot,AffineSubspace.direction_bot,finrank_bot] at dim
  obtain ⟨a,ha⟩ := pos
  let U : AffineSubspace F G := AffineSubspace.mk' a ⊥
  have one : (U : Set G)={a} := by ext x; simp [U,AffineSubspace.mem_mk',vsub_eq_sub,sub_eq_zero]
  refine ⟨U,by rw [one]; exact Set.singleton_subset_iff.mpr ha,?_,?_⟩
  · exact ⟨a,show a∈(U : Set G) from one.symm ▸ Set.mem_singleton a⟩
  · change Module.finrank F (AffineSubspace.mk' a (⊥ : Submodule F G)).direction = sSup dims
    rwa [AffineSubspace.direction_mk',finrank_bot]

/-- For a nonempty output set, quotienting removes precisely the kernel dimension from
the maximal affine dimension of its full inverse image. -/
theorem max_dimension_pull (f : G →ₗ[F] H) (onto : Function.Surjective f)
    (S : Finset H) (pos : S.Nonempty) :
    maxCosetDim F G ↑(pull f S) = Module.finrank F f.ker+maxCosetDim F H ↑S := by
  classical
  obtain ⟨a,ha⟩ := pos
  obtain ⟨x,rfl⟩ := onto a
  have live : (pull f S).Nonempty := ⟨x,(mem_pull _ _ _).mpr ha⟩
  obtain ⟨T,hT,⟨t⟩,rk⟩ := attained_flat live
  obtain ⟨U,hU,⟨u⟩,ur⟩ := attained_flat (show S.Nonempty from ⟨_,ha⟩)
  apply le_antisymm
  · let I := T.map f.toAffineMap
    have i : I := ⟨f t,AffineSubspace.mem_map.mpr ⟨_,t.property,rfl⟩⟩
    have hi : (I : Set H) ⊆ S := by
      intro y hy; obtain ⟨z,hz,rfl⟩ := AffineSubspace.mem_map.mp hy;exact (mem_pull _ _ _).mp (hT hz)
    have inside : T ≤ I.comap f.toAffineMap := fun z hz => AffineSubspace.mem_comap.mpr (AffineSubspace.mem_map.mpr ⟨z,hz,rfl⟩)
    have upper := Submodule.finrank_mono (AffineSubspace.direction_le inside)
    rw [rk,comap_rank f onto I i] at upper
    apply upper.trans
    apply Nat.add_le_add_left
    rw [←maxCosetDim_affineSubspace F H I];exact maxCosetDim_mono F H hi
  · have inc : (U.comap f.toAffineMap : Set G) ⊆ pull f S :=
      fun _ hz => (mem_pull _ _ _).mpr (hU (AffineSubspace.mem_comap.mp hz))
    have le := maxCosetDim_mono F G inc
    rwa [maxCosetDim_affineSubspace,comap_rank f onto U u,ur] at le

end Green51PeriodQuotients
#print axioms Green51PeriodQuotients.max_dimension_pull
