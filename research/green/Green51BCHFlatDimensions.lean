import Green51BracketProducts
import Green51BCHThreshold

/-! # Affine dimensions in a projected binary BCH double -/

open Green51BCHCompression Green51BCH
open scoped Pointwise
namespace Green51BracketRank
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K]

private def pairTransform (t : K) : K →ₗ[F] K where
  toFun x := x*(x+t)
  map_add' x y := by ring_nf;reduce_mod_char!
  map_smul' r y := by
    rcases (show ∀ i:F,i=0 ∨ i=1 from by decide) r with rfl|rfl <;> simp

private theorem pair_ker (t : K) : (pairTransform t).ker=Submodule.span F {t} := by
  apply le_antisymm
  · intro x hx
    rcases mul_eq_zero.mp (show x*(x+t)=0 from hx) with eq|eq
    · exact eq ▸ Submodule.zero_mem _
    · rw [CharTwo.add_eq_zero.mp eq]
      exact Submodule.subset_span (Set.mem_singleton _)
  · apply Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
    change t*(t+t)=0
    rw [CharTwo.add_self_eq_zero,mul_zero]

/-- A flat of dimension at least three in a projected BCH double requires
at least that many discarded seventh-coordinate dimensions. -/
theorem dim_le_kernel [Fintype K] {H : Type*} [AddCommGroup H] [Module F H]
    (L : K →ₗ[F] H) (p : Space K × H) (W : Submodule F (Space K × H))
    (inside : p+ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L))
    (big : 3≤Module.finrank F W) : Module.finrank F W≤Module.finrank F L.ker := by
  obtain ⟨t,U,nt,ht,sz,kill⟩ := input_of_flat L p W inside big
  let A := U.map (pairTransform t)
  have line : (pairTransform t).ker≤U := by rw [pair_ker t];exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ht)
  have rank := Green51QuadraticFlats.map_rank (pairTransform t) U line
  rw [pair_ker t,finrank_span_singleton nt,sz] at rank
  have dimA : Module.finrank F A=Module.finrank F W := Nat.add_right_cancel rank
  let f := LinearMap.mulLeft F t
  let S := L.ker.comap f
  have inj : Function.Injective f := fun _ _ h => mul_left_cancel₀ nt h
  have eq := (S.equivMapOfInjective f inj).finrank_eq
  have le : S.map f≤L.ker := Submodule.map_comap_le _ _
  have b := bracket_rank A S (by omega) (by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    change L (t*bracket (b*(b+t)) (c*(c+t)))=0
    rw [←moore_bracket]
    exact kill b hb c hc)
  exact dimA ▸ (b.trans (eq.trans_le (Submodule.finrank_mono le)))

end Green51BracketRank
#print axioms Green51BracketRank.dim_le_kernel