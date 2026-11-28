import Green51BCHThreshold
import Green51TwoAlternating

/-! # Retaining at most two tests of the seventh coordinate in even dimension -/

open Green50Downsets Green51BCH Green51BCHCompression Green51TwoAlternating
open scoped Pointwise
namespace Green51BCHExceptional
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K]
variable {H : Type*} [AddCommGroup H] [Module F H]

private def minorForm (l : K →ₗ[F] F) : LinearMap.BilinForm F K :=
  LinearMap.mk₂ F (fun x y => l (moore 1 x y))
    (fun x y z => by rw [moore_left,map_add])
    (fun r x y => by
      rcases (show ∀ i:F,i=0 ∨ i=1 from by decide) r with rfl|rfl <;> simp [moore_prod])
    (fun x y z => by rw [moore_right,map_add])
    (fun r x y => by
      rcases (show ∀ i:F,i=0 ∨ i=1 from by decide) r with rfl|rfl <;> simp [moore_prod])

/-- Two binary tests leave a flat of dimension `k+1` whenever at least `2*(k+1)` field coordinates are available. -/
theorem two_tests_floor [Finite K] (k : ℕ) (room : 2*(k+1) ≤ Module.finrank F K) (L : K →ₗ[F] H)
    (rank : Module.finrank F L.range≤2) :
    ∃ (p : Space K × H) (W : Submodule F (Space K × H)), Module.finrank F W=k+1 ∧
      p+ᵥ (W:Set _) ⊆ Set.range (lifted L)+Set.range (lifted L) := by
  obtain ⟨e,inj⟩ := finrank_le_iff_exists_linearMap.mp
    (show Module.finrank F L.range≤Module.finrank F (Cube 2) by simp [Cube];omega)
  let f := e.comp L.rangeRestrict
  let A (i : Fin 2) := minorForm ((LinearMap.proj i).comp f)
  have alt (i : Fin 2) : (A i).IsAlt := fun x => by
    change f (moore 1 x x) i=0
    simp [moore_alternating]
  let D := Submodule.span F {(1:K)}
  obtain ⟨complement,comp⟩ := D.exists_isCompl
  have rankX := Submodule.finrank_add_eq_of_isCompl comp
  have dD : Module.finrank F D=1 := finrank_span_singleton one_ne_zero
  obtain ⟨embed, injEmbed⟩ := finrank_le_iff_exists_linearMap.mp
    (show Module.finrank F (Cube (2*k+1)) ≤ Module.finrank F complement by simp [Cube]; omega)
  let inclusion := complement.subtype.comp embed
  let X := inclusion.range
  have rankSpace : Module.finrank F X = 2*k+1 := by
    rw [show X = inclusion.range from rfl, inclusion.finrank_range_of_inj
      (complement.subtype_injective.comp injEmbed)]
    simp [Cube]
  have inComplement : X ≤ complement := by
    rintro _ ⟨x, rfl⟩
    exact (embed x).property
  obtain ⟨Y,sz,iso₀,iso₁⟩ := simultaneous F k ((A 0).restrict X) ((A 1).restrict X)
    (fun x => alt 0 x.val) (fun x => alt 1 x.val) rankSpace
  let S := Y.map X.subtype
  have sr : Module.finrank F S=k+1 := (X.finrank_map_subtype_eq Y).trans sz
  have outside : (1:K)∉S := by
    rintro ⟨x,_,hx⟩
    have x1 : (1:K)∈X := hx ▸ x.property
    have d1 : (1:K)∈D := Submodule.subset_span (Set.mem_singleton _)
    exact one_ne_zero ((Submodule.disjoint_def.mp comp.disjoint) 1 d1 (inComplement x1))
  let U := S ⊔ D
  have ur : Module.finrank F U=(k+1)+1 := by rw [show U=S ⊔ Submodule.span F {1} from rfl,extend_dim S 1 outside,sr]
  have vertical (i : Fin 2) (x : K) : A i 1 x=0 := by
    change f (moore 1 1 x) i=0
    simp [moore_prod,CharTwo.add_self_eq_zero]
  have both (i : Fin 2) (x : K) (hx : x∈S) (y : K) (hy : y∈S) : A i x y=0 := by
    obtain ⟨v,hv,rfl⟩ := hx
    obtain ⟨w,hw,rfl⟩ := hy
    fin_cases i
    · exact iso₀ v hv w hw
    · exact iso₁ v hv w hw
  have onU (i : Fin 2) := extend_isotropic (A i) (alt i) S 1
    (fun x _ => vertical i x) (both i)
  have kill (x) (hx : x∈U) (y) (hy : y∈U) : L (moore 1 x y)=0 := by
    have z : f (moore 1 x y)=0 := funext (fun i => onU i x hx y hy)
    exact congrArg Subtype.val ((e.map_eq_zero_iff inj).mp z)
  have mem : (1:K)∈U := (show D≤U from le_sup_right) (Submodule.subset_span (Set.mem_singleton _))
  obtain ⟨p,W,h,flat⟩ := produces_flat L U 1 mem one_ne_zero kill
  exact ⟨p,W,by omega,flat⟩

/-- Two retained linear tests on the seventh power always leave a half-dimensional flat in even field dimension. -/
theorem two_tests_in_even [Finite K] (k : ℕ) (dim : Module.finrank F K=2*(k+1)) (L : K →ₗ[F] H)
    (rank : Module.finrank F L.range≤2) :
    ∃ (p : Space K × H) (W : Submodule F (Space K × H)), Module.finrank F W=k+1 ∧
      p+ᵥ (W:Set _) ⊆ Set.range (lifted L)+Set.range (lifted L) :=
  two_tests_floor k (le_of_eq dim.symm) L rank

/-- The dimension-six specialization expressed by the number of discarded coordinates. -/
theorem four_forces_flat [Finite K] (dim : Module.finrank F K=6) (L : K →ₗ[F] H)
    (large : 4≤Module.finrank F L.ker) :
    ∃ (p : Space K × H) (W : Submodule F (Space K × H)), Module.finrank F W=3 ∧
      p+ᵥ (W:Set _) ⊆ Set.range (lifted L)+Set.range (lifted L) := by
  have rank := L.finrank_range_add_finrank_ker
  exact two_tests_in_even 2 dim L (by omega)

end Green51BCHExceptional
#print axioms Green51BCHExceptional.two_tests_floor
#print axioms Green51BCHExceptional.two_tests_in_even
#print axioms Green51BCHExceptional.four_forces_flat
