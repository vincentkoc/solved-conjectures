import Green51BracketProducts
import Green51BCHThreshold

/-! # Affine dimensions in a projected binary BCH double -/

open Green51BCHCompression Green51BCHOptimality Green51BCH
open scoped Pointwise
namespace Green51BracketRank
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

/-- Normalize the first coordinate of a flat to a bracket-isotropic subspace
of the Artin–Schreier image. -/
theorem trace_space_of_flat {H : Type*} [AddCommGroup H] [Module F H]
    (L : K →ₗ[F] H) (p : Space K × H) (W : Submodule F (Space K × H))
    (inside : p+ᵥ (W:Set _) ⊆ Set.range (lifted L)+Set.range (lifted L))
    (big : 3≤Module.finrank F W) :
    ∃ t : K, t≠0 ∧ ∃ A : Submodule F K, Module.finrank F A=Module.finrank F W ∧
      A≤(artinSchreier (K:=K)).range ∧ ∀ x∈A,∀ y∈A,L (t^7*bracket x y)=0 := by
  obtain ⟨t,U,nt,ht,sz,kill⟩ := input_of_flat L p W inside big
  let M := artinSchreier (K:=K)
  let k := M.comp (LinearMap.mulLeft F t⁻¹)
  have line : k.ker=Submodule.span F {t} := by
    apply le_antisymm
    · intro x hx
      change (t⁻¹*x)^2+t⁻¹*x=0 at hx
      have eq : t⁻¹*x*(t⁻¹*x+1)=0 := by linear_combination hx
      rcases mul_eq_zero.mp eq with z|z
      · exact ((mul_eq_zero.mp z).resolve_left (inv_ne_zero nt)) ▸ Submodule.zero_mem _
      · have one := CharTwo.add_eq_zero.mp z
        have eqx : x=t := by calc
          x=t*(t⁻¹*x) := by field_simp
          _=t := by rw [one,mul_one]
        rw [eqx]
        exact Submodule.subset_span (Set.mem_singleton _)
    · apply Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
      change (t⁻¹*t)^2+t⁻¹*t=0
      rw [inv_mul_cancel₀ nt,one_pow,CharTwo.add_self_eq_zero]
  let A := U.map k
  have rank := Green51QuadraticFlats.map_rank k U (by rw [line];exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ht))
  rw [line,finrank_span_singleton nt,sz] at rank
  change Module.finrank F A+1=Module.finrank F W+1 at rank
  refine ⟨t,nt,A,Nat.add_right_cancel rank,?_,?_⟩
  · rintro _ ⟨a,_,rfl⟩
    exact ⟨t⁻¹*a,rfl⟩
  · rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    have eq : t^7*bracket (k b) (k c)=moore t b c := by
      rw [moore_bracket]
      change t^7*bracket ((t⁻¹*b)^2+t⁻¹*b) ((t⁻¹*c)^2+t⁻¹*c)=_
      unfold bracket;field_simp
    rw [eq]
    exact kill b hb c hc

/-- A flat of dimension at least three in a projected BCH double requires
at least that many discarded seventh-coordinate dimensions. -/
theorem dim_le_kernel {H : Type*} [AddCommGroup H] [Module F H]
    (L : K →ₗ[F] H) (p : Space K × H) (W : Submodule F (Space K × H))
    (inside : p+ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L))
    (big : 3≤Module.finrank F W) : Module.finrank F W≤Module.finrank F L.ker := by
  obtain ⟨t,nt,A,dim,_,kill⟩ := trace_space_of_flat L p W inside big
  let f := LinearMap.mulLeft F (t^7)
  let S := L.ker.comap f
  have inj : Function.Injective f := fun _ _ h => mul_left_cancel₀ (pow_ne_zero _ nt) h
  have eq := (S.equivMapOfInjective f inj).finrank_eq
  have le : S.map f≤L.ker := Submodule.map_comap_le _ _
  have b := bracket_rank A S (by omega) (fun x hx y hy => kill x hx y hy)
  exact dim ▸ (b.trans (eq.trans_le (Submodule.finrank_mono le)))

end Green51BracketRank
#print axioms Green51BracketRank.trace_space_of_flat
#print axioms Green51BracketRank.dim_le_kernel
