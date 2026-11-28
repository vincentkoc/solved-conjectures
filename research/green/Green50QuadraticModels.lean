import Green50QuadraticBogolyubov
import Green50Sharp

/-! # Hamming balls obstruct quadratic graph selection at the density bound. -/

open scoped Pointwise
namespace Green50QuadraticModels
open Green50Sharp Green50QuadraticBogolyubov
local notation "F₂" => ZMod 2

/-- In unbounded dimensions some balls force every quadratic graph in their twofold
sumset to use more output dimensions than the indicated logarithm. -/
theorem large_ball_obstruction {c : ℝ} (hc : 1 < c) (hroot : 2*c⁻¹-1 < c⁻¹^10) (N : ℕ) :
    ∃ n ≥ N, ∃ k, ∀ (U V : Submodule F₂ (Fin n → F₂)), IsCompl U V →
      ∀ (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V),
        Green50Graphs.graph U V f ⊆ ball n k + ball n k →
        (∀ a x, f x + f (x+a) = B a x + (f 0+f a)) →
        Real.logb c (1/((ball n k).dens:ℝ)) < (Module.finrank F₂ V : ℝ) := by
  obtain ⟨n,hn,k,hbad⟩ := large_ball_counterexamples (r := 10) hc hroot N
  refine ⟨n,hn,k,?_⟩
  intro U V huv f B hg hf
  obtain ⟨W,t,hw,hd⟩ := tenfold_quadratic_linear (ball n k) U V huv f B hg hf
  have hh := hbad W t hw
  rw [Module.finrank_pi,Fintype.card_fin] at hd
  have he : (n:ℝ) ≤ (Module.finrank F₂ W:ℝ) + (Module.finrank F₂ V:ℝ) := by exact_mod_cast hd
  linarith

end Green50QuadraticModels

#print axioms Green50QuadraticModels.large_ball_obstruction
