import Green51SparseDimensions
import Green50BCH
open Finset Green50Sharp Green50Downsets Green51SparseDimensions
open scoped Classical Pointwise
namespace Green51AffineSeparation
local notation "F" => ZMod 2
variable {K : Type*} [Field K]

/-- The triple-error-correcting BCH graph over a binary field. -/
def graphPoint (x : K) : Fin 3 → K := Green50BCH.column 3 x

private theorem graph_coordinates (x : K) : graphPoint x = ![x,x^3,x^5] := by
  funext i
  fin_cases i <;> simp [graphPoint,Green50BCH.column]

private theorem graph_inj : Function.Injective (graphPoint (K:=K)) := by
  intro x y eq
  simpa [graph_coordinates] using congrFun eq 0

variable [CharP K 2] [Module F K]

omit [Module F K] in
private theorem fourth (x y : K) : (x+y)^4=x^4+y^4 := by
  rw [show 4=2*2 by decide,pow_mul,CharTwo.add_sq,CharTwo.add_sq]
  simp [←pow_mul]

private def derivative : K →ₗ[F] (Fin 3 → K) :=
  { toFun := fun x => ![0,x^2+x,x^4+x]
    map_add' := by
      intro x y; funext i
      fin_cases i <;> simp [CharTwo.add_sq,fourth] <;> abel
    map_smul' := by
      intro c x
      rcases (show ∀ u:F,u=0 ∨ u=1 from by decide) c with rfl|rfl <;> simp }

private theorem graph_translate (x : K) :
    graphPoint 1 + derivative x = graphPoint (x+1)+graphPoint x := by
  have two := CharTwo.two_eq_zero (R:=K)
  have cube : (x+1)^3+x^3=1+(x^2+x) := by
    rw [pow_succ (x+1) 2,CharTwo.add_sq,one_pow]
    linear_combination x^3 * two
  have fifth : (x+1)^5+x^5=1+(x^4+x) := by
    rw [pow_succ (x+1) 4,fourth,one_pow]
    linear_combination x^5 * two
  funext i
  fin_cases i <;> simp [graph_coordinates,derivative,cube,fifth,CharTwo.add_self_eq_zero,add_right_comm]

private theorem derivative_kernel :
    derivative.ker = Submodule.span F {(1:K)} := by
  apply le_antisymm
  · intro x hx
    have zero := congrFun ((LinearMap.mem_ker).mp hx) 1
    have h : x*x+x=0 := by simpa [derivative,pow_two] using zero
    have prod : x*(x+1)=0 := by simpa [mul_add] using h
    rcases mul_eq_zero.mp prod with left|right
    · rw [left]; exact Submodule.zero_mem _
    · have eq : x=1 := add_right_cancel (right.trans (ZModModule.add_self (1:K)).symm)
      rw [eq]; exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro x hx
    obtain rfl : x=1 := Set.mem_singleton_iff.mp hx
    apply LinearMap.mem_ker.mpr
    funext i; fin_cases i <;> simp [derivative,ZModModule.add_self]

/-- The graph of the three odd BCH powers has a translate of the derivative
range in its double, with affine dimension one less than the field degree. -/
theorem graph_derivative_flat [Fintype K] [FiniteDimensional F K] :
    ∃ (W : Submodule F (Fin 3 → K)) (p : Fin 3 → K),
      Module.finrank F W + 1 = Module.finrank F K ∧
      p +ᵥ (W : Set (Fin 3 → K)) ⊆ ↑((univ.image (graphPoint (K:=K)))+univ.image (graphPoint (K:=K))) := by
  classical
  refine ⟨derivative.range,graphPoint 1,?_,?_⟩
  · have eq := (derivative (K:=K)).finrank_range_add_finrank_ker
    rwa [derivative_kernel,finrank_span_singleton (one_ne_zero : (1:K)≠0)] at eq
  · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    change graphPoint 1 + derivative x∈_
    rw [graph_translate]
    exact add_mem_add (mem_image_of_mem _ (mem_univ _)) (mem_image_of_mem _ (mem_univ _))
omit [CharP K 2] [Module F K] in
/-- The graph has one label for every field element. -/
theorem graph_size [Fintype K] : (univ.image (graphPoint (K:=K))).card=Fintype.card K := by
  rw [card_image_of_injective _ graph_inj,card_univ]

/-- The same graph excludes linear three-spaces because any four- or six-point
relation would violate the BCH distance bound. -/
theorem graph_linear_avoidance [Fintype K] (large : 5≤Fintype.card K) :
    ¬∃ W : Submodule F (Fin 3 → K), Module.finrank F W=3 ∧
      ∀ w∈W,w∈univ.image (graphPoint (K:=K))+univ.image (graphPoint (K:=K)) := by
  classical
  let A := univ.image (graphPoint (K:=K))
  have size : A.card=Fintype.card K := graph_size
  intro flat
  obtain ⟨T,sub,number,zero⟩ := (linear_three_iff A (size ▸ large)).mp flat
  let U := T.erase 0
  have hU : U.Nonempty := by
    apply card_pos.mp
    by_cases h : (0:Fin 3 → K)∈T
    · have le := card_erase_add_one h
      change 0 < (T.erase 0).card; omega
    · change 0 < (T.erase 0).card; rw [erase_eq_of_notMem h]; omega
  have same (y : Fin 3 → K) (hy : y∈U) : graphPoint (y 0)=y := by
    obtain ⟨x,_,rfl⟩ := mem_image.mp (sub (mem_of_mem_erase hy))
    simp [graph_coordinates]
  let v (i : Fin U.card) : K := ((U.equivFin.symm i).val) 0
  have recover (i : Fin U.card) : graphPoint (v i)=(U.equivFin.symm i).val :=
    same _ (U.equivFin.symm i).property
  have inj : Function.Injective v := by
    intro i j eq
    exact U.equivFin.symm.injective (Subtype.ext ((recover i).symm.trans ((congrArg graphPoint eq).trans (recover j))))
  have nz (i : Fin U.card) : v i≠0 := by
    intro eq
    have z : graphPoint (v i)=0 := by rw [eq,graph_coordinates]; funext j; fin_cases j <;> simp
    exact (mem_erase.mp (U.equivFin.symm i).property).1 ((recover i).symm.trans z)
  have hle := card_le_card (erase_subset (0:Fin 3 → K) T)
  have impossible := Green50BCH.column_girth (t:=3) (card_pos.mpr hU) (show U.card≤6 by dsimp [U];omega) v inj nz
  apply impossible
  change (∑ i,graphPoint (v i))=0
  calc
    _ = ∑ i,(U.equivFin.symm i).val := sum_congr rfl fun i _ => recover i
    _ = ∑ i : U,i.val := U.equivFin.symm.sum_comp Subtype.val
    _ = ∑ i∈U,i := sum_coe_sort U id
    _ = 0 := by
      by_cases h : (0:Fin 3 → K)∈T
      · simpa only [U,id_eq,add_zero] using (sum_erase_add T id h).trans zero
      · simpa only [U,erase_eq_of_notMem h] using zero

end Green51AffineSeparation

#print axioms Green51AffineSeparation.graph_size
#print axioms Green51AffineSeparation.graph_derivative_flat
#print axioms Green51AffineSeparation.graph_linear_avoidance
