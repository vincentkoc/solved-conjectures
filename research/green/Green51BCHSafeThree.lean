import Green51BCHCandidateCollision

/-! # A three-dimensional kernel that excludes affine three-spaces in dimension six -/

open Green50Downsets Green51BCH Green51BCHCompression Green51BCHOptimality Green51BCHFlags
open scoped Pointwise
namespace Green51BCHExceptional
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K]

private theorem uncovered [Fintype K] (dim : Module.finrank F K=6) :
    ∃ S : Planes K, S.val∉Set.range (candidateMap (K:=K)) := by
  classical
  let _ := Fintype.ofFinite (Planes (TraceSpace K))
  let f := candidateMap (K:=K)
  let _ := Fintype.ofFinite (Set.range f)
  have nr : Fintype.card (NinthRoots K)≤9 := by
    change Fintype.card {h:Kˣ // h^9=1}≤9
    rw [Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le (by decide : 0<9)
  have rank := (artinSchreier (K:=K)).finrank_range_add_finrank_ker
  rw [artinSchreier_ker,finrank_span_singleton one_ne_zero,dim] at rank
  change Module.finrank F (TraceSpace K)+1=6 at rank
  have re : Module.finrank F (TraceSpace K)=5 := by omega
  have szE := planes_card (TraceSpace K) (by omega)
  rw [re] at szE
  have nE : Fintype.card (Planes (TraceSpace K))=155 := by
    rw [Nat.card_eq_fintype_card] at szE
    have q : (∏ i:Fin 3,(2^5-2^i.val : ℕ))=26040 := by decide
    omega
  have szK := planes_card K (by omega)
  rw [dim] at szK
  have nK : Nat.card (Planes K)=1395 := by
    have q : (∏ i:Fin 3,(2^6-2^i.val : ℕ))=234360 := by decide
    omega
  have noninj : ¬ Function.Injective (Set.rangeFactorization f) := fun h =>
    candidate_collision dim (fun x y eq => h (Subtype.ext eq))
  have lt := Fintype.card_lt_of_surjective_not_injective _ Set.rangeFactorization_surjective noninj
  rw [Fintype.card_prod,nE] at lt
  by_contra! covered
  let j (S : Planes K) : Set.range f := ⟨S.val,covered S⟩
  have le := Nat.card_le_card_of_injective j (fun x y eq => Subtype.ext (congrArg (fun v : Set.range f => v.val) eq))
  rw [nK,Nat.card_eq_fintype_card] at le
  omega

/-- Some projection with a three-dimensional kernel still excludes every affine
three-space from the doubled curve over the field of 64 elements. -/
theorem three_can_avoid [Fintype K] (dim : Module.finrank F K=6) :
    ∃ S : Planes K, ∀ (p : Space K × (K ⧸ S.val)) (W : Submodule F (Space K × (K ⧸ S.val))),
      p+ᵥ (W:Set _) ⊆ Set.range (lifted S.val.mkQ)+Set.range (lifted S.val.mkQ) →
      Module.finrank F W≤2 := by
  obtain ⟨S,miss⟩ := uncovered dim
  refine ⟨S,fun p W inside => ?_⟩
  by_contra! big
  exact miss (kernel_in_candidates dim S p W inside big)

end Green51BCHExceptional
#print axioms Green51BCHExceptional.three_can_avoid
