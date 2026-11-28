import Green51SimplexSection

/-! # Permutation equivalence of binary simplex codes -/

open Finset Green50Downsets Green50Sharp
open scoped Classical
namespace Green51SimplexSection
local notation "F" => ZMod 2

private theorem index_columns {U : Type*} [AddCommGroup U] [Module F U] [Fintype U]
    {n : ℕ} (col : Fin n → Module.Dual F U)
    (counts : ∀ f : Module.Dual F U, (univ.filter (fun i => col i=f)).card =
      if f=0 then 0 else 1) :
    ∃ e : Fin n ≃ {f : Module.Dual F U // f≠0}, ∀ i, (e i).val=col i := by
  classical
  have non (i) : col i≠0 := by
    intro z
    have empty : univ.filter (fun i => col i=0) = ∅ := card_eq_zero.mp (by simpa using counts 0)
    have h : i∈univ.filter (fun i => col i=0) := mem_filter.mpr ⟨mem_univ _,z⟩
    rw [empty] at h
    exact notMem_empty i h
  let g (i : Fin n) : {f : Module.Dual F U // f≠0} := ⟨col i,non i⟩
  have unique (f : {f : Module.Dual F U // f≠0}) : ∃! i, g i=f := by
    have one : (univ.filter (fun i => col i=f.val)).card = 1 := by simpa [f.property] using counts f.val
    obtain ⟨i, hi, un⟩ := card_eq_one_iff_existsUnique.mp one
    refine ⟨i, Subtype.ext (mem_filter.mp hi).2, ?_⟩
    intro j hj
    exact un j (mem_filter.mpr ⟨mem_univ _,congrArg Subtype.val hj⟩)
  exact ⟨Equiv.ofBijective g
    ⟨fun i j eq => (unique (g j)).unique eq rfl,fun f => (unique f).exists⟩, fun _ => rfl⟩

/-- If both binary codes attain the simplex bound in the same length,
one permutation of coordinates identifies their full word spaces. -/
theorem simplex_permutation {n : ℕ} (C D : Submodule F (Cube n))
    (cr : n+1 ≤ Fintype.card C) (dr : n+1 ≤ Fintype.card D)
    (cd : ∀ x:C, x≠0 → n+1≤2*(supp x.val).card)
    (dd : ∀ y:D, y≠0 → n+1≤2*(supp y.val).card) :
    ∃ σ : Equiv.Perm (Fin n), ∀ z : Cube n, z∈C ↔ (fun i => z (σ i))∈D := by
  classical
  let c (i:Fin n) : Module.Dual F C := (LinearMap.proj i).comp C.subtype
  let d (i:Fin n) : Module.Dual F D := (LinearMap.proj i).comp D.subtype
  obtain ⟨cs, multC⟩ := simplex_columns c cr cd
  obtain ⟨ds, _⟩ := simplex_columns d dr dd
  have dims : Module.finrank F C = Module.finrank F D := by
    have sizes := cs.trans ds.symm
    have csize : Fintype.card C=2^Module.finrank F C := by rw [Module.card_eq_pow_finrank (K:=F),ZMod.card]
    have dsize : Fintype.card D=2^Module.finrank F D := by rw [Module.card_eq_pow_finrank (K:=F),ZMod.card]
    rw [csize,dsize] at sizes
    exact Nat.pow_right_injective (by decide : 1 < 2) sizes
  let e : C ≃ₗ[F] D := LinearEquiv.ofFinrankEq C D dims
  let back (i:Fin n) := (d i).comp e.toLinearMap
  have db (x:C) (hx:x≠0) : n+1 ≤ 2*(univ.filter (fun i => back i x≠0)).card :=
    dd (e x) (fun h => hx (e.injective (h.trans (map_zero e).symm)))
  obtain ⟨_,multD⟩ := simplex_columns back cr db
  obtain ⟨u,hu⟩ := index_columns c multC
  obtain ⟨v,hv⟩ := index_columns back multD
  let σ := v.trans u.symm
  have compat (i:Fin n) : c (σ i) = back i := by
    rw [←hu,←hv]
    exact congrArg Subtype.val (u.apply_symm_apply (v i))
  refine ⟨σ,fun z => ?_⟩
  constructor
  · intro h
    have eq : (fun i => z (σ i)) = (e ⟨z,h⟩).val := by
      funext i
      exact LinearMap.congr_fun (compat i) ⟨z,h⟩
    exact eq ▸ (e ⟨z,h⟩).property
  · intro h
    obtain ⟨x,hx⟩ := e.surjective ⟨_,h⟩
    have eq : x.val=z := by
      funext j
      obtain ⟨i,rfl⟩ := σ.surjective j
      have same := LinearMap.congr_fun (compat i) x
      change x.val (σ i) = (e x).val i at same
      rw [hx] at same
      exact same
    exact eq ▸ x.property

end Green51SimplexSection
#print axioms Green51SimplexSection.simplex_permutation
