import Mathlib

/-! # Repairing sign assignments on an affine parity slice -/

open Finset
open scoped Pointwise Classical
namespace Green53ParityThreshold

/-- Field of the Boolean cube. -/
abbrev F := ZMod 2
/-- The image of a coordinate subspace has a spanning collection of at most
`finrank F V` coordinate images. These same coordinates suffice for every correction. -/
theorem sparse_correction {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : (J → F) →ₗ[F] V) (U : Finset J) :
    ∃ T ⊆ U, T.card ≤ Module.finrank F V ∧
      ∀ x : J → F, (∀ j, j∉U → x j=0) →
        ∃ y : J → F, (∀ j,j∉T → y j=0) ∧ Q y=Q x := by
  classical
  let col (j : J) := Q (Pi.single j 1)
  let S := col '' (U : Set J)
  obtain ⟨B,sub,hcard,sp,_⟩ := Submodule.exists_finset_span_eq_linearIndepOn F S
  have hit (v : B) : ∃ j∈U,col j=v.val := sub v.property
  choose pre mempre idpre using hit
  let T := univ.image pre
  have tb : T.card ≤ B.card := (card_image_le).trans_eq (by simp)
  refine ⟨T,?_,tb.trans (hcard.le.trans (Submodule.finrank_le _)),?_⟩
  · intro j hj
    obtain ⟨v,_,rfl⟩ := mem_image.mp hj; exact mempre v
  · intro x xs
    have decomp : ∑ j, x j • Pi.single j (1:F) = x := by
      funext j; simp [Finset.sum_apply,Pi.single_apply]
    have ins : Q x∈Submodule.span F S := by
      rw [←decomp,map_sum]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      rw [map_smul]
      by_cases jU : j∈U
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,jU,rfl⟩)
      · simp [xs j jU]
    have br : Set.range (fun v : B => v.val) = (B : Set V) := by ext v; simp
    have hmem : Q x∈Submodule.span F (Set.range (fun v : B => v.val)) := by
      simpa only [br,sp] using ins
    obtain ⟨a,formula⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmem
    let y := ∑ v : B,a v • (Pi.single (pre v) (1:F) : J → F)
    refine ⟨y,?_,?_⟩
    · intro j no
      have diff (v : B) : j ≠ pre v := fun eq => no (mem_image.mpr ⟨v,mem_univ _,eq.symm⟩)
      simp [y,Finset.sum_apply,diff]
    · dsimp only [y]; rw [map_sum]
      simpa only [map_smul,←idpre,col] using formula

/-- Repair both endpoints by the same set of at most `finrank F V` free flips. -/
theorem correct_pair {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : (J → F) →ₗ[F] V) (t : Finset J) (x₀ x z : J → F)
    (pinned : ∀ j∈t,x j=x₀ j) (dir : Q z=0) :
    ∃ (T : Finset J) (v : J → F), Disjoint t T ∧ T.card ≤ Module.finrank F V ∧
      (∀ j,j∉T → v j=0) ∧ Q (x+v)=Q x₀ ∧ Q (x+v+z)=Q x₀ := by
  classical
  let U := univ\t
  obtain ⟨T,sub,card,cover⟩ := sparse_correction Q U
  have supp (j : J) (jn : j∉U) : (x₀-x) j=0 := by
    have jt : j∈t := by simpa [U] using jn
    simp [pinned j jt]
  obtain ⟨v,hv,eq⟩ := cover (x₀-x) supp
  have hit : Q (x+v)=Q x₀ := by rw [map_add,eq,map_sub]; abel
  refine ⟨T,v,?_,card,hv,hit,?_⟩
  · exact Finset.disjoint_left.mpr (by intro j ht hT; exact (mem_sdiff.mp (sub hT)).2 ht)
  · rw [map_add,hit,dir,add_zero]

/-- The positive sign corresponds to zero in the Boolean cube. -/
def decode : Bool ≃ F where
  toFun b := if b then 0 else 1
  invFun a := decide (a=0)
  left_inv b := by cases b <;> decide
  right_inv := by decide
/-- Identify a Boolean signing with its vector over `ZMod 2`. -/
def cube {J : Type*} : (J → Bool) ≃ (J → F) := Equiv.piCongrRight (fun _ => decode)

/-- A nonempty parity slice occupies at least 2^(−dim V) of the cube. -/
theorem slice_size {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : (J → F) →ₗ[F] V) (x₀ : J → F) :
    2^(Fintype.card J) ≤ 2^(Module.finrank F V)*
      (univ.filter (fun x : J → Bool => Q (cube x)=Q x₀)).card := by
  classical
  let G := univ.filter (fun x : J → Bool => Q (cube x)=Q x₀)
  let E : Q.ker ≃ G := {
    toFun := fun u => ⟨cube.symm (x₀+u.val), mem_filter.mpr ⟨mem_univ _,by
      rw [Equiv.apply_symm_apply,map_add,LinearMap.mem_ker.mp u.property,add_zero]⟩⟩
    invFun := fun x => ⟨cube x.val-x₀, by
      rw [LinearMap.mem_ker,map_sub,(mem_filter.mp x.property).2,sub_self]⟩
    left_inv := fun u => by ext j; simp
    right_inv := fun x => by apply Subtype.ext; simp }
  have g : G.card=2^(Module.finrank F Q.ker) := by
    calc
      _ = Fintype.card Q.ker := by rw [Fintype.card_congr E,Fintype.card_coe]
      _ = _ := by simpa only [ZMod.card] using (Module.card_eq_pow_finrank (K:=F) (V:=Q.ker))
  change _ ≤ 2^_*G.card
  rw [g,←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have dim := Q.finrank_range_add_finrank_ker
  have bound := Q.range.finrank_le
  simpa only [Module.finrank_fintype_fun_eq_card] using dim.symm.le.trans (Nat.add_le_add_right bound _)

end Green53ParityThreshold

#print axioms Green53ParityThreshold.sparse_correction
#print axioms Green53ParityThreshold.correct_pair
#print axioms Green53ParityThreshold.slice_size
