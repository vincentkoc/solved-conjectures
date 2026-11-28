import Green50QuadraticGraphs

/-! # Twofold sums of function graphs with affine derivative images -/

open Finset
open scoped Pointwise
namespace Green52AffineDerivatives
local notation "K" => ZMod 2
variable {G : Type*} [AddCommGroup G] [Module K G]

private theorem twice (x : G) : x + x = 0 := by
  rw [← two_smul K,show (2:K)=0 by decide,zero_smul]

/-- Directions preserving a binary-valued function form a subspace. -/
private def periods (F : G → K) : Submodule K G where
  carrier := {a | ∀ x, F (x+a)=F x}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x
    rw [←add_assoc,hb,ha]
  smul_mem' := by
    intro c a ha
    rcases (show ∀ z : K, z=0 ∨ z=1 from by decide) c with rfl | rfl
    · simp
    · simpa using ha

/-- A single linear equation excludes every translation that flips a fixed Boolean function. -/
private theorem excludes_flips (F : G → K) (e : G) (he : ∀ x, F (x+e) = F x+1) :
    ∃ L : G →ₗ[K] K, ∀ a, L a = 0 → ¬ (∀ x, F (x+a) = F x+1) := by
  have he' : e ∉ periods F := by
    intro hp
    have hz : F ((0:G)+e) = F (0:G) := hp 0
    have hh := he 0
    rw [hz] at hh
    exact (show ∀ t : K, t ≠ t+1 from by decide) _ hh
  obtain ⟨L,hLe,hker⟩ := Submodule.exists_le_ker_of_notMem he'
  refine ⟨L,?_⟩
  intro a hLa hflip
  have hp : a+e ∈ periods F := by
    intro x
    rw [←add_assoc,he,hflip,add_assoc, twice (1:K),add_zero]
  have hzero : L (a+e)=0 := hker hp
  rw [map_add,hLa,zero_add] at hzero
  exact hLe hzero

variable {U V : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

private theorem scalar_direction (f : U → V) (l : Module.Dual K V) (hl : l ≠ 0) :
    ∃ L : Module.Dual K (U × V), ∀ a b, L (a,b) = 0 →
      ∃ x, l (f x + f (x+a)) = l b := by
  have hy : ∃ y, l y ≠ 0 := by
    by_contra! ha
    exact hl (LinearMap.ext fun x => ha x)
  obtain ⟨y,hy⟩ := hy
  have h1 : l y = 1 := (show ∀ z : K, z ≠ 0 → z = 1 from by decide) _ hy
  let F (p : U × V) := l (f p.1 + p.2)
  have flip (p : U × V) : F (p+(0,y)) = F p + 1 := by
    simp [F,h1,add_assoc]
  obtain ⟨L,hL⟩ := excludes_flips F (0,y) flip
  refine ⟨L,?_⟩
  intro a b hz
  by_contra! hnone
  apply hL (a,b) hz
  rintro ⟨x,v⟩
  change l (f (x+a) + (v+b)) = l (f x + v) + 1
  simp only [map_add]
  apply (show ∀ i j k t : K, i+j ≠ k → j+(t+k)=(i+t)+1 from by decide)
  simpa using hnone x

/-- All scalar projections of the derivative fibres contain the corresponding
projections of one common linear subspace of codimension at most |V|−1. -/
theorem projection_flat [Fintype U] [Fintype V] (f : U → V) :
    ∃ T : Submodule K (U × V),
      Module.finrank K (U × V) ≤ Module.finrank K T + (Fintype.card V-1) ∧
      ∀ w ∈ T, ∀ l : Module.Dual K V, ∃ x, l (f x+f (x+w.1)) = l w.2 := by
  classical
  let _ : Fintype (Module.Dual K V) := Fintype.ofInjective (fun l : Module.Dual K V => (l : V → K)) DFunLike.coe_injective
  let I := {l : Module.Dual K V // l ≠ 0}
  let _ : Fintype I := inferInstanceAs (Fintype {l : Module.Dual K V // l ≠ 0})
  choose L hL using fun l : I => scalar_direction f l.val l.property
  let P : (U × V) →ₗ[K] (I → K) := LinearMap.pi L
  refine ⟨P.ker,?_,?_⟩
  · have cardD : Fintype.card (Module.Dual K V) = Fintype.card V := by
      calc
        _ = Fintype.card K ^ Module.finrank K (Module.Dual K V) := Module.card_eq_pow_finrank
        _ = _ := by rw [Subspace.dual_finrank_eq]; exact Module.card_eq_pow_finrank.symm
    have ci : Fintype.card I = Fintype.card V - 1 := by
      dsimp [I]
      rw [Fintype.card_subtype_compl (· = (0:Module.Dual K V)),cardD]
      simp
    have hR := Submodule.finrank_le P.range
    rw [Module.finrank_pi,ci] at hR
    have hsum := P.finrank_range_add_finrank_ker
    omega
  · rintro ⟨a,b⟩ hw l
    by_cases hl : l=0
    · exact ⟨0,by simp [hl]⟩
    · exact hL ⟨l,hl⟩ a b (congrFun (show P (a,b)=0 from hw) ⟨l,hl⟩)

variable [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

/-- The twofold sum of a graph with affine derivative images contains a linear
space of codimension at most |V|−1, uniformly in the input dimension. -/
theorem twofold_of_affine_images (f : U → V)
    (h : ∀ a, ∃ W : Submodule K V, ∀ b,
      (∃ x, f x+f (x+a)=b) ↔ b-(f 0+f a) ∈ W) :
    ∃ T : Submodule K (U × V), (T:Set (U × V)) ⊆ ↑((2:ℕ) • Green50QuadraticGraphs.graph f) ∧
      Module.finrank K (U × V) ≤ Module.finrank K T + (Fintype.card V-1) := by
  obtain ⟨T,hd,hT⟩ := projection_flat f
  refine ⟨T,?_,hd⟩
  rintro ⟨a,b⟩ hw
  obtain ⟨W,hW⟩ := h a
  apply (Green50QuadraticGraphs.twofold_fibre _ _ _).mpr
  apply (hW b).mpr
  by_contra hbad
  obtain ⟨l,hne,hker⟩ := Submodule.exists_le_ker_of_notMem hbad
  obtain ⟨x,hx⟩ := hT (a,b) hw l
  have hz : l (f x + f (x+a) - (f 0+f a)) = 0 :=
    hker ((hW _).mp ⟨x,rfl⟩)
  rw [map_sub,hx,←map_sub] at hz
  exact hne hz

/-- Every binary quadratic function satisfies the affine-derivative criterion. -/
theorem twofold_quadratic (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x, f x+f (x+a)=B a x+(f 0+f a)) :
    ∃ T : Submodule K (U × V), (T:Set (U × V)) ⊆ ↑((2:ℕ) • Green50QuadraticGraphs.graph f) ∧
      Module.finrank K (U × V) ≤ Module.finrank K T + (Fintype.card V-1) := by
  apply twofold_of_affine_images f
  intro a
  refine ⟨(B a).range,?_⟩
  intro b
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,eq_sub_of_add_eq ((hf a x).symm.trans hx)⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,(hf a x).trans (add_eq_of_eq_sub hx)⟩

end Green52AffineDerivatives

#print axioms Green52AffineDerivatives.projection_flat
#print axioms Green52AffineDerivatives.twofold_of_affine_images
#print axioms Green52AffineDerivatives.twofold_quadratic
