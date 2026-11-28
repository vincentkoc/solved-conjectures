import Mathlib

/-!
# The density-one-half endpoint for twofold sumsets

A missing sum translates the set onto its complement. All missing sums therefore belong
to a single coset of the translation stabilizer.
-/

open Finset
open scoped Pointwise

namespace Green50HalfDensity

local notation "K" => ZMod 2
private abbrev E (n : ℕ) := Fin n → K

/-- At or above density one half, the twofold sum contains a subspace of codimension at most one. -/
theorem half_density_kernel {n : ℕ} (A : Finset (Fin n → K)) (hA : 1/2 ≤ (A.dens : ℝ)) :
    ∃ l : Module.Dual K (Fin n → K), ∀ x, l x = 0 → x ∈ A + A := by
  classical
  have da : (A.dens : ℝ) = (A.card:ℝ) / Fintype.card (E n) := by simp [E,Finset.dens]
  rw [da, le_div_iff₀ (by exact_mod_cast Fintype.card_pos)] at hA
  have hn : Fintype.card (Fin n → K) ≤ 2*A.card := by exact_mod_cast (show (Fintype.card (E n):ℝ) ≤ 2*A.card by linarith)
  have double (x : E n) : x+x=0 := by
    funext j
    exact CharTwo.add_self_eq_zero (x j)
  have flip (t : E n) (ht : t ∉ A+A) (x : E n) : x+t ∈ A ↔ x ∉ A := by
    have sub : A.image (·+t) ⊆ Aᶜ := by
      intro y hy
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
      apply mem_compl.mpr
      intro h
      exact ht (mem_add.mpr ⟨z,hz,z+t,h,by rw [←add_assoc,double,zero_add]⟩)
    have eq := eq_of_subset_of_card_le sub (show Aᶜ.card ≤ _ by
      rw [card_compl,card_image_of_injective A (add_left_injective t)]; omega)
    constructor
    · intro hx
      exact mem_compl.mp (sub (mem_image.mpr ⟨x+t,hx,by rw [add_assoc,double,add_zero]⟩))
    · intro hx
      obtain ⟨y,hy,hyx⟩ := mem_image.mp (eq.symm ▸ (mem_compl.mpr hx))
      rw [← hyx,add_assoc,double,add_zero]
      exact hy
  by_cases hall : ∀ t : E n, t ∈ A+A
  · exact ⟨0,fun x _ => hall x⟩
  push Not at hall
  obtain ⟨t,ht⟩ := hall
  let H : Submodule K (E n) := {
    carrier := {z | ∀ x, x+z ∈ A ↔ x ∈ A}
    zero_mem' := by simp
    add_mem' := by
      intro z w hz hw x
      exact (add_assoc x z w) ▸ (hw (x+z)).trans (hz x)
    smul_mem' := by
      intro c z hz
      rcases (by decide : ∀ a : K, a=0 ∨ a=1) c with rfl|rfl
      · simp
      · simpa using hz }
  have htH : t ∉ H := by
    intro h
    have hsame := h (0:E n)
    have hflip := flip t ht (0:E n)
    tauto
  obtain ⟨l,hlt,hlH⟩ := Submodule.exists_dual_map_eq_bot_of_notMem htH inferInstance
  refine ⟨l,?_⟩
  · intro z hz
    by_contra hzmiss
    have hzt : z+t ∈ H := by
      intro x
      rw [←add_assoc,flip t ht,flip z hzmiss,not_not]
    have hlz : l z = 0 := hz
    have hzero : l (z+t) ∈ H.map l := Submodule.mem_map_of_mem hzt
    rw [hlH] at hzero
    change l (z+t) = 0 at hzero
    rw [map_add,hlz,zero_add] at hzero
    exact hlt hzero

/-- The kernel at half density has codimension at most one. -/
theorem half_density_subspace {n : ℕ} (A : Finset (Fin n → K)) (hA : 1/2 ≤ (A.dens : ℝ)) :
    ∃ W : Submodule K (Fin n → K), (W : Set (Fin n → K)) ⊆ ↑(A + A) ∧
      n ≤ Module.finrank K W + 1 := by
  obtain ⟨l,hl⟩ := half_density_kernel A hA
  refine ⟨l.ker,fun x hx => hl x hx,?_⟩
  have hdim := l.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hdim
  have hr := Submodule.finrank_le l.range
  rw [Module.finrank_self] at hr
  omega

#print axioms Green50HalfDensity.half_density_kernel

#print axioms Green50HalfDensity.half_density_subspace

end Green50HalfDensity
