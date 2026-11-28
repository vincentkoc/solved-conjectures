import Mathlib

/-! # Full function graphs in binary sumsets

A maximal subspace on which quotient projection is injective on A yields a full graph in A + A.
See `FUNCTION-GRAPH-REDUCTION.md` for the implications for Green 50.
-/

open Finset
open scoped Pointwise
namespace Green50Graphs
variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
private theorem twice (x : G) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul]

/-- A maximal kernel that separates A maps its twofold sumset onto the quotient. -/
theorem quotient_model (A : Finset G) (hne : A.Nonempty) :
    ∃ V : Submodule (ZMod 2) G,
      (∀ z ∈ A + A, z ∈ V → z = 0) ∧
      (∀ x : G, ∃ z ∈ A + A, x + z ∈ V) ∧
      A.card * Nat.card V ≤ Fintype.card G := by
  classical
  let good (V : Submodule (ZMod 2) G) := ∀ z ∈ A + A, z ∈ V → z = 0
  let S := univ.filter good
  have hbot : (⊥ : Submodule (ZMod 2) G) ∈ S :=
    mem_filter.mpr ⟨mem_univ _, fun _ _ h => by simpa using h⟩
  obtain ⟨V, hV, hmax⟩ := exists_max_image S (fun W => Module.finrank (ZMod 2) W) ⟨_, hbot⟩
  have sepV := (mem_filter.mp hV).2
  have hzero : 0 ∈ A + A := by
    obtain ⟨a, ha⟩ := hne
    exact twice a ▸ add_mem_add ha ha
  refine ⟨V, sepV, ?_, ?_⟩
  · intro x
    by_contra! hn
    have hx : x ∉ V := by simpa using hn 0 hzero
    let W := V ⊔ Submodule.span (ZMod 2) {x}
    have bigger : V < W := lt_of_le_of_ne le_sup_left (fun he => hx (he ▸
      (show x ∈ W from (le_sup_right : Submodule.span (ZMod 2) {x} ≤ W)
        (Submodule.mem_span_singleton_self x))))
    have hW : W ∈ S := by
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      intro z hz hw
      obtain ⟨v, hv, y, hy, he⟩ := Submodule.mem_sup.mp hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) c with rfl | rfl
      · simp only [zero_smul, add_zero] at he
        exact sepV z hz (he ▸ hv)
      · simp only [one_smul] at he
        exfalso
        apply hn z hz
        rw [← he, add_left_comm, twice, add_zero]
        exact hv
    exact (Submodule.finrank_lt_finrank_of_lt bigger).not_ge (hmax W hW)
  · let f (p : A × V) : G := p.1.val + p.2.val
    have inj : Function.Injective f := by
      intro ⟨a, u⟩ ⟨b, v⟩ h
      change a.val + u.val = b.val + v.val at h
      have hs : a.val + b.val = u.val + v.val := by
        calc
          _ = (a.val + u.val) + (b.val + u.val) := by rw [add_add_add_comm, twice, add_zero]
          _ = _ := by rw [h, add_add_add_comm, twice, zero_add, add_comm]
      have hab := sepV _ (add_mem_add a.property b.property) (hs ▸ V.add_mem u.property v.property)
      have he : a.val = b.val := by
        calc
          _ = (a.val + b.val) + b.val := by rw [add_assoc, twice, add_zero]
          _ = _ := by rw [hab, zero_add]
      rw [he] at h
      exact Prod.ext (Subtype.ext he) (Subtype.ext (add_left_cancel h))
    rw [Nat.card_eq_fintype_card]
    simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective f inj


/-- A full function graph over complementary binary subspaces, embedded by addition. -/
noncomputable def graph (U V : Submodule (ZMod 2) G) (f : U → V) : Finset G := by
  classical
  exact univ.image (fun u : U => u.val + (f u).val)

/-- A graph over complementary summands has one point per domain element. -/
theorem graph_card (U V : Submodule (ZMod 2) G) (h : IsCompl U V) (f : U → V) :
    (graph U V f).card = Nat.card U := by
  classical
  have hj : Function.Injective (fun u : U => u.val + (f u).val) := by
    intro u u' he
    have eq : U.prodEquivOfIsCompl V h (u, f u) = U.prodEquivOfIsCompl V h (u', f u') := he
    exact congrArg Prod.fst ((U.prodEquivOfIsCompl V h).injective eq)
  simp [graph, card_image_of_injective _ hj, Nat.card_eq_fintype_card]

/-- The twofold sumset contains a graph at least as dense as the original family. -/
theorem graph_in_twofold (A : Finset G) (hne : A.Nonempty) :
    ∃ (U V : Submodule (ZMod 2) G) (_ : IsCompl U V) (f : U → V),
      graph U V f ⊆ A + A ∧ A.card * Nat.card V ≤ Fintype.card G := by
  classical
  obtain ⟨V, _, covers, hs⟩ := quotient_model A hne
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl V
  choose g hgf hV using fun (u : U) => covers u.val
  let f (u : U) : V := ⟨u.val + g u, hV u⟩
  refine ⟨U, V, hU.symm, f, ?_, hs⟩
  intro z hz
  obtain ⟨u, _, rfl⟩ := mem_image.mp hz
  change u.val + (u.val + g u) ∈ A + A
  simpa only [← add_assoc, twice, zero_add] using hgf u

abbrev Cube (n : ℕ) := Fin n → ZMod 2

/-- The Green 50 conclusion for a specified summand count and coefficient. -/
def SetBound (k : ℕ) (C : ℝ) : Prop :=
  ∀ n (A : Finset (Cube n)), A.Nonempty →
    ∃ (W : Submodule (ZMod 2) (Cube n)) (v : Cube n),
      v +ᵥ (W : Set (Cube n)) ⊆ (↑(k • A) : Set (Cube n)) ∧
      (n : ℝ) - C * Real.logb 2 (1 / (A.dens : ℝ)) ≤ Module.finrank (ZMod 2) W

/-- The corresponding bound for full graphs, with output dimension as the density cost. -/
def GraphBound (k : ℕ) (C : ℝ) : Prop :=
  ∀ n (U V : Submodule (ZMod 2) (Cube n)), IsCompl U V → ∀ f : U → V,
    ∃ (W : Submodule (ZMod 2) (Cube n)) (v : Cube n),
      v +ᵥ (W : Set (Cube n)) ⊆ (↑(k • graph U V f) : Set (Cube n)) ∧
      (n : ℝ) - C * Module.finrank (ZMod 2) V ≤ Module.finrank (ZMod 2) W

theorem graph_to_set {k : ℕ} {C : ℝ} (hC : 0 ≤ C) (h : GraphBound k C) : SetBound (2 * k) C := by
  intro n A hne
  obtain ⟨U, V, hUV, f, hs, hsize⟩ := graph_in_twofold A hne
  obtain ⟨W, v, contained, dim⟩ := h n U V hUV f
  refine ⟨W, v, ?_, ?_⟩
  · intro y hy
    have hh := nsmul_subset_nsmul_left (n := k) hs (contained hy)
    change y ∈ (2 * k) • A
    simpa only [← two_nsmul, ← mul_smul, Nat.mul_comm k 2] using hh
  · classical
    have hdens : (A.dens : ℝ) = (A.card : ℝ) / 2 ^ n := by simp [Finset.dens, Cube, Fintype.card_pi]
    have ha : (0 : ℝ) < A.card := by exact_mod_cast card_pos.mpr hne
    have h₀ : (A.card : ℝ) * 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ n := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card] at hsize
      simpa [Cube, Fintype.card_pi] using (show (A.card : ℝ) * (2 : ℝ) ^ Module.finrank (ZMod 2) V ≤
        (Fintype.card (Cube n) : ℝ) by exact_mod_cast hsize)
    have hd : (Module.finrank (ZMod 2) V : ℝ) ≤ Real.logb 2 (1 / (A.dens : ℝ)) := by
      rw [hdens, one_div_div, Real.le_logb_iff_rpow_le (by norm_num) (div_pos (by positivity) ha),
        Real.rpow_natCast, le_div_iff₀ ha]
      linarith
    linarith [mul_le_mul_of_nonneg_left hd hC]

theorem set_to_graph {k : ℕ} {C : ℝ} (h : SetBound k C) : GraphBound k C := by
  classical
  intro n U V hUV f
  have hne : (graph U V f).Nonempty :=
    ⟨(0 : U).val + (f 0).val, mem_image_of_mem _ (mem_univ 0)⟩
  obtain ⟨W, v, hw, hd⟩ := h n _ hne
  refine ⟨W, v, hw, ?_⟩
  have size : Fintype.card U * Fintype.card V = Fintype.card (Cube n) := by
    simpa only [Fintype.card_prod] using Fintype.card_congr (U.prodEquivOfIsCompl V hUV).toEquiv
  have den : ((graph U V f).dens : ℝ) = (Fintype.card V : ℝ)⁻¹ := by
    have hU : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
    have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, graph_card U V hUV,
      Nat.card_eq_fintype_card, ← size, Nat.cast_mul]
    field_simp
    simp
  rw [den, one_div, inv_inv, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card,
    Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hd
  exact hd

/-- Five summands of total function graphs suffice for Green's tenfold statement with the same C. -/
theorem five_graphs_suffice (h : ∃ C > (0 : ℝ), GraphBound 5 C) :
    ∃ C > (0 : ℝ), SetBound 10 C := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC,graph_to_set hC.le h⟩

/-- Existence of some fixed summand count is equivalent for full graphs and all subsets. -/
theorem exists_fixed_summands_iff :
    (∃ k > 0, ∃ C > (0 : ℝ), SetBound k C) ↔ (∃ k > 0, ∃ C > (0 : ℝ), GraphBound k C) := by
  constructor
  · rintro ⟨k, hk, C,  hC, h⟩
    exact ⟨k, hk, C,  hC,set_to_graph h⟩
  · rintro ⟨k, hk, C,  hC, h⟩
    exact ⟨2 * k,by omega, C,  hC,graph_to_set hC.le h⟩

#print axioms quotient_model
#print axioms graph_card
#print axioms graph_in_twofold
#print axioms graph_to_set
#print axioms set_to_graph
#print axioms five_graphs_suffice
#print axioms exists_fixed_summands_iff

end Green50Graphs
