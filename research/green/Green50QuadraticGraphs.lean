import Green50Graphs

/-! # Five sums of a quadratic graph in characteristic two

The squared sizes of the scalar radicals bound the number of bad direction pairs.
Under the resulting rank condition, five graph points can realize every ambient point.
-/

open Finset
open scoped Pointwise

namespace Green50QuadraticGraphs
variable {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]

private theorem twice {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] (x : G) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul]

def graph (f : U → V) : Finset (U × V) := univ.image (fun x => (x, f x))

omit [Module (ZMod 2) V] [Fintype V] in
/-- The twofold graph fibre over a direction is exactly the image of the first difference. -/
theorem twofold_fibre (f : U → V) (a : U) (b : V) :
    (a, b) ∈ (2 : ℕ) • graph f ↔ ∃ x, f x + f (x + a) = b := by
  rw [two_nsmul, mem_add]
  constructor
  · rintro ⟨_, hx, _, hy, he⟩
    obtain ⟨x, _, rfl⟩ := mem_image.mp hx
    obtain ⟨y, _, rfl⟩ := mem_image.mp hy
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change x + y = a at h₁
    change f x + f y = b at h₂
    refine ⟨x, ?_⟩
    rw [← h₁, ← add_assoc, twice, zero_add]
    exact h₂
  · rintro ⟨x, hx⟩
    refine ⟨(x, f x), mem_image_of_mem _ (mem_univ _),
      (x + a, f (x + a)), mem_image_of_mem _ (mem_univ _), Prod.ext ?_ hx⟩
    change x + (x + a) = a
    rw [← add_assoc, twice, zero_add]

omit [Module (ZMod 2) V] in
/-- One surjective directional difference fills the whole ambient space in three summands. -/
theorem threefold_of_surj (f : U → V) (a : U)
    (h : Function.Surjective (fun x => f x + f (x + a))) : (3 : ℕ) • graph f = univ := by
  apply eq_univ_of_forall
  rintro ⟨x, y⟩
  rw [show 3 = 2 + 1 by decide, succ_nsmul]
  refine mem_add.mpr ⟨(a, y - f (x + a)), (twofold_fibre _ _ _).mpr (h _), (x + a, f (x + a)),
    mem_image_of_mem _ (mem_univ _), Prod.ext ?_ ?_⟩
  · change a + (x + a) = x
    rw [add_left_comm, twice, add_zero]
  · exact sub_add_cancel _ _

omit [Module (ZMod 2) V] in
/-- Two directions suffice if their differences together realize every output. -/
theorem fivefold_of_differences (f : U → V) (a b : U)
    (h : ∀ t : V, ∃ x y : U, (f x + f (x + a)) + (f y + f (y + b)) = t) :
    (5 : ℕ) • graph f = univ := by
  apply eq_univ_of_forall
  rintro ⟨u, t⟩
  let z := u + (a + b)
  obtain ⟨x, y, he⟩ := h (t - f z)
  have hx := (twofold_fibre f a _).mpr ⟨x, rfl⟩
  have hy := (twofold_fibre f b _).mpr ⟨y, rfl⟩
  rw [show 5 = 2 + 2 + 1 by decide, succ_nsmul, add_nsmul]
  have hz : (z, f z) ∈ graph f := mem_image_of_mem _ (mem_univ z)
  refine (show (u, t) = ((a, f x + f (x + a)) + (b, f y + f (y + b))) + (z, f z) from ?_).symm ▸
    (add_mem_add (add_mem_add hx hy) hz)
  apply Prod.ext
  · change u = (a + b) + z
    dsimp [z]
    rw [add_left_comm, twice, add_zero]
  · change t = (f x + f (x + a) + (f y + f (y + b))) + f z
    rw [he, sub_add_cancel]

/-- The scalar bilinear form obtained by applying an output functional to the polarization. -/
def component (B : U →ₗ[ZMod 2] U →ₗ[ZMod 2] V) (l : Module.Dual (ZMod 2) V) :
    U →ₗ[ZMod 2] Module.Dual (ZMod 2) U := LinearMap.llcomp (ZMod 2) U V (ZMod 2) l ∘ₗ B

omit [Fintype U] [DecidableEq U] [DecidableEq V] in
private theorem output_obstruction (F : (U × U) →ₗ[ZMod 2] V) (h : ¬ Function.Surjective F) :
    ∃ l : Module.Dual (ZMod 2) V, l ≠ 0 ∧ ∀ p : U × U, l (F p) = 0 := by
  have hne : LinearMap.range F ≠ ⊤ := fun e => h (LinearMap.range_eq_top.mp e)
  have han : (LinearMap.range F).dualAnnihilator ≠ ⊥ := fun e =>
    hne ((Submodule.dualAnnihilator_eq_bot_iff).mp e)
  obtain ⟨l, hl, hn⟩ := (Submodule.ne_bot_iff _).mp han
  exact ⟨l, hn, fun p => ((LinearMap.range F).mem_dualAnnihilator l).mp hl _ ⟨p, rfl⟩⟩

private theorem outside_union {α ι : Type*} [Fintype α] (s : Finset ι) (bad : ι → Finset α)
    (h : ∑ i ∈ s, (bad i).card < Fintype.card α) :
    ∃ x : α, ∀ i ∈ s, x ∉ bad i := by
  classical
  by_contra! hc
  have hall : s.biUnion bad = univ := eq_univ_of_forall fun x => by
    obtain ⟨i, hi, hx⟩ := hc x
    exact mem_biUnion.mpr ⟨i, hi, hx⟩
  have hb := card_biUnion_le (s := s) (t := bad)
  rw [hall, card_univ] at hb
  omega

noncomputable section

local instance : Fintype (Module.Dual (ZMod 2) V) :=
  Fintype.ofInjective (fun l : Module.Dual (ZMod 2) V => (l : V → ZMod 2)) DFunLike.coe_injective

open scoped Classical

omit [DecidableEq U] in
/-- Scalar radicals with small total squared size leave two jointly surjective directions. -/
theorem surjective_pair_of_radicals (B : U →ₗ[ZMod 2] U →ₗ[ZMod 2] V)
    (h : ∑ l : Module.Dual (ZMod 2) V with l ≠ 0,
        (Nat.card (LinearMap.ker (component B l))) ^ 2 < (Nat.card U) ^ 2) :
    ∃ a b : U, Function.Surjective ((B a).coprod (B b)) := by
  classical
  let A (l : Module.Dual (ZMod 2) V) := (LinearMap.ker (component B l) : Set U).toFinset
  have hc (l : Module.Dual (ZMod 2) V) : (A l).card = Nat.card (LinearMap.ker (component B l)) := by
    simp [A, Nat.card_eq_fintype_card]
  obtain ⟨⟨a, b⟩, hab⟩ := outside_union (univ.filter (fun l : Module.Dual (ZMod 2) V => l ≠ 0))
    (fun l => A l ×ˢ A l) (by simpa only [card_product, hc, Fintype.card_prod,
      Nat.card_eq_fintype_card, Fintype.card_prod, ← sq] using h)
  refine ⟨a, b,?_⟩
  by_contra hn
  obtain ⟨l, hl, hz⟩ := output_obstruction _ hn
  apply hab l (mem_filter.mpr ⟨mem_univ _, hl⟩)
  apply mem_product.mpr
  constructor
  · apply Set.mem_toFinset.mpr
    apply LinearMap.ext
    intro x
    simpa [component] using hz (x, 0)
  · apply Set.mem_toFinset.mpr
    apply LinearMap.ext
    intro y
    simpa [component] using hz (0, y)

/-- Under the radical count, five sums of the quadratic graph fill the entire product. -/
theorem fivefold_of_radicals (f : U → V) (B : U →ₗ[ZMod 2] U →ₗ[ZMod 2] V)
    (hf : ∀ a x : U, f x + f (x + a) = B a x + (f 0 + f a))
    (h : ∑ l : Module.Dual (ZMod 2) V with l ≠ 0,
        (Nat.card (LinearMap.ker (component B l))) ^ 2 < (Nat.card U) ^ 2) :
    (5 : ℕ) • graph f = univ := by
  obtain ⟨a, b, hs⟩ := surjective_pair_of_radicals B h
  apply fivefold_of_differences f a b
  intro t
  obtain ⟨⟨x, y⟩, he⟩ := hs (t - ((f 0 + f a) + (f 0 + f b)))
  change B a x + B b y = _ at he
  refine ⟨x, y,?_⟩
  rw [hf, hf]
  calc
    _ = (B a x + B b y) + ((f 0 + f a) + (f 0 + f b)) := by abel
    _ = t := by rw [he, sub_add_cancel]

/-- It suffices that twice the rank of each nonzero scalar polarization reach the output
dimension. The conclusion includes every point of every fibre. -/
theorem fivefold_of_component_rank (f : U → V) (B : U →ₗ[ZMod 2] U →ₗ[ZMod 2] V)
    (hf : ∀ a x : U, f x + f (x + a) = B a x + (f 0 + f a))
    (hr : ∀ l : Module.Dual (ZMod 2) V, l ≠ 0 →
      Module.finrank (ZMod 2) V ≤ 2 * Module.finrank (ZMod 2) (component B l).range) :
    (5 : ℕ) • graph f = univ := by
  classical
  apply fivefold_of_radicals f B hf
  let L := univ.filter (fun l : Module.Dual (ZMod 2) V => l ≠ 0)
  have dual_card : Nat.card (Module.Dual (ZMod 2) V) = Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq,
      ← Module.natCard_eq_pow_finrank]
  have count : L.card < Nat.card V := by
    rw [← dual_card, Nat.card_eq_fintype_card, ← card_univ]
    apply card_lt_card
    apply lt_of_le_of_ne (subset_univ L)
    intro he
    have h0 : (0 : Module.Dual (ZMod 2) V) ∈ L := he ▸ mem_univ _
    simp [L] at h0
  have one (l : Module.Dual (ZMod 2) V) (hl : l ∈ L) :
      Nat.card (LinearMap.ker (component B l)) ^ 2 * Nat.card V ≤ (Nat.card U) ^ 2 := by
    have hr' := hr l (mem_filter.mp hl).2
    have hdim := (component B l).finrank_range_add_finrank_ker
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (component B l).ker),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U), Nat.card_zmod,
      ← pow_mul, ← pow_mul, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  change ∑ l ∈ L, (Nat.card (LinearMap.ker (component B l))) ^ 2 < _
  apply Nat.lt_of_mul_lt_mul_right (a := Nat.card V)
  calc
    _ = ∑ l ∈ L, Nat.card (LinearMap.ker (component B l)) ^ 2 * Nat.card V := by rw [sum_mul]
    _ ≤ ∑ _l ∈ L, (Nat.card U) ^ 2 := sum_le_sum one
    _ = L.card * (Nat.card U) ^ 2 := by simp
    _ < Nat.card V * (Nat.card U) ^ 2 := Nat.mul_lt_mul_of_pos_right count (pow_pos Nat.card_pos _)
    _ = _ := mul_comm _ _

end
section Embedded
open scoped Classical
variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] [DecidableEq G]

/-- Transport a product-graph sumset equality to the graph in the original cube. -/
theorem embedded_full (U V : Submodule (ZMod 2) G) (h : IsCompl U V) (f : U → V) (k : ℕ)
    (hk : k • graph f = univ) : k • Green50Graphs.graph U V f = univ := by
  classical
  let e := U.prodEquivOfIsCompl V h
  have eq_graph : (graph f).image e = Green50Graphs.graph U V f := by
    rw [graph, Green50Graphs.graph, image_image]
    rfl
  rw [← eq_graph, ← image_nsmul e (graph f), hk, image_univ_of_surjective e.surjective]

/-- A high-rank quadratic graph inside A + A forces the tenfold sumset to fill the cube. -/
theorem tenfold_of_quadratic_model (A : Finset G) (U V : Submodule (ZMod 2) G)
    (h : IsCompl U V) (f : U → V) (B : U →ₗ[ZMod 2] U →ₗ[ZMod 2] V)
    (contained : Green50Graphs.graph U V f ⊆ A + A)
    (hf : ∀ a x : U, f x + f (x + a) = B a x + (f 0 + f a))
    (hr : ∀ l : Module.Dual (ZMod 2) V, l ≠ 0 →
      Module.finrank (ZMod 2) V ≤ 2 * Module.finrank (ZMod 2) (component B l).range) :
    (10 : ℕ) • A = univ := by
  classical
  have hfull := embedded_full U V h f 5 (fivefold_of_component_rank f B hf hr)
  have hs := nsmul_subset_nsmul_left (n := 5) contained
  rw [hfull] at hs
  apply eq_univ_of_forall
  intro x
  simpa only [← two_nsmul, ← mul_smul, show (5 : ℕ) * 2 = 10 by decide] using hs (mem_univ x)
end Embedded

omit [Fintype V] [Module (ZMod 2) V] in
/-- Four summands above zero are sums of two differences in the same direction. -/
theorem fourfold_zero_fibre (f : U → V) (t : V) :
    (0, t) ∈ (4 : ℕ) • graph f ↔ ∃ a x y : U, (f x + f (x + a)) + (f y + f (y + a)) = t := by
  rw [show 4 = 2 + 2 by decide, add_nsmul, mem_add]
  constructor
  · rintro ⟨⟨a, v⟩, ha, ⟨b, w⟩, hb, he⟩
    have hab : a + b = 0 := congrArg Prod.fst he
    have hv : v + w = t := congrArg Prod.snd he
    have hab' : a = b := by
      calc
        a = a + (b + b) := by rw [twice, add_zero]
        _ = b := by rw [← add_assoc, hab, zero_add]
    subst b
    obtain ⟨x, rfl⟩ := (twofold_fibre f a v).mp ha
    obtain ⟨y, rfl⟩ := (twofold_fibre f a w).mp hb
    exact ⟨a, x, y, hv⟩
  · rintro ⟨a, x, y, h⟩
    exact ⟨_, (twofold_fibre f a _).mpr ⟨x, rfl⟩, _, (twofold_fibre f a _).mpr ⟨y, rfl⟩, Prod.ext (twice a) h⟩

omit [Module (ZMod 2) V] in
private theorem fourfold_ne_full_of_missing (f : U → V) (t : V)
    (h : ∀ a x y : U, (f x + f (x + a)) + (f y + f (y + a)) ≠ t) :
    (4 : ℕ) • graph f ≠ univ := by
  intro he
  have ht : ((0 : U), t) ∈ (4 : ℕ) • graph f := by
    rw [he]
    exact mem_univ _
  obtain ⟨a, x, y, hh⟩ := (fourfold_zero_fibre f t).mp ht
  exact h a x y hh

abbrev Four := Fin 4 → ZMod 2

/-- Four quadratic coordinates indexed by the pairs 03, 12, 13 and 23. -/
def minorsGraphMap (x : Four) : Four :=
  ![x 0 * x 3, x 1 * x 2, x 1 * x 3, x 2 * x 3]

private def minor (a b : Four) (i j : Fin 4) := a i * b j + a j * b i

private theorem difference_coords (a x y : Four) :
    (minorsGraphMap x + minorsGraphMap (x + a)) + (minorsGraphMap y + minorsGraphMap (y + a)) =
      ![minor a (x + y) 0 3, minor a (x + y) 1 2, minor a (x + y) 1 3, minor a (x + y) 2 3] := by
  ext i
  fin_cases i <;> simp [minorsGraphMap, minor, Pi.add_apply] <;> ring_nf <;> simp [show (2 : ZMod 2) = 0 by decide]

/-- This quadratic map has exact covering order five. -/
theorem five_is_sharp :
    (5 : ℕ) • graph minorsGraphMap = univ ∧ (4 : ℕ) • graph minorsGraphMap ≠ univ := by
  constructor
  · apply fivefold_of_differences minorsGraphMap (![0, 0, 0, 1] : Four) (![0, 0, 1, 0] : Four)
    intro t
    refine ⟨![t 0, t 2, t 3, 0], ![0, t 1, 0, 0], ?_⟩
    ext i
    fin_cases i <;> simp [minorsGraphMap, Pi.add_apply, twice]
  · apply fourfold_ne_full_of_missing minorsGraphMap (![1, 1, 0, 0] : Four)
    intro a x y he
    rw [difference_coords] at he
    let b := x + y
    have h03 : minor a b 0 3 = 1 := congrFun he 0
    have h12 : minor a b 1 2 = 1 := congrFun he 1
    have h13 : minor a b 1 3 = 0 := congrFun he 2
    have h23 : minor a b 2 3 = 0 := congrFun he 3
    have hp : minor a b 0 1 * minor a b 2 3 + minor a b 0 2 * minor a b 1 3 +
        minor a b 0 3 * minor a b 1 2 = 0 := by
      unfold minor
      ring_nf
      simp [show (2 : ZMod 2) = 0 by decide]
    rw [h03, h12, h13, h23] at hp
    norm_num at hp

end Green50QuadraticGraphs

#print axioms Green50QuadraticGraphs.twofold_fibre
#print axioms Green50QuadraticGraphs.threefold_of_surj
#print axioms Green50QuadraticGraphs.fivefold_of_differences
#print axioms Green50QuadraticGraphs.surjective_pair_of_radicals
#print axioms Green50QuadraticGraphs.fivefold_of_radicals
#print axioms Green50QuadraticGraphs.fivefold_of_component_rank
#print axioms Green50QuadraticGraphs.embedded_full
#print axioms Green50QuadraticGraphs.tenfold_of_quadratic_model
#print axioms Green50QuadraticGraphs.fourfold_zero_fibre
#print axioms Green50QuadraticGraphs.five_is_sharp
