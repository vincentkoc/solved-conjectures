import Green50QuadraticGraphs

/-! # Fibres of iterated sums of a binary quadratic graph

Each additional pair of graph points contributes a value of the bilinear polarization.
-/

open Finset
open scoped Pointwise

namespace Green50QuadraticFibres
open Green50QuadraticGraphs
local notation "K" => ZMod 2
variable {U V : Type*} [AddCommGroup U] [Module K U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

private theorem twice {G : Type*} [AddCommGroup G] [Module K G] (x : G) : x + x = 0 := by
  rw [← two_smul K x, show (2 : K) = 0 by decide, zero_smul]

def vertical (B : U →ₗ[K] U →ₗ[K] V) : Finset (U × V) :=
  univ.image (fun p : U × U => ((0 : U), B p.1 p.2))

/-- Membership in the vertical sumset is equivalent to a sum of k values of B. -/
theorem mem_vertical_sum (B : U →ₗ[K] U →ₗ[K] V) (k : ℕ) (v : V) :
    ((0 : U), v) ∈ k • vertical B ↔
      ∃ x y : Fin k → U, ∑ i, B (x i) (y i) = v := by
  rw [← Finset.mem_coe, Finset.coe_nsmul, Set.mem_nsmul_iff_sum]
  constructor
  · rintro ⟨f, hf, he⟩
    have h i : ∃ z : U × U, (0, B z.1 z.2) = f i := by
      obtain ⟨z, _, hz⟩ := mem_image.mp (hf i)
      exact ⟨z, hz⟩
    choose z hz using h
    refine ⟨fun i => (z i).1, fun i => (z i).2, ?_⟩
    simpa only [← hz, Prod.snd_sum] using congrArg Prod.snd he
  · rintro ⟨x,y,h⟩
    let g (i : Fin k) : U × V := (0, B (x i) (y i))
    refine ⟨g, ?_, ?_⟩
    · intro i
      change g i ∈ vertical B
      exact mem_image.mpr ⟨(x i, y i), mem_univ _, rfl⟩
    · apply Prod.ext
      · rw [Prod.fst_sum]; simp [g]
      · rw [Prod.snd_sum]; exact h

omit [Fintype U] [DecidableEq U] [DecidableEq V] in
private theorem three_values (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x : U, f x + f (x + a) = B a x + (f 0 + f a)) (u a x : U) :
    f u + (f x + f (x + a)) = f (u + a) + B a (u + x) := by
  have df : f (u + a) = f u + (B a u + (f 0 + f a)) := by
    rw [← hf, ← add_assoc, twice, zero_add]
  rw [hf, df, map_add]
  calc
    _ = (f u + (B a x + (f 0 + f a))) + (B a u + B a u) := by rw [twice, add_zero]
    _ = _ := by abel

/-- The threefold sumset is the graph plus the vertical image of its bilinear form. -/
theorem threefold (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x : U, f x + f (x + a) = B a x + (f 0 + f a)) :
    (3 : ℕ) • graph f = graph f + vertical B := by
  ext p
  rw [show 3 = 2 + 1 by decide, succ_nsmul, add_comm ((2 : ℕ) • graph f), mem_add, mem_add]
  constructor
  · rintro ⟨_, hu,⟨a, b⟩, hab, rfl⟩
    obtain ⟨u, _, rfl⟩ := mem_image.mp hu
    obtain ⟨x, rfl⟩ := (twofold_fibre f a b).mp hab
    refine ⟨(u + a, f (u + a)), mem_image_of_mem _ (mem_univ _),
      (0, B a (u + x)), mem_image_of_mem (fun z : U × U => (0, B z.1 z.2)) (mem_univ (a, u + x)),
      Prod.ext ?_ ?_⟩
    · exact add_zero _
    · exact (three_values f B hf u a x).symm
  · rintro ⟨_, hu, _, hp, rfl⟩
    obtain ⟨y, _, rfl⟩ := mem_image.mp hu
    obtain ⟨⟨a, b⟩, _, rfl⟩ := mem_image.mp hp
    let u := y + a
    let x := u + b
    have h₁ : u + a=y := by dsimp [u]; rw [add_assoc, twice, add_zero]
    have h₂ : u + x=b := by dsimp [x]; rw [←add_assoc, twice, zero_add]
    refine ⟨(u, f u), mem_image_of_mem _ (mem_univ _), (a, f x + f (x + a)),
      (twofold_fibre f a _).mpr ⟨x, rfl⟩, Prod.ext ?_ ?_⟩
    · change u + a=y + 0
      rw [h₁, add_zero]
    · change f u + (f x + f (x + a)) = f y + B a b
      rw [three_values f B hf, h₁, h₂]

/-- Each additional pair of summands contributes one independent bilinear value. -/
theorem odd_sumset (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x : U, f x + f (x + a) = B a x + (f 0 + f a)) (k : ℕ) :
    (2 * k + 1) • graph f = graph f + k • vertical B := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, add_nsmul, ih, succ_nsmul (vertical B) k]
    have h := threefold f B hf
    rw [show 3 = 2 + 1 by decide, succ_nsmul] at h
    calc
      _ = ((2 : ℕ) • graph f + graph f) + k • vertical B := by rw [add_comm (graph f + k • vertical B), ← add_assoc]
      _ = _ := by rw [h, add_assoc, add_comm (vertical B) (k • vertical B)]

/-- Every sum of vertical polar values has zero first coordinate. -/
theorem vertical_fst (B : U →ₗ[K] U →ₗ[K] V) (k : ℕ) (p : U × V)
    (hp : p ∈ k • vertical B) : p.1 = 0 := by
  induction k generalizing p with
  | zero => exact congrArg Prod.fst (show p = 0 by simpa using hp)
  | succ k ih =>
    rw [succ_nsmul, mem_add] at hp
    obtain ⟨x, hx, y, hy, rfl⟩ := hp
    obtain ⟨a, _, rfl⟩ := mem_image.mp hy
    exact (add_zero _).trans (ih x hx)

/-- The zero-input fibre at even length contains exactly the sums of k polarization values. -/
theorem even_zero_fibre (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x : U, f x + f (x + a) = B a x + (f 0 + f a)) (k : ℕ) (v : V) :
    ((0 : U), v) ∈ (2 * k + 2) • graph f ↔ ((0 : U), v) ∈ k • vertical B := by
  have hsum : (2 * k + 2) • graph f = (2 : ℕ) • graph f + k • vertical B := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, succ_nsmul, odd_sumset f B hf, two_nsmul]
    rw [add_right_comm]
  rw [hsum, mem_add]
  constructor
  · rintro ⟨⟨a, b⟩, h, ⟨c, d⟩, hq, he⟩
    have hc : c = 0 := vertical_fst B k (c, d) hq
    subst c
    have hz : a + 0 = 0 := congrArg Prod.fst he
    obtain rfl : a = 0 := by simpa using hz
    obtain ⟨x, hx⟩ := (twofold_fibre f 0 b).mp h
    have hb : b = 0 := by simpa [twice] using hx.symm
    rw [hb] at he
    have he' : (0 : V) + d = v := congrArg Prod.snd he
    simp only [zero_add] at he'
    exact he' ▸ hq
  · intro h
    have h0 : ((0 : U), (0 : V)) ∈ (2 : ℕ) • graph f :=
      (twofold_fibre f 0 0).mpr ⟨0, by rw [add_zero, twice]⟩
    exact ⟨_, h0, _, h, zero_add _⟩

end Green50QuadraticFibres

#print axioms Green50QuadraticFibres.threefold
#print axioms Green50QuadraticFibres.odd_sumset
#print axioms Green50QuadraticFibres.even_zero_fibre
#print axioms Green50QuadraticFibres.mem_vertical_sum
#print axioms Green50QuadraticFibres.vertical_fst
