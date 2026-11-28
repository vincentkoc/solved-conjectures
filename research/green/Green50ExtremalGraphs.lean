import Green50AlternatingRank

/-! # The sharp covering order of binary quadratic graphs at prescribed dimensions -/

open Finset
open scoped Pointwise

namespace Green50ExtremalGraphs
local notation "K" => ZMod 2
variable {D E : Type*} [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [AddCommGroup E] [Module K E]

private theorem twice {G : Type*} [AddCommGroup G] [Module K G] (v : G) : v + v = 0 := by
  rw [← two_smul K v, show (2 : K) = 0 by decide, zero_smul]

/-- Integrate an arbitrary alternating map to a normalized binary quadratic function. -/
theorem quadratic_primitive (B : D →ₗ[K] D →ₗ[K] E) (hB : ∀ a, B a a = 0) :
    ∃ f : D → E, f 0 = 0 ∧ ∀ a x, f x + f (x + a) = B a x + (f 0 + f a) := by
  classical
  let b := Module.finBasis K D
  let A : D →ₗ[K] D →ₗ[K] E := b.constr K fun i =>
    b.constr K (fun j => if i < j then B (b i) (b j) else 0)
  have sym (x y : D) : B x y = B y x := by
    have he := hB (x + y)
    simp [hB] at he
    calc
      B x y = -(B y x) := eq_neg_of_add_eq_zero_left he
      _ = B y x := neg_eq_of_add_eq_zero_left (twice _)
  have split : A + A.flip = B := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    simp only [LinearMap.add_apply, LinearMap.flip_apply, A, Module.Basis.constr_basis]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.asymm]
    · simp [hB]
    · simp [h, h.asymm, sym (b i) (b j)]
  refine ⟨fun x => A x x, by simp, ?_⟩
  intro a x
  have hcross := congrArg (fun F : D →ₗ[K] D →ₗ[K] E => F a x) split
  change A a x + A x a = B a x at hcross
  simp only [map_add, LinearMap.add_apply, map_zero, zero_add]
  rw [← hcross]
  have h := twice (A x x)
  abel_nf at h ⊢
  rw [h, zero_add]

open Green50AlternatingRank Green50QuadraticDiameter Green50QuadraticGraphs Green50QuadraticFibres

abbrev Cube (n : ℕ) := Fin n → K

/-- For each feasible combination of input and polar output dimensions, a normalized
quadratic graph attains the universal covering bound at every positive summand count. -/
theorem extremal_graph (n d : ℕ) (hd : d ≤ n.choose 2) :
    ∃ (f : Cube n → Cube d) (G : Cube n →ₗ[K] Cube n →ₗ[K] Cube d),
      f 0 = 0 ∧ (∀ a x, f x + f (x + a) = G a x + (f 0 + f a)) ∧ valueSpan G = ⊤ ∧
      ∀ m : ℕ, 0 < m → (m • graph f = univ ↔ 2 * min (n / 2) d.sqrt + 1 ≤ m) := by
  classical
  let r := min (n / 2) d.sqrt
  let s := n - 2 * r
  have hdim : 2 * r + s = n := by
    have hx : r ≤ n / 2 := min_le_left _ _
    dsimp [s]; omega
  have hr : r * r ≤ d := Nat.le_sqrt.mp (min_le_right _ _)
  let V := Model K r s
  let U := Module.Dual K V
  obtain ⟨T, J, hcod, _, hmin⟩ := (minimum_rank_at_codimension K r s d (by rwa [hdim])).mpr hr
  let Q := alternatingForms K V ⧸ T
  let B := quotientPair T
  have vn : Module.finrank K V = n := by simp [V, Model, Module.finrank_prod]; omega
  let eu : Cube n ≃ₗ[K] U := LinearEquiv.ofFinrankEq _ _ (by simp [Cube, U, Subspace.dual_finrank_eq, vn])
  let ev : Q ≃ₗ[K] Cube d := LinearEquiv.ofFinrankEq _ _ (by simp [Q, Cube, hcod, V])
  let G : Cube n →ₗ[K] Cube n →ₗ[K] Cube d := LinearMap.mk₂ K (fun x y => ev (B (eu x) (eu y)))
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have halt (x : Cube n) : G x x = 0 := by
    change ev (quotientPair T _ _) = 0
    rw [quotient_alt, map_zero]
  have hspan : valueSpan G = ⊤ := by
    refine top_unique fun v htop => ?_
    clear htop
    obtain ⟨q, rfl⟩ := ev.surjective v
    have hq : q ∈ valueSpan B := by rw [show valueSpan B = ⊤ from quotient_span T]; trivial
    change q ∈ Submodule.span K _ at hq
    induction hq using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hz
      apply Submodule.subset_span
      exact ⟨(eu.symm a, eu.symm b), by simp [G]⟩
    | zero => simp
    | add _ _ _ _ hx hy => simpa using (valueSpan G).add_mem hx hy
    | smul c _ _ h => simpa using (valueSpan G).smul_mem c h
  obtain ⟨f, h0, hf⟩ := quadratic_primitive G halt
  have hz : (0 : Cube n × Cube d) ∈ graph f := by
    exact mem_image.mpr ⟨0, mem_univ _, Prod.ext rfl h0⟩
  have mono : Monotone (fun k : ℕ => k • graph f) := by
    apply monotone_nat_of_le_succ
    intro k p hp
    rw [succ_nsmul]
    exact mem_add.mpr ⟨p, hp, 0, hz, add_zero _⟩
  have outDim : Module.finrank K (valueSpan G) = d := by
    rw [hspan, finrank_top]
    simp [Cube]
  have cover : (2 * r + 1) • graph f = univ := by
    apply eq_univ_of_forall
    rintro ⟨u, v⟩
    apply (graph_fibre_of_radius f G hf ?_ u v).mpr (by rw [hspan]; trivial)
    rw [outDim]
    simp [Cube, r]
  refine ⟨f, G, h0, hf, hspan, ?_⟩
  intro m hm
  change m • graph f = univ ↔ 2 * r + 1 ≤ m
  constructor
  · intro hall
    by_contra! hsmall
    obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    have hp : ((0 : Cube n), ev (T.mkQ J)) ∈ m • graph f := by rw [hall]; exact mem_univ _
    have h2 := mono (show m ≤ 2 * k + 2 by omega) hp
    obtain ⟨x, y, he⟩ := (mem_vertical_sum G k _).mp ((even_zero_fibre f G hf k _).mp h2)
    have rep : Represented B k (T.mkQ J) := by
      refine ⟨fun i => eu (x i), fun i => eu (y i), ev.injective ?_⟩
      rw [map_sum]
      exact he
    obtain ⟨F, hF, small⟩ := class_rank_of_rep T J rep
    have := hmin F hF
    omega
  · intro h
    apply eq_univ_of_forall
    intro p
    exact mono h (show p ∈ (2 * r + 1) • graph f by rw [cover]; exact mem_univ _)

end Green50ExtremalGraphs
#print axioms Green50ExtremalGraphs.quadratic_primitive
#print axioms Green50ExtremalGraphs.extremal_graph
