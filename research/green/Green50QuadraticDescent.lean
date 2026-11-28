import Green50QuadraticGraphs

/-! # Affine subspaces in five sums of an arbitrary quadratic graph

An alternating scalar component of rank r has a totally isotropic subspace of codimension r/2.
Restricting there removes one output coordinate. See `QUADRATIC-FUNCTION-GRAPHS.md`.
-/

open Finset
open scoped Pointwise Classical
namespace Green50QuadraticDescent
open Green50QuadraticGraphs
local notation "K" => ZMod 2

private theorem twice {G : Type*} [AddCommGroup G] [Module K G] (x : G) : x + x = 0 := by
  rw [← two_smul K x, show (2 : K) = 0 by decide, zero_smul]

/-- Cost of successively eliminating scalar components of insufficient rank. -/
def cost : ℕ → ℕ
  | 0 => 0
  | d + 1 => cost d + d / 4 + 1

private theorem cost_add_four (d : ℕ) : cost (d + 4) = cost d + d + 4 := by
  simp only [cost]
  omega

theorem cost_eq (d : ℕ) : cost d = (d + 2) ^ 2 / 8 := by
  have blocks (q r : ℕ) (hr : r < 4) : cost (4 * q + r) = (q + 1) * (2 * q + r) := by
    induction q with
    | zero => interval_cases r <;> decide
    | succ q ih =>
      rw [show 4 * (q + 1) + r = 4 * q + r+4 by omega, cost_add_four, ih]
      ring
  let q := d / 4
  let r := d % 4
  have hr : r < 4 := Nat.mod_lt _ (by decide)
  have hd : d = 4 * q + r := by dsimp [q, r]; omega
  rw [hd, blocks q r hr]
  clear_value r q
  interval_cases r <;> ring_nf <;> omega

private def HasSubspace {G : Type*} [AddCommGroup G] [Module K G] (S : Finset G) (k : ℕ) :=
  ∃ W : Submodule K G, (∀ w ∈ W, w ∈ S) ∧ Module.finrank K G ≤ Module.finrank K W + k

private theorem push_subspace {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    [Module K G] [Module K G'] [DecidableEq G'] (e : G →ₗ[K] G') (he : Function.Injective e)
    {S : Finset G} {T : Finset G'} {k c : ℕ} (hs : HasSubspace S k)
    (ht : S.image e ⊆ T) (hd : Module.finrank K G' ≤ Module.finrank K G + c) :
    HasSubspace T (k + c) := by
  obtain ⟨W, hw, dim⟩ := hs
  refine ⟨W.map e, ?_, ?_⟩
  · rintro _ ⟨w, h, rfl⟩
    exact ht (mem_image_of_mem _ (hw w h))
  · have hdim := (W.equivMapOfInjective e he).finrank_eq
    omega

variable {U V : Type*} [AddCommGroup U] [Module K U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [DecidableEq U] in
/-- A maximal totally isotropic subspace loses precisely half the rank of an alternating form. -/
theorem isotropic_half_rank (Q : LinearMap.BilinForm K U) (hQ : Q.IsAlt) :
    ∃ H : Submodule K U, (∀ x ∈ H, ∀ y ∈ H, Q x y = 0) ∧
      2 * (Module.finrank K U - Module.finrank K H) = Module.finrank K Q.range := by
  classical
  let family := univ.filter (fun H : Submodule K U => H ≤ Q.orthogonal H)
  have hbot : (⊥ : Submodule K U) ∈ family := mem_filter.mpr ⟨mem_univ _, bot_le⟩
  obtain ⟨H, hH, hmax⟩ := exists_max_image family (fun H => Module.finrank K H) ⟨_, hbot⟩
  have hii : H ≤ Q.orthogonal H := (mem_filter.mp hH).2
  have heq : Q.orthogonal H = H := by
    refine le_antisymm ?_ hii
    intro z hz
    by_contra hn
    let P := H ⊔ Submodule.span K {z}
    have hlt : H < P := lt_of_le_of_ne le_sup_left fun he => hn (he ▸
      (show z ∈ P from (le_sup_right : Submodule.span K {z} ≤ P) (Submodule.mem_span_singleton_self z)))
    have hit : P ∈ family := by
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro a ha b hb
      obtain ⟨x, hx, x', hx', rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx'
      obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.mp hy'
      have hyx : Q y x = 0 := hii hx y hy
      have hyz : Q y z = 0 := hz y hy
      have hzx : Q z x = 0 := (hQ.eq_iff).mp (hz x hx)
      have hzz : Q z z = 0 := hQ z
      simp [map_add, hyx, hyz, hzx, hzz]
    exact (Submodule.finrank_lt_finrank_of_lt hlt).not_ge (hmax P hit)
  have hker : Q.ker ≤ H := by
    rw [← heq]
    intro x hx y _
    apply hQ.eq_iff.mp
    exact LinearMap.congr_fun (show Q x = 0 from hx) y
  have dim := Q.finrank_add_finrank_orthogonal' H
  rw [heq, inf_eq_right.mpr hker] at dim
  have rk := Q.finrank_range_add_finrank_ker
  exact ⟨H, fun x hx y hy => hii hy x hx, by omega⟩

private def Normal (f : U → V) (B : U →ₗ[K] U →ₗ[K] V) :=
  f 0 = 0 ∧ ∀ a x : U, f (x + a) = f x + (B a x + f a)

private theorem high (f : U → V) (B : U →ₗ[K] U →ₗ[K] V) (hf : Normal f B)
    (hr : ∀ l : Module.Dual K V, l ≠ 0 →
      Module.finrank K V ≤ 2 * Module.finrank K (component B l).range) :
    (5 : ℕ) • graph f = univ := by
  apply fivefold_of_component_rank f B _ hr
  intro a x
  rw [hf.2, ← add_assoc, twice, zero_add, hf.1, zero_add]

private theorem smaller (f : U → V) (B : U →ₗ[K] U →ₗ[K] V) (hf : Normal f B)
    (l : Module.Dual K V) (hl : l ≠ 0) (R : Submodule K U)
    (isotropic : ∀ a ∈ R, ∀ x ∈ R, l (B a x) = 0) :
    let W := l.ker
    ∃ (g : R → W) (C : R →ₗ[K] R →ₗ[K] W) (e : (R × W) →ₗ[K] (U × V)),
      Normal g C ∧ Function.Injective e ∧ (graph g).image e ⊆ graph f := by
  classical
  let W := l.ker
  obtain ⟨v, hv⟩ := (LinearMap.surjective hl) (1 : K)
  let pr : V →ₗ[K] V := LinearMap.id - l.smulRight v
  have hpr (y : V) : pr y ∈ W := by
    change l (y - l y • v) = 0
    simp [hv]
  let P := pr.codRestrict W hpr
  let g (a : R) := P (f a)
  let C : R →ₗ[K] R →ₗ[K] W := (B.compl₁₂ R.subtype R.subtype).compr₂ P
  have hrad (a x : R) : l (B a x) = 0 := isotropic a a.property x x.property
  let L : R →ₗ[K] K := {
    toFun := fun x => l (f x)
    map_add' := by
      intro x a
      change l (f ((x : U) + a)) = _
      rw [hf.2]
      simp [hrad a]
    map_smul' := by
      intro c x
      rcases (show ∀ t : K, t = 0 ∨ t = 1 from by decide) c with rfl | rfl <;> simp [hf.1]
  }
  let fst := LinearMap.fst K R W
  let snd := LinearMap.snd K R W
  let e := (R.subtype.comp fst).prod (W.subtype.comp snd + (L.smulRight v).comp fst)
  refine ⟨g, C, e, ⟨?_, ?_⟩, ?_, ?_⟩
  · change P (f 0) = 0
    rw [hf.1, map_zero]
  · intro a x
    change P (f ((x : U) + a)) = P (f x) + (P (B a x) + P (f a))
    rw [hf.2, map_add, map_add]
  · rintro ⟨x, y⟩ ⟨x', y'⟩ he
    have hx : (x : U) = (x' : U) := congrArg Prod.fst he
    obtain rfl : x = x' := Subtype.ext hx
    have hy : (y : V) + L x • v = (y' : V) + L x • v := congrArg Prod.snd he
    exact Prod.ext rfl (Subtype.ext (add_right_cancel hy))
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hz
    obtain ⟨a, _, rfl⟩ := mem_image.mp hp
    refine mem_image.mpr ⟨(a : U), mem_univ _, Prod.ext rfl ?_⟩
    change f a = (f a - l (f a) • v) + l (f a) • v
    rw [sub_add_cancel]

universe u v

private theorem descend (d : ℕ) :
    ∀ {U : Type u} {V : Type v} [AddCommGroup U] [Module K U] [Fintype U] [DecidableEq U]
      [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
      (f : U → V) (B : U →ₗ[K] U →ₗ[K] V),
      Module.finrank K V = d → Normal f B → HasSubspace (5 • graph f) (cost d) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro U V _ _ _ _ _ _ _ _ f B hd hf
    classical
    by_cases good : ∀ l : Module.Dual K V, l ≠ 0 →
        Module.finrank K V ≤ 2 * Module.finrank K (component B l).range
    · refine ⟨⊤, ?_, by simp⟩
      rw [high f B hf good]
      simp
    push Not at good
    obtain ⟨l, hl, hr⟩ := good
    have hv := Module.Dual.finrank_ker_add_one_of_ne_zero hl
    have alt : (component B l).IsAlt := by
      intro x
      have hx := hf.2 x x
      rw [twice, hf.1, add_left_comm, twice, add_zero] at hx
      change l (B x x) = 0
      rw [← hx, map_zero]
    obtain ⟨H, hH, hdimH⟩ := isotropic_half_rank (component B l) alt
    change 2 * (Module.finrank K U - Module.finrank K H) =
      Module.finrank K (component B l).range at hdimH
    obtain ⟨g, C, e, hg, he, contained⟩ := smaller f B hf l hl H hH
    have smallerFlat := ih (Module.finrank K l.ker) (by omega) g C rfl hg
    have hmap : (5 • graph g).image e ⊆ 5 • graph f := by
      rw [image_nsmul]
      exact nsmul_subset_nsmul_left contained
    have hdim : Module.finrank K (U × V) ≤
        Module.finrank K (H × l.ker) + (Module.finrank K l.ker / 4 + 1) := by
      rw [Module.finrank_prod, Module.finrank_prod]
      omega
    have result := push_subspace e he smallerFlat hmap hdim
    rw [show d = Module.finrank K l.ker + 1 by omega, cost]
    simpa only [Nat.add_assoc] using result

/-- Every binary quadratic graph contains a coset of bounded codimension in five summands. -/
theorem quadratic_graph_coset (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x : U, f x + f (x + a) = B a x + (f 0 + f a)) :
    ∃ (W : Submodule K (U × V)) (t : U × V),
      (∀ w ∈ W, t + w ∈ (5 : ℕ) • graph f) ∧
      Module.finrank K (U × V) ≤ Module.finrank K W + (Module.finrank K V + 2) ^ 2 / 8 := by
  classical
  let g (x : U) := f x + f 0
  have hg : Normal g B := by
    refine ⟨twice _, ?_⟩
    intro a x
    change f (x + a) + f 0 = (f x + f 0) + (B a x + (f a + f 0))
    calc
      _ = f x + (f x + f (x + a)) + f 0 := by rw [← add_assoc, twice, zero_add]
      _ = _ := by rw [hf]; abel
  obtain ⟨W, hw, dim⟩ := descend _ g B rfl hg
  let t : U × V := (0, f 0)
  have hgraph : {t} + graph g ⊆ graph f := by
    intro p hp
    obtain ⟨v, hv, y, hy, rfl⟩ := mem_add.mp hp
    obtain rfl := mem_singleton.mp hv
    obtain ⟨x, _, rfl⟩ := mem_image.mp hy
    refine mem_image.mpr ⟨x, mem_univ _, Prod.ext ?_ ?_⟩
    · exact (zero_add x).symm
    · change f x = f 0 + (f x + f 0)
      rw [add_left_comm, twice, add_zero]
  refine ⟨W, 5 • t, ?_, by simpa only [cost_eq] using dim⟩
  intro w hW
  apply nsmul_subset_nsmul_left (n := 5) hgraph
  rw [nsmul_add, nsmul_singleton]
  exact add_mem_add (mem_singleton_self _) (hw w hW)

/-- Ten summands inherit the codimension bound whenever A + A contains a full quadratic graph. -/
theorem tenfold_quadratic_coset {G : Type*} [AddCommGroup G] [Module K G] [Fintype G]
    [DecidableEq G] (A : Finset G) (U V : Submodule K G) (hc : IsCompl U V)
    (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hg : Green50Graphs.graph U V f ⊆ A + A)
    (hf : ∀ a x : U, f x + f (x + a) = B a x + (f 0 + f a)) :
    ∃ (W : Submodule K G) (v : G), v +ᵥ (W : Set G) ⊆ (↑((10 : ℕ) • A) : Set G) ∧
      Module.finrank K G ≤ Module.finrank K W + (Module.finrank K V + 2) ^ 2 / 8 := by
  classical
  obtain ⟨W, t, hw, hd⟩ := quadratic_graph_coset f B hf
  let e := U.prodEquivOfIsCompl V hc
  have hgraph : (graph f).image e = Green50Graphs.graph U V f := by
    rw [graph, Green50Graphs.graph, image_image]
    rfl
  have embedded : ((5 : ℕ) • graph f).image e ⊆ (10 : ℕ) • A := by
    rw [image_nsmul, hgraph]
    simpa only [← two_nsmul, ← mul_smul, show (5 : ℕ) * 2 = 10 by decide] using
      (nsmul_subset_nsmul_left (n := 5) hg)
  refine ⟨W.map e.toLinearMap, e t, ?_, ?_⟩
  · rintro _ ⟨_, ⟨w, hwW, rfl⟩, rfl⟩
    exact embedded (show e t + e w ∈ _ by
      rw [← map_add]
      exact mem_image_of_mem _ (hw w hwW))
  · rw [← e.finrank_eq, ← (W.equivMapOfInjective e.toLinearMap e.injective).finrank_eq]
    exact hd

omit [Fintype V] in
/-- The zero map attains codimension equal to the output dimension in every positive sumset. -/
theorem zero_map_dimension (k : ℕ) (W : Submodule K (U × V)) (t : U × V)
    (h : ∀ w ∈ W, t + w ∈ k • graph (fun _ : U => (0 : V))) :
    Module.finrank K W ≤ Module.finrank K U := by
  classical
  let fst := (LinearMap.fst K U V).comp W.subtype
  have zero_outputs (n : ℕ) (p : U × V) (hp : p ∈ n • graph (fun _ : U => (0 : V))) :
      p.2 = 0 := by
    induction n generalizing p with
    | zero =>
      simpa using congrArg Prod.snd (show p = 0 by simpa using hp)
    | succ n ih =>
      rw [succ_nsmul, mem_add] at hp
      obtain ⟨a, ha, b, hb, rfl⟩ := hp
      obtain ⟨x, _, rfl⟩ := mem_image.mp hb
      exact (add_zero _).trans (ih a ha)
  have ht : t.2 = 0 := zero_outputs k t (by simpa using h 0 W.zero_mem)
  have hz (w : W) : w.val.2 = 0 := by
    have hh := zero_outputs k (t + w.val) (h w w.property)
    change t.2 + w.val.2 = 0 at hh
    simpa [ht] using hh
  apply LinearMap.finrank_le_finrank_of_injective (f := fst)
  intro x y he
  exact Subtype.ext (Prod.ext he ((hz x).trans (hz y).symm))

section Products
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D E : ι → Type*}
  [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)] [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)] [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

/-- Five sums of independent quadratic graphs pay the sum of the individual codimension costs. -/
theorem product_quadratic_coset (f : ∀ i, D i → E i) (B : ∀ i, D i →ₗ[K] D i →ₗ[K] E i)
    (hf : ∀ i a x, f i x + f i (x + a) = B i a x + (f i 0 + f i a)) :
    ∃ (H : Submodule K (∀ i, D i × E i)) (v : ∀ i, D i × E i),
      (∀ w ∈ H, v + w ∈ (5 : ℕ) • Fintype.piFinset (fun i => graph (f i))) ∧
      Module.finrank K (∀ i, D i × E i) ≤ Module.finrank K H +
        ∑ i, (Module.finrank K (E i) + 2) ^ 2 / 8 := by
  classical
  choose W t hw dim using fun i => quadratic_graph_coset (f i) (B i) (hf i)
  let e : (∀ i, W i) →ₗ[K] (∀ i, D i × E i) :=
    LinearMap.pi (fun i => (W i).subtype.comp (LinearMap.proj i))
  have he : Function.Injective e := fun x y h => funext (fun i => Subtype.ext (congrFun h i))
  have prod (k : ℕ) :
      (k + 1) • Fintype.piFinset (fun i => graph (f i)) =
        Fintype.piFinset (fun i => (k + 1) • graph (f i)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, ih, ← Fintype.piFinset_add]
      congr 1
  refine ⟨e.range, t, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    rw [show 5 = 4 + 1 by decide, prod]
    apply Fintype.mem_piFinset.mpr
    intro i
    exact hw i (z i) (z i).property
  · rw [LinearMap.finrank_range_of_inj he, Module.finrank_pi_fintype, Module.finrank_pi_fintype,
      ← sum_add_distrib]
    exact sum_le_sum fun i _ => dim i

/-- If every independent output block has at most four coordinates, the loss is at most the
total output dimension, uniformly in the number of blocks. -/
theorem four_coordinate_blocks (f : ∀ i, D i → E i) (B : ∀ i, D i →ₗ[K] D i →ₗ[K] E i)
    (hf : ∀ i a x, f i x + f i (x + a) = B i a x + (f i 0 + f i a))
    (hd : ∀ i, Module.finrank K (E i) ≤ 4) :
    ∃ (H : Submodule K (∀ i, D i × E i)) (v : ∀ i, D i × E i),
      (∀ w ∈ H, v + w ∈ (5 : ℕ) • Fintype.piFinset (fun i => graph (f i))) ∧
      Module.finrank K (∀ i, D i × E i) ≤ Module.finrank K H + ∑ i, Module.finrank K (E i) := by
  obtain ⟨H, v, hw, bound⟩ := product_quadratic_coset f B hf
  refine ⟨H, v, hw, bound.trans (Nat.add_le_add_left (sum_le_sum fun i _ => ?_) _)⟩
  generalize h : Module.finrank K (E i) = d
  have h4 := hd i
  rw [h] at h4
  interval_cases d <;> decide
end Products

end Green50QuadraticDescent

#print axioms Green50QuadraticDescent.cost_eq
#print axioms Green50QuadraticDescent.isotropic_half_rank
#print axioms Green50QuadraticDescent.quadratic_graph_coset
#print axioms Green50QuadraticDescent.tenfold_quadratic_coset
#print axioms Green50QuadraticDescent.product_quadratic_coset
#print axioms Green50QuadraticDescent.four_coordinate_blocks
#print axioms Green50QuadraticDescent.zero_map_dimension
