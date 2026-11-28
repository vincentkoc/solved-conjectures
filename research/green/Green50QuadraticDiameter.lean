import Green50SymplecticSpaces
import Green50QuadraticFibres

/-! # Representing values by a sum of alternating bilinear products -/

open Finset
open scoped Pointwise

namespace Green50QuadraticDiameter

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

private abbrev PairIndex (ι : Type*) [LT ι] := {p : ι × ι // p.1 < p.2}
private abbrev E (K ι : Type*) := ι → K

private def basisVector (i : ι) : E K ι := Pi.single i 1

private def wedge (a b : Module.Dual K (E K ι)) : LinearMap.BilinForm K (E K ι) :=
  a.smulRight b - b.smulRight a

omit [Fintype ι] [LinearOrder ι] in
private theorem wedge_apply (a b : Module.Dual K (E K ι)) (x y) :
    wedge a b x y = a x * b y - b x * a y := rfl

private def encode : (PairIndex ι → K) →ₗ[K] LinearMap.BilinForm K (E K ι) :=
  ∑ p : PairIndex ι, (LinearMap.proj p).smulRight
    (wedge (LinearMap.proj p.val.1) (LinearMap.proj p.val.2))

private theorem encode_alt (c : PairIndex ι → K) : (encode c).IsAlt := by
  intro x
  simp [encode, LinearMap.sum_apply, wedge_apply, mul_comm]

private theorem encode_entry (c : PairIndex ι → K) (p : PairIndex ι) :
    encode c (basisVector p.val.1) (basisVector p.val.2) = c p := by
  simp only [encode, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
    LinearMap.smul_apply, smul_eq_mul, wedge_apply, basisVector, Pi.single_apply]
  rw [sum_eq_single p]
  · simp [p.property.ne, p.property.ne']
  · rintro ⟨⟨i, j⟩, ij⟩ _ h
    have h₁ : ¬(i = p.val.1 ∧ j = p.val.2) := by rintro ⟨rfl, rfl⟩; exact h rfl
    have h₂ : ¬(j = p.val.1 ∧ i = p.val.2) := by rintro ⟨rfl, rfl⟩; exact ij.asymm p.property
    dsimp only
    split_ifs <;> simp_all
  · simp

private theorem encode_injective : Function.Injective (@encode K _ ι _ _) := by
  intro a b he; funext p
  rw [← encode_entry a p, ← encode_entry b p, he]

private theorem card_pairs : Fintype.card (PairIndex ι) = (Fintype.card ι).choose 2 := by
  rw [Fintype.card_subtype]
  simpa only [univ_product_univ, card_univ] using
    (card_product_filter_lt (s := (univ : Finset ι)))

private def evaluate (B : U →ₗ[K] U →ₗ[K] V) (P : ι → U) :
    LinearMap.BilinForm K (E K ι) →ₗ[K] V :=
  ∑ p : PairIndex ι, (((LinearMap.applyₗ (R := K) (basisVector p.val.2)).comp
    (LinearMap.applyₗ (R := K) (basisVector p.val.1))).smulRight (B (P p.val.1) (P p.val.2)))

private def realize (P : ι → U) (a : Module.Dual K (E K ι)) : U :=
  ∑ i, a (basisVector i) • P i

private theorem upper_sum {G : Type*} [AddCommMonoid G] (f : ι → ι → G) :
    (∑ p : PairIndex ι, f p.val.1 p.val.2) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
  let g (p : ι × ι) := f p.1 p.2
  have h := sum_subtype (F := (inferInstance : Fintype (PairIndex ι)))
    (p := fun p : ι × ι => p.1 < p.2) (univ.filter fun p : ι × ι => p.1 < p.2) (by simp) g
  change (∑ p : PairIndex ι, g p.val) = _
  rw [← h, sum_filter, Fintype.sum_prod_type]

private theorem evaluate_wedge (B : U →ₗ[K] U →ₗ[K] V) (hB : ∀ u, B u u = 0) (P : ι → U)
    (a b : Module.Dual K (E K ι)) : evaluate B P (wedge a b) = B (realize P a) (realize P b) := by
  have swap (i j : ι) : -B (P i) (P j) = B (P j) (P i) := by
    have he := hB (P i + P j)
    simp [map_add, hB] at he
    exact neg_eq_of_add_eq_zero_left he
  let f i j := (a (basisVector i) * b (basisVector j)) • B (P i) (P j)
  have hdiag i : f i i = 0 := by simp [f, hB]
  have hsum : (∑ i, ∑ j, f i j) = B (realize P a) (realize P b) := by
    simp [f, realize, map_sum, Finset.sum_apply, Finset.smul_sum, smul_smul]
    rw [sum_comm]; simp [mul_comm]
  rw [← hsum]
  simp only [evaluate, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
    LinearMap.applyₗ_apply_apply, wedge_apply]
  have term (i j : ι) :
      (a (basisVector i) * b (basisVector j) - b (basisVector i) * a (basisVector j)) • B (P i) (P j)
      = f i j + f j i := by
    rw [sub_smul, sub_eq_add_neg, ←smul_neg, swap, mul_comm (b _)]
  simp_rw [term]
  rw [upper_sum (fun i j => f i j + f j i)]
  have split (i j : ι) : (if i < j then f i j + f j i else 0) =
      (if i < j then f i j else 0) + (if i < j then f j i else 0) := by split_ifs <;> simp
  simp_rw [split, sum_add_distrib]
  conv_lhs => rhs; rw [sum_comm]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.asymm]
  · simp [hdiag]
  · simp [h, h.asymm]

/-- A representation with exactly m values of the bilinear map. -/
def Represented (B : U →ₗ[K] U →ₗ[K] V) (m : ℕ) (v : V) : Prop :=
  ∃ x y : Fin m → U, ∑ i, B (x i) (y i) = v

private theorem realize_coordinate (P : ι → U) (i : ι) :
    realize P (LinearMap.proj i : Module.Dual K (E K ι)) = P i := by
  simp [realize, basisVector, Pi.single_apply, ite_smul]

private theorem evaluation_rep (B : U →ₗ[K] U →ₗ[K] V) (hB : ∀ u, B u u = 0) (P : ι → U)
    (F : LinearMap.BilinForm K (E K ι)) (m : ℕ) (a b : Fin m → Module.Dual K (E K ι))
    (hab : ∀ x y, F x y = ∑ i, (a i x * b i y - b i x * a i y)) :
    Represented B m (evaluate B P F) := by
  have he : F = ∑ i, wedge (a i) (b i) := by
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    simpa only [LinearMap.sum_apply, wedge_apply] using hab x y
  refine ⟨fun i => realize P (a i), fun i => realize P (b i), ?_⟩
  rw [he, map_sum]
  simp_rw [evaluate_wedge B hB]

/-- The output directions generated by the values of the bilinear map. -/
def valueSpan (B : U →ₗ[K] U →ₗ[K] V) : Submodule K V :=
  Submodule.span K (Set.range fun p : U × U => B p.1 p.2)

private theorem evaluate_mem (B : U →ₗ[K] U →ₗ[K] V) (P : ι → U)
    (F : LinearMap.BilinForm K (E K ι)) : evaluate B P F ∈ valueSpan B := by
  simp only [evaluate, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
    LinearMap.applyₗ_apply_apply]
  exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨(P p.val.1, P p.val.2), rfl⟩))

/-- The square of the minimum representation length is at most the dimension spanned by the outputs. -/
theorem length_square_le [Fintype K] [FiniteDimensional K V] (B : U →ₗ[K] U →ₗ[K] V)
    (hB : ∀ u, B u u = 0) {v : V} {k : ℕ} (hk : Represented B k v)
    (hmin : ∀ m, Represented B m v → k ≤ m) : k * k ≤ Module.finrank K (valueSpan B) := by
  classical
  obtain ⟨x, y, hxy⟩ := hk
  let I := Fin (k + k)
  let P : I → U := Fin.addCases x y
  let a (i : Fin k) : Module.Dual K (E K I) := LinearMap.proj (Fin.castAdd k i)
  let b (i : Fin k) : Module.Dual K (E K I) := LinearMap.proj (Fin.natAdd k i)
  let J : LinearMap.BilinForm K (E K I) := ∑ i, wedge (a i) (b i)
  have hJ : J.IsAlt := by
    intro u
    simp [J, LinearMap.sum_apply, wedge_apply, mul_comm]
  let L := evaluate B P
  have hv : L J = v := by
    dsimp only [L, J]
    rw [map_sum]
    simp_rw [evaluate_wedge B hB]
    simpa only [a, b, realize_coordinate, P, Fin.addCases_left, Fin.addCases_right] using hxy
  let C := (L.comp encode).ker
  let emb := (encode (K := K) (ι := I)).comp C.subtype
  have hei : Function.Injective emb := encode_injective.comp Subtype.val_injective
  have hT : ∀ A ∈ emb.range, A.IsAlt := by
    rintro _ ⟨c, rfl⟩
    exact encode_alt c.val
  have hd : Module.finrank K (E K I) = 2 * k := by simp [E, I]; omega
  have hs : ∀ A ∈ emb.range, Function.Injective (J + A) := by
    rintro _ ⟨c, rfl⟩
    have heval : L (J + emb c) = v := by
      rw [map_add, hv, show L (emb c) = 0 from c.property, add_zero]
    obtain ⟨m, hm, hfull, p, q, hrep⟩ := Green50SymplecticSpaces.alternating_decomposition K (2 * k)
      (J + emb c) (hJ.add (encode_alt c.val)) hd
    have small := evaluation_rep B hB P _ m p q hrep
    change Represented B m (L (J + emb c)) at small
    rw [heval] at small
    exact hfull (by have := hmin m small; omega)
  have hbound := Green50SymplecticSpaces.dimension_bound K k J emb.range hJ hT hs hd
  rw [LinearMap.finrank_range_of_inj hei] at hbound
  let cost := L.comp (encode (K := K) (ι := I))
  have hbudget := cost.finrank_range_add_finrank_ker
  have hrank := Submodule.finrank_mono (show cost.range ≤ valueSpan B by
    rintro _ ⟨c, rfl⟩; exact evaluate_mem B P (encode c))
  change Module.finrank K cost.ker ≤ k * (k-1) at hbound
  rw [Module.finrank_pi, card_pairs] at hbudget
  simp only [I, Fintype.card_fin] at hbudget
  have arith : (k + k).choose 2 = k * k + k * (k-1) := by
    rw [Nat.choose_two_right]
    cases k with
    | zero => decide
    | succ k =>
      simp only [Nat.succ_sub_one]
      exact Nat.div_eq_of_eq_mul_left (by decide) (by simp; ring)
  have total : (k + k).choose 2 ≤ Module.finrank K (valueSpan B) + k * (k-1) :=
    hbudget ▸ Nat.add_le_add hrank hbound
  omega

private theorem represented_add (B : U →ₗ[K] U →ₗ[K] V) {p q : ℕ} {u v : V}
    (hu : Represented B p u) (hv : Represented B q v) : Represented B (p + q) (u + v) := by
  obtain ⟨a, b, ha⟩ := hu
  obtain ⟨c, d, hc⟩ := hv
  refine ⟨Fin.addCases a c, Fin.addCases b d, ?_⟩
  simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, ha, hc]

private theorem represented_pad (B : U →ₗ[K] U →ₗ[K] V) {p q : ℕ} {v : V}
    (hp : Represented B p v) (hpq : p ≤ q) : Represented B q v := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hpq
  have hz : Represented B r 0 := ⟨0, 0, by simp⟩
  simpa only [add_zero] using represented_add B hp hz

/-- Every vector in the span has a representation of length at most the square root of
the span dimension. Zero products pad all representations to that same length. -/
theorem span_iff_represented [Fintype K] [FiniteDimensional K V] (B : U →ₗ[K] U →ₗ[K] V)
    (hB : ∀ u, B u u = 0) (v : V) :
    v ∈ valueSpan B ↔ Represented B (Module.finrank K (valueSpan B)).sqrt v := by
  classical
  constructor
  · intro hv
    have hex : ∃ p, Represented B p v := by
      change v ∈ Submodule.span K _ at hv
      induction hv using Submodule.span_induction with
      | mem v h =>
        obtain ⟨⟨x, y⟩, rfl⟩ := h
        exact ⟨1, fun _ => x, fun _ => y, by simp⟩
      | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
      | add v w _ _ ih jh =>
        obtain ⟨p, hp⟩ := ih
        obtain ⟨q, hq⟩ := jh
        exact ⟨p + q, represented_add B hp hq⟩
      | smul c v _ ih =>
        obtain ⟨p, x, y, he⟩ := ih
        refine ⟨p, fun i => c • x i, y, ?_⟩
        simp [← he, Finset.smul_sum]
    have h := Nat.find_spec hex
    exact represented_pad B h (Nat.le_sqrt.mpr (length_square_le B hB h (fun m => Nat.find_min' hex)))
  · rintro ⟨x, y, rfl⟩
    exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨(x i, y i), rfl⟩)

/-- A shortest sum of k polar products also needs at least 2k input dimensions,
over any field. -/
theorem length_twice_le_input [FiniteDimensional K U] (B : U →ₗ[K] U →ₗ[K] V)
    (hB : ∀ x, B x x = 0) {v : V} {k : ℕ} (h : Represented B k v)
    (least : ∀ m, Represented B m v → k ≤ m) : 2 * k ≤ Module.finrank K U := by
  classical
  let n := Module.finrank K U
  let p := Module.finBasis K U
  let coeff (x : U) : Module.Dual K (E K (Fin n)) :=
    ∑ i, (p.repr x i) • (LinearMap.proj i : Module.Dual K (E K (Fin n)))
  have realize_coeff (x : U) : realize p (coeff x) = x := by
    change ∑ i, (coeff x) (basisVector i) • p i = x
    simp [coeff, basisVector, LinearMap.sum_apply, Pi.single_apply]
  obtain ⟨x, y, hxy⟩ := h
  let F := ∑ i, wedge (coeff (x i)) (coeff (y i))
  have ha : F.IsAlt := by intro z; simp [F, LinearMap.sum_apply, wedge_apply, mul_comm]
  have he : evaluate B p F = v := by
    dsimp only [F]
    rw [map_sum]
    simp only [evaluate_wedge B hB, realize_coeff, hxy]
  obtain ⟨m, hm, _, a, b, hab⟩ := Green50SymplecticSpaces.alternating_decomposition K n F ha
    (by simp [E])
  have hrep := evaluation_rep B hB p F m a b hab
  rw [he] at hrep
  have := least m hrep
  omega

/-- The smaller of half the input dimension and the square root of the polar span dimension
suffices for every output in the span. -/
theorem span_iff_radius [Fintype K] [FiniteDimensional K U] [FiniteDimensional K V]
    (B : U →ₗ[K] U →ₗ[K] V) (hB : ∀ u, B u u = 0) (r : ℕ)
    (hr : min (Module.finrank K U / 2) (Module.finrank K (valueSpan B)).sqrt ≤ r) (v : V) :
    v ∈ valueSpan B ↔ Represented B r v := by
  classical
  constructor
  · intro hv
    have hex : ∃ m, Represented B m v := ⟨_, (span_iff_represented B hB v).mp hv⟩
    have least := Nat.find_spec hex
    have lower (m : ℕ) (hm : Represented B m v) : Nat.find hex ≤ m := Nat.find_min' hex hm
    have byInput := length_twice_le_input B hB least lower
    have byOutput := Nat.le_sqrt.mpr (length_square_le B hB least lower)
    exact represented_pad B least (le_trans (le_min (by omega) byOutput) hr)
  · rintro ⟨x, y, rfl⟩
    exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨(x i, y i), rfl⟩)


/-- The polar span on n inputs has dimension at most n choose two. -/
theorem value_span_le_pairs [FiniteDimensional K U] [FiniteDimensional K V]
    (B : U →ₗ[K] U →ₗ[K] V) (hB : ∀ x, B x x = 0) :
    Module.finrank K (valueSpan B) ≤ (Module.finrank K U).choose 2 := by
  classical
  let b := Module.finBasis K U
  let v (p : PairIndex (Fin (Module.finrank K U))) := B (b p.val.1) (b p.val.2)
  let W := Submodule.span K (Set.range v)
  have swap (x y : U) : -B x y = B y x := by
    have h := hB (x + y)
    simp [hB] at h
    exact neg_eq_of_add_eq_zero_left (by simpa only [add_comm] using h)
  have basis_mem i j : B (b i) (b j) ∈ W := by
    rcases lt_trichotomy i j with h | rfl | h
    · exact Submodule.subset_span ⟨⟨(i, j), h⟩, rfl⟩
    · rw [hB]; exact W.zero_mem
    · rw [← swap (b j) (b i)]
      exact W.neg_mem (Submodule.subset_span ⟨⟨(j, i), h⟩, rfl⟩)
  have incl : valueSpan B ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change B x y ∈ W
    have left (j) : B x (b j) ∈ W := by
      rw [← b.sum_repr x]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
      exact W.sum_mem fun i _ => W.smul_mem _ (basis_mem i j)
    rw [← b.sum_repr y, map_sum]
    apply W.sum_mem
    intro j _
    rw [map_smul]
    exact W.smul_mem _ (left j)
  have hw : Module.finrank K W ≤ Fintype.card (PairIndex (Fin (Module.finrank K U))) :=
    finrank_range_le_card (R := K) v
  have bound := (Submodule.finrank_mono incl).trans hw
  simpa only [card_pairs, Fintype.card_fin] using bound

section Binary
open Green50QuadraticGraphs Green50QuadraticFibres
variable {D E' : Type*} [AddCommGroup D] [Module (ZMod 2) D] [Fintype D] [DecidableEq D]
  [AddCommGroup E'] [Module (ZMod 2) E'] [Fintype E'] [DecidableEq E']
local notation "F₂" => ZMod 2

private theorem add_self_zero {G : Type*} [AddCommGroup G] [Module F₂ G] (x : G) : x + x = 0 := by
  rw [← two_smul F₂ x, show (2:F₂) = 0 by decide, zero_smul]

private theorem neg_self {G : Type*} [AddCommGroup G] [Module F₂ G] (x : G) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self_zero x)

omit [Fintype D] [DecidableEq D] [DecidableEq E'] in
private theorem polar_alt (f : D → E') (B : D →ₗ[F₂] D →ₗ[F₂] E')
    (hf : ∀ a x : D, f x + f (x + a) = B a x + (f 0 + f a)) (x : D) : B x x = 0 := by
  have he := hf x x
  rw [add_self_zero, add_comm (f 0), eq_comm] at he
  exact add_right_cancel (he.trans (zero_add _).symm)

/-- Once either dimension bound holds, each odd sumset contains exactly one coset
of the value span above each input. -/
theorem graph_fibre_of_radius (f : D → E') (B : D →ₗ[F₂] D →ₗ[F₂] E')
    (hf : ∀ a x : D, f x + f (x + a) = B a x + (f 0 + f a)) {r : ℕ}
    (hr : min (Module.finrank F₂ D / 2) (Module.finrank F₂ (valueSpan B)).sqrt ≤ r) (u : D) (v : E') :
    (u, v) ∈ (2 * r + 1) • graph f ↔ v-f u ∈ valueSpan B := by
  rw [odd_sumset f B hf, mem_add]
  constructor
  · rintro ⟨_, h, p, hp, he⟩
    obtain ⟨w, _, rfl⟩ := mem_image.mp h
    obtain ⟨a, b⟩ := p
    obtain rfl : a = 0 := vertical_fst B r (a, b) hp
    have hu : w = u := by simpa using congrArg Prod.fst he
    subst w
    have hb : b = v-f u := by
      have h := congrArg Prod.snd he
      change f u + b = v at h
      rw [← h]; abel
    subst b
    obtain ⟨x, y, eq⟩ := (mem_vertical_sum B r _).mp hp
    rw [← eq]
    exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨(x i, y i), rfl⟩)
  · intro h
    refine ⟨(u, f u), mem_image_of_mem _ (mem_univ u), (0, v-f u), ?_, Prod.ext (add_zero _) ?_⟩
    · exact (mem_vertical_sum B r _).mpr
        ((span_iff_radius B (polar_alt f B hf) r hr _).mp h)
    · change f u + (v-f u) = v; abel

/-- From the square-root threshold onward, each odd sumset contains exactly one coset
of the value span above each input. -/
theorem graph_fibre (f : D → E') (B : D →ₗ[F₂] D →ₗ[F₂] E')
    (hf : ∀ a x : D, f x + f (x + a) = B a x + (f 0 + f a)) {r : ℕ}
    (hr : (Module.finrank F₂ (valueSpan B)).sqrt ≤ r) (u : D) (v : E') :
    (u, v) ∈ (2 * r + 1) • graph f ↔ v-f u ∈ valueSpan B :=
  graph_fibre_of_radius f B hf ((min_le_right _ _).trans hr) u v

omit [Fintype D] [Fintype E'] in
private theorem odd_in_span (S : Finset (D × E')) (k : ℕ) :
    ∀ p ∈ (2 * k + 1) • S, p ∈ affineSpan F₂ (S : Set (D × E')) := by
  induction k with
  | zero =>
    intro p hp
    exact subset_affineSpan _ _ (by simpa using hp)
  | succ k ih =>
    intro p hp
    rw [show 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 by omega, succ_nsmul, succ_nsmul, mem_add] at hp
    obtain ⟨_, h, x, hx, rfl⟩ := hp
    obtain ⟨v, hv, y, hy, rfl⟩ := mem_add.mp h
    have h := (affineSpan F₂ (S : Set (D × E'))).smul_vsub_vadd_mem (1:F₂) (ih v hv)
      (subset_affineSpan _ _ hy) (subset_affineSpan _ _ hx)
    simpa only [one_smul, vsub_eq_sub, vadd_eq_add, sub_eq_add_neg, neg_self] using h

/-- The input dimension and the polar span dimension both bound the covering order. -/
theorem graph_affine_span_of_radius (f : D → E') (B : D →ₗ[F₂] D →ₗ[F₂] E')
    (hf : ∀ a x : D, f x + f (x + a) = B a x + (f 0 + f a)) {r : ℕ}
    (hr : min (Module.finrank F₂ D / 2) (Module.finrank F₂ (valueSpan B)).sqrt ≤ r) :
    (↑((2 * r + 1) • graph f) : Set (D × E')) = affineSpan F₂ (graph f : Set (D × E')) := by
  let n := 2 * r + 1
  let S := n • graph f
  have triple {p q z : D × E'} (hp : p ∈ S) (hq : q ∈ S) (hz : z ∈ S) : p + q + z ∈ S := by
    have hsum : p + q + z ∈ ((n + n) + n) • graph f := by
      rw [add_nsmul, add_nsmul]
      exact add_mem_add (add_mem_add hp hq) hz
    have he : n + n + n = 2 * (3 * r + 1) + 1 := by dsimp [n]; omega
    rw [he] at hsum
    exact (graph_fibre_of_radius f B hf hr _ _).mpr ((graph_fibre_of_radius f B hf (r := 3 * r + 1) (by omega) _ _).mp hsum)
  let H : AffineSubspace F₂ (D × E') :=
    { carrier := (S : Set _)
      smul_vsub_vadd_mem' := by
        intro c p q z hp hq hz
        have hc : c = 0 ∨ c = 1 := by fin_cases c <;> first | exact Or.inl rfl | exact Or.inr rfl
        rcases hc with rfl | rfl
        · simpa only [zero_smul, zero_vadd] using hz
        · simpa only [one_smul, vsub_eq_sub, vadd_eq_add, sub_eq_add_neg, neg_self, Finset.mem_coe] using triple hp hq hz }
  apply Set.Subset.antisymm (odd_in_span _ r)
  change affineSpan F₂ _ ≤ H
  apply affineSpan_le.mpr
  intro p hp
  obtain ⟨u, _, rfl⟩ := mem_image.mp hp
  exact (graph_fibre_of_radius f B hf hr _ _).mpr (by simp)

/-- Every binary quadratic graph fills its affine span in 2⌊√d⌋+1 summands, where d is
the dimension of the subspace spanned by its polarization. -/
theorem graph_affine_span (f : D → E') (B : D →ₗ[F₂] D →ₗ[F₂] E')
    (hf : ∀ a x : D, f x + f (x + a) = B a x + (f 0 + f a)) {r : ℕ}
    (hr : (Module.finrank F₂ (valueSpan B)).sqrt ≤ r) :
    (↑((2 * r + 1) • graph f) : Set (D × E')) = affineSpan F₂ (graph f : Set (D × E')) :=
  graph_affine_span_of_radius f B hf ((min_le_right _ _).trans hr)

private theorem binary_card (X : Type*) [AddCommGroup X] [Module F₂ X] [Fintype X] :
    Nat.card X = 2 ^ Module.finrank F₂ X := by
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F₂) (V := X), ZMod.card]

/-- The direction of the affine span has one dimension for each input direction and
one for each independent polar output. -/
theorem affine_span_dimension (f : D → E') (B : D →ₗ[F₂] D →ₗ[F₂] E')
    (hf : ∀ a x : D, f x + f (x + a) = B a x + (f 0 + f a)) :
    Module.finrank F₂ (affineSpan F₂ (graph f : Set (D × E'))).direction =
      Module.finrank F₂ D + Module.finrank F₂ (valueSpan B) := by
  classical
  let H := affineSpan F₂ (graph f : Set (D × E'))
  have mem (x : D) (y : E') : (x, y) ∈ H ↔ y - f x ∈ valueSpan B := by
    change (x, y) ∈ (↑(affineSpan F₂ (graph f : Set (D × E'))) : Set (D × E')) ↔ _
    rw [← graph_affine_span f B hf (r := (Module.finrank F₂ (valueSpan B)).sqrt) le_rfl]
    exact graph_fibre f B hf le_rfl x y
  let t : H := ⟨(0, f 0), (mem _ _).mpr (by simp)⟩
  let _ : Nonempty H := ⟨t⟩
  let e : H ≃ D × valueSpan B :=
    { toFun := fun p => (p.val.1, ⟨p.val.2-f p.val.1, (mem _ _).mp p.property⟩)
      invFun := fun ⟨x, y⟩ => ⟨(x, y.val + f x), (mem _ _).mpr (by simp)⟩
      left_inv := by rintro ⟨⟨x, y⟩, h⟩; simp
      right_inv := by rintro ⟨x, ⟨y, h⟩⟩; simp }
  have hc := Nat.card_congr ((Equiv.vaddConst t : H.direction ≃ H).trans e)
  rw [Nat.card_prod, binary_card H.direction, binary_card D, binary_card (valueSpan B), ← Nat.pow_add] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc

/-- Five summands fill the affine span if the polarization spans at most eight dimensions. -/
theorem fivefold_of_le_eight (f : D → E') (B : D →ₗ[F₂] D →ₗ[F₂] E')
    (hf : ∀ a x : D, f x + f (x + a) = B a x + (f 0 + f a))
    (hd : Module.finrank F₂ (valueSpan B) ≤ 8) :
    (↑((5 : ℕ) • graph f) : Set (D × E')) = affineSpan F₂ (graph f : Set (D × E')) := by
  apply graph_affine_span f B hf (r := 2)
  exact Nat.le_of_lt_succ (Nat.sqrt_lt.mpr (by omega))

/-- If A + A contains the graph, ten summands contain a coset of codimension exactly
the output dimension minus the dimension of the polar value span, when the latter is at most eight. -/
theorem tenfold_coset_of_le_eight {G : Type*} [AddCommGroup G] [Module F₂ G] [Fintype G]
    [DecidableEq G] (A : Finset G) (U V : Submodule F₂ G) (hc : IsCompl U V)
    (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hg : Green50Graphs.graph U V f ⊆ A + A)
    (hf : ∀ a x : U, f x + f (x + a) = B a x + (f 0 + f a))
    (hd : Module.finrank F₂ (valueSpan B) ≤ 8) :
    ∃ (W : Submodule F₂ G) (t : G), t +ᵥ (W : Set G) ⊆ (↑((10 : ℕ) • A) : Set G) ∧
      Module.finrank F₂ G + Module.finrank F₂ (valueSpan B) =
        Module.finrank F₂ W + Module.finrank F₂ V := by
  classical
  let H := affineSpan F₂ (graph f : Set (U × V))
  let e := U.prodEquivOfIsCompl V hc
  have hgraph : (graph f).image e = Green50Graphs.graph U V f := by
    rw [graph, Green50Graphs.graph, image_image]
    rfl
  have embedded : ((5 : ℕ) • graph f).image e ⊆ (10 : ℕ) • A := by
    rw [image_nsmul, hgraph]
    simpa only [← two_nsmul, ← mul_smul, show (5 : ℕ) * 2 = 10 by decide] using
      (nsmul_subset_nsmul_left (n := 5) hg)
  let t : U × V := (0, f 0)
  have ht : t ∈ H := subset_affineSpan _ _ (mem_image_of_mem _ (mem_univ 0))
  refine ⟨H.direction.map e.toLinearMap, e t, ?_, ?_⟩
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    apply embedded
    change e t + e w ∈ _
    rw [← map_add]
    apply mem_image_of_mem
    change t + w ∈ (↑((5 : ℕ) • graph f) : Set _)
    rw [fivefold_of_le_eight f B hf hd, add_comm]
    exact H.vadd_mem_of_mem_direction hw ht
  · rw [← e.finrank_eq, ← (H.direction.equivMapOfInjective e.toLinearMap e.injective).finrank_eq,
      Module.finrank_prod, show Module.finrank F₂ H.direction = _ from affine_span_dimension f B hf]
    omega

end Binary
end Green50QuadraticDiameter

#print axioms Green50QuadraticDiameter.length_square_le
#print axioms Green50QuadraticDiameter.span_iff_represented
#print axioms Green50QuadraticDiameter.graph_fibre
#print axioms Green50QuadraticDiameter.graph_affine_span
#print axioms Green50QuadraticDiameter.affine_span_dimension
#print axioms Green50QuadraticDiameter.fivefold_of_le_eight
#print axioms Green50QuadraticDiameter.tenfold_coset_of_le_eight
#print axioms Green50QuadraticDiameter.length_twice_le_input
#print axioms Green50QuadraticDiameter.span_iff_radius
#print axioms Green50QuadraticDiameter.graph_fibre_of_radius
#print axioms Green50QuadraticDiameter.graph_affine_span_of_radius
#print axioms Green50QuadraticDiameter.value_span_le_pairs
