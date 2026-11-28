import Green50QuadraticFibres
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Exact additive covering order of triangular binary quadratic graphs -/

open Finset
open scoped Pointwise
namespace Green50TriangularGraphs
open Green50QuadraticGraphs Green50QuadraticFibres
local notation "K" => ZMod 2

abbrev Input (t : ℕ) := (Fin t → K) × (Fin t → K)
abbrev Output (t : ℕ) := Matrix (Fin t) (Fin t) K

/-- The strict upper triangle records same-vector products; the rest records cross products. -/
def triangular {t : ℕ} (x : Input t) : Output t :=
  Matrix.of fun i j => if i < j then x.1 i * x.1 j else x.1 j * x.2 i

private def form {t : ℕ} : Input t →ₗ[K] Input t →ₗ[K] Output t :=
  LinearMap.mk₂ K (fun x y => Matrix.of fun i j =>
    if i < j then x.1 i * y.1 j + y.1 i * x.1 j
    else x.1 j * y.2 i + y.1 j * x.2 i)
    (by intros; ext i j; by_cases h : i < j <;> simp [h] <;> ring)
    (by intros; ext i j; by_cases h : i < j <;> simp [h] <;> ring)
    (by intros; ext i j; by_cases h : i < j <;> simp [h] <;> ring)
    (by intros; ext i j; by_cases h : i < j <;> simp [h] <;> ring)

private theorem polarizes {t : ℕ} (a x : Input t) :
    triangular x + triangular (x + a) = form a x + (triangular 0 + triangular a) := by
  ext i j
  by_cases h : i < j <;> simp [triangular, form, h] <;> ring_nf <;>
    simp [show (2 : K) = 0 by decide]

private def direction {t : ℕ} (l : Fin t) : Input t :=
  (fun i => if l = i then 1 else 0, 0)

private def partnerVector {t : ℕ} (v : Output t) (l : Fin t) : Input t :=
  (fun j => if l < j then v l j else 0, fun i => v i l)

private theorem direction_entry {t : ℕ} (v : Output t) (l i j : Fin t) :
    form (direction l) (partnerVector v l) i j = if l = min i j then v i j else 0 := by
  by_cases ij : i < j
  · rw [min_eq_left ij.le]
    by_cases li : l = i
    · subst l; simp [form, direction, partnerVector, ij]
    · by_cases lj : l = j
      · subst l; simp [form, direction, partnerVector, ij, ij.ne', not_lt.mpr ij.le]
      · simp [form, direction, partnerVector, ij, li, lj]
  · simp [form, direction, partnerVector, ij, min_eq_right (le_of_not_gt ij), ite_mul]
    split_ifs <;> subst_vars <;> rfl

private theorem partial_sum {r s : ℕ} (v : Output (r + s))
    (hv : ∀ i j : Fin s, v (Fin.natAdd r i) (Fin.natAdd r j) = 0) :
    ∃ x y : Fin r → Input (r + s), ∑ l, form (x l) (y l) = v := by
  refine ⟨fun l => direction (Fin.castAdd s l), fun l => partnerVector v (Fin.castAdd s l), ?_⟩
  ext i j
  simp only [Matrix.sum_apply, direction_entry]
  by_cases h : (min i j).val < r
  · let l : Fin r := ⟨(min i j).val, h⟩
    have hl : Fin.castAdd s l = min i j := Fin.ext rfl
    rw [sum_eq_single l]
    · rw [if_pos hl]
    · intro a _ ha; exact if_neg (fun eq => ha (Fin.castAdd_inj.mp (eq.trans hl.symm)))
    · simp
  · have hi : r ≤ i.val := le_trans (Nat.le_of_not_gt h) (show (min i j).val ≤ i.val from min_le_left i j)
    have hj : r ≤ j.val := le_trans (Nat.le_of_not_gt h) (show (min i j).val ≤ j.val from min_le_right i j)
    let a : Fin s := ⟨i.val - r, by have := i.isLt; omega⟩
    let b : Fin s := ⟨j.val - r, by have := j.isLt; omega⟩
    have ei : Fin.natAdd r a = i := Fin.ext (by change r + (i.val - r) = i.val; omega)
    have ej : Fin.natAdd r b = j := Fin.ext (by change r + (j.val - r) = j.val; omega)
    rw [← ei, ← ej, hv]
    simp

/-- Every input-output target is the sum of exactly 2t + 1 graph points. -/
theorem covers (t : ℕ) : (2 * t + 1) • graph (@triangular t) = univ := by
  rw [odd_sumset triangular form polarizes]
  apply eq_univ_of_forall
  rintro ⟨u, v⟩
  refine mem_add.mpr ⟨(u, triangular u), mem_image_of_mem _ (mem_univ u),
    (0, v - triangular u), (mem_vertical_sum form _ _).mpr
      (partial_sum (r := t) (s := 0) _ (fun i => Fin.elim0 i)), Prod.ext ?_ ?_⟩
  · exact add_zero _
  · change triangular u + (v - triangular u) = v
    abel

private def pairing {k : ℕ} (a b : Input k) : K :=
  ∑ l, (a.1 l * b.2 l + a.2 l * b.1 l)

private theorem pairing_comm {k : ℕ} (a b : Input k) : pairing a b = pairing b a := by
  unfold pairing
  apply sum_congr rfl
  intro l _
  ring

private theorem pairing_self {k : ℕ} (a : Input k) : pairing a a = 0 := by
  apply sum_eq_zero
  intro l _
  rw [mul_comm (a.2 l), ← two_mul, show (2 : K) = 0 by decide, zero_mul]

/-- An isotropic family with triangular mixed products needs at least t hyperbolic planes. -/
private theorem pairing_width {t k : ℕ} (a b : Fin t → Input k)
    (haa : ∀ i j, pairing (a i) (a j) = 0)
    (hab : ∀ i j, i ≤ j → pairing (a i) (b j) = if i = j then 1 else 0) : t ≤ k := by
  classical
  let u := Sum.elim b a
  let v := Sum.elim a b
  let X : Matrix (Fin t ⊕ Fin t) (Fin k ⊕ Fin k) K :=
    Matrix.of fun i => Sum.elim (u i).1 (u i).2
  let Y : Matrix (Fin k ⊕ Fin k) (Fin t ⊕ Fin t) K :=
    Matrix.of fun l j => Sum.elim (v j).2 (v j).1 l
  let C : Output t := Matrix.of fun i j => pairing (a i) (b j)
  let D : Output t := Matrix.of fun i j => pairing (b i) (b j)
  have hentry (i j) : (X * Y) i j = pairing (u i) (v j) := by
    simp [Matrix.mul_apply, X, Y, Fintype.sum_sum_type, pairing, sum_add_distrib]
  have blocks : X * Y = Matrix.fromBlocks C.transpose D 0 C := by
    ext i j
    rw [hentry]
    cases i <;> cases j <;> simp [u, v, C, D, haa, pairing_comm]
  have tri : C.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    exact (hab i j hij.le).trans (if_neg hij.ne)
  have diag (i) : C i i = 1 := by simpa [C] using hab i i le_rfl
  have hdet : C.det = 1 := by rw [Matrix.det_of_isLowerTriangular C tri]; simp [diag]
  have full : IsUnit (X * Y) := by
    rw [Matrix.isUnit_iff_isUnit_det, blocks, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_transpose, hdet, one_mul]
    exact isUnit_one
  have h := (Matrix.rank_mul_le_left X Y).trans (Matrix.rank_le_card_width X)
  rw [Matrix.rank_of_isUnit _ full] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

private theorem one_requires {t k : ℕ} (x y : Fin k → Input t)
    (h : ∑ l, form (x l) (y l) = (1 : Output t)) : t ≤ k := by
  let a (i : Fin t) : Input k := (fun l => (x l).1 i, fun l => (y l).1 i)
  let b (i : Fin t) : Input k := (fun l => (x l).2 i, fun l => (y l).2 i)
  have entry (i j : Fin t) := congrArg (fun m : Output t => m i j) h
  have upper (i j : Fin t) (ij : i < j) : pairing (a i) (a j) = 0 := by
    simpa [pairing, a, form, Matrix.sum_apply, ij, Matrix.one_apply, ij.ne] using entry i j
  apply pairing_width a b
  · intro i j
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact upper i j hlt
    · exact pairing_self _
    · rw [pairing_comm]; exact upper j i hgt
  · intro i j ij
    simpa [pairing, a, b, form, Matrix.sum_apply, not_lt.mpr ij, Matrix.one_apply, eq_comm] using entry j i

/-- The zero-input identity-matrix target still fails with only 2t summands. -/
theorem identity_missing {t : ℕ} (ht : 0 < t) :
    ((0 : Input t), (1 : Output t)) ∉ (2 * t) • graph triangular := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, even_zero_fibre triangular form polarizes, mem_vertical_sum]
  rintro ⟨x, y, h⟩
  have := one_requires x y h
  omega

/-- The entire ambient group is attained precisely from order 2t + 1 onward. -/
theorem covers_iff {t : ℕ} (ht : 0 < t) (n : ℕ) :
    n • graph (@triangular t) = univ ↔ 2 * t + 1 ≤ n := by
  have hzero : (0 : Input t × Output t) ∈ graph triangular := by
    refine mem_image.mpr ⟨0, mem_univ _, ?_⟩
    apply Prod.ext
    · rfl
    · change triangular (0 : Input t) = 0
      ext i j; simp [triangular]
  have mono : Monotone (fun m : ℕ => m • graph (@triangular t)) := by
    apply monotone_nat_of_le_succ
    intro m p hp
    rw [succ_nsmul]
    exact mem_add.mpr ⟨p, hp, 0, hzero, add_zero _⟩
  constructor
  · intro h
    by_contra! hn
    have hmem : ((0 : Input t), (1 : Output t)) ∈ n • graph triangular := by rw [h]; exact mem_univ _
    exact identity_missing ht (mono (show n ≤ 2 * t by omega) hmem)
  · intro hn
    apply eq_univ_of_forall
    intro p
    apply mono hn
    change p ∈ (2 * t + 1) • graph (@triangular t)
    rw [covers]
    exact mem_univ _

/-- Forget the first r coordinates and read the remaining first input vector and output block. -/
private def restriction (r s : ℕ) : (Input (r + s) × Output (r + s)) →ₗ[K] ((Fin s → K) × Output s) where
  toFun p := (fun i => p.1.1 (Fin.natAdd r i), Matrix.of fun i j => p.2 (Fin.natAdd r i) (Fin.natAdd r j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def extend {s : ℕ} {A : Type*} [Zero A] (r : ℕ) (f : Fin s → A) : Fin (r + s) → A :=
  Fin.addCases (fun _ => 0) f

private theorem extension_last {r s : ℕ} {A : Type*} [Zero A] (f : Fin s → A) (i : Fin s) :
    extend r f (Fin.natAdd r i) = f i := Fin.addCases_right i

private theorem restriction_surj (r s : ℕ) : Function.Surjective (restriction r s) := by
  rintro ⟨x, v⟩
  refine ⟨((extend r x, 0), Matrix.of (extend r (fun i => extend r (v i)))), ?_⟩
  apply Prod.ext
  · funext i; exact extension_last x i
  · ext i j
    change extend r (fun i => extend r (v i)) (Fin.natAdd r i) (Fin.natAdd r j) = v i j
    rw [extension_last, extension_last]

/-- With t=r + s, 2r + 1 summands contain a linear subspace of codimension s(s+1). -/
theorem subspace (r s : ℕ) :
    ∃ H : Submodule K (Input (r + s) × Output (r + s)),
      Module.finrank K ((Input (r + s) × Output (r + s)) ⧸ H) = s * (s + 1) ∧
      ∀ p ∈ H, p ∈ (2 * r + 1) • graph (@triangular (r + s)) := by
  refine ⟨(restriction r s).ker, ?_, ?_⟩
  · have h := (LinearMap.quotKerEquivOfSurjective _ (restriction_surj r s)).finrank_eq
    rw [h, Module.finrank_prod, Module.finrank_matrix, Module.finrank_pi, Module.finrank_self]
    simp; ring
  · rintro ⟨u, v⟩ hp
    have h : restriction r s (u,v) = 0 := hp
    have h₁ (i : Fin s) : u.1 (Fin.natAdd r i) = 0 := congrArg (fun p => p.1 i) h
    have h₂ (i j : Fin s) : v (Fin.natAdd r i) (Fin.natAdd r j) = 0 := congrArg (fun p => p.2 i j) h
    have hc (i j : Fin s) : (v - triangular u) (Fin.natAdd r i) (Fin.natAdd r j) = 0 := by
      simp [triangular, h₁, h₂]
    rw [odd_sumset triangular form polarizes]
    exact mem_add.mpr ⟨(u,triangular u), mem_image_of_mem _ (mem_univ u), (0, v - triangular u),
      (mem_vertical_sum form _ _).mpr (partial_sum _ hc), Prod.ext (add_zero _)
        (show triangular u + (v - triangular u) = v by abel)⟩

end Green50TriangularGraphs

#print axioms Green50TriangularGraphs.covers
#print axioms Green50TriangularGraphs.identity_missing
#print axioms Green50TriangularGraphs.covers_iff

#print axioms Green50TriangularGraphs.subspace
