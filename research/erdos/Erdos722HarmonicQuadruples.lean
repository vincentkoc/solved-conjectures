import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Harmonic quadruples over a field of characteristic three

On the projective line, a four-set is a block when the middle coefficient of
the product of its four linear forms vanishes. For a finite field of order
`3 ^ d` this realizes the classical Steiner quadruple system on `3 ^ d + 1`
points. See M. Huber, https://arxiv.org/abs/math/0401117.
-/

namespace Erdos722.Harmonic

open Finset Polynomial

variable {K V : Type*} [Field K]

private def num : Option K → K
  | none => 1
  | some a => a

private def den : Option K → K
  | none => 0
  | some _ => 1

/-- The affine point `a` contributes `C a + X`; infinity contributes `1`. -/
noncomputable def pointFactor (x : Option K) : K[X] := C (num x) + C (den x) * X

private theorem det_ne_zero {x y : Option K} (h : x ≠ y) :
    num x * den y - den x * num y ≠ 0 := by
  cases x <;> cases y <;> simp_all [num, den, sub_ne_zero]

private theorem coeff_succ (x : Option K) (P : K[X]) (n : ℕ) :
    (pointFactor x * P).coeff (n + 1) = num x * P.coeff (n + 1) + den x * P.coeff n := by
  simp only [pointFactor, add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul]

private theorem coeff_zero (x : Option K) (P : K[X]) :
    (pointFactor x * P).coeff 0 = num x * P.coeff 0 := by
  simp [pointFactor, add_mul, mul_assoc]

/-- A repeated point gives a product of two nonzero determinants. -/
private theorem repeated [CharP K 3] {x y z : Option K} (hxy : x ≠ y) (hxz : x ≠ z) :
    (pointFactor x * (pointFactor x * (pointFactor y * pointFactor z))).coeff 2 ≠ 0 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have hd := mul_ne_zero (det_ne_zero hxy) (det_ne_zero hxz)
  apply ne_of_eq_of_ne _ hd
  simp only [show (2 : ℕ) = 1 + 1 from rfl, coeff_succ, coeff_zero]
  norm_num [pointFactor, coeff_C_mul_X, coeff_C]
  linear_combination (num x * den x * (num y * den z + den y * num z)) * h3

private theorem unique_zero {A B : K} (h : A ≠ 0 ∨ B ≠ 0) :
    ∃! w : Option K, num w * A + den w * B = 0 := by
  by_cases hA : A = 0
  · have hB := h.resolve_left (not_not_intro hA)
    refine ⟨none, by simp [num, den, hA], ?_⟩
    rintro (_ | w) hw
    · rfl
    · simp [num, den, hA, hB] at hw
  · refine ⟨some (-B / A), ?_, ?_⟩
    · simp [num, den, hA]
    · rintro (_ | w) hw
      · simp [num, den, hA] at hw
      · simp only [num, den, one_mul] at hw
        exact congrArg some ((eq_div_iff hA).mpr (by linear_combination hw))

/-- Every triple on the projective line has a unique new point that makes
the middle coefficient vanish. The field may be infinite. -/
theorem existsUnique_completion [CharP K 3] (label : V ≃ Option K) (S : Finset V)
    (hS : S.card = 3) :
    ∃! w, w ∉ S ∧ (pointFactor (label w) * ∏ x ∈ S, pointFactor (label x)).coeff 2 = 0 := by
  classical
  let P := ∏ x ∈ S, pointFactor (label x)
  have fresh {x : V} (hx : x ∈ S) : (pointFactor (label x) * P).coeff 2 ≠ 0 := by
    obtain ⟨y, z, hyz, hpair⟩ := card_eq_two.mp
      (show (S.erase x).card = 2 by rw [card_erase_of_mem hx, hS])
    have hnot : x ∉ ({y, z} : Finset V) := hpair ▸ (notMem_erase x S)
    simp only [mem_insert, mem_singleton, not_or] at hnot
    have hp : P = pointFactor (label x) * (pointFactor (label y) * pointFactor (label z)) := by
      dsimp only [P]
      rw [← S.mul_prod_erase (fun v ↦ pointFactor (label v)) hx, hpair, prod_pair hyz]
    rw [hp]
    exact repeated (label.injective.ne hnot.1) (label.injective.ne hnot.2)
  have nonzero : P.coeff 2 ≠ 0 ∨ P.coeff 1 ≠ 0 := by
    by_contra! h
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < S.card)
    exact fresh hx (by rw [coeff_succ _ _ 1, h.1, h.2]; simp)
  obtain ⟨u, hu, unique⟩ := unique_zero nonzero
  have hu' : (pointFactor u * P).coeff 2 = 0 := (coeff_succ u P 1).trans hu
  refine ⟨label.symm u, ⟨fun hx ↦ fresh hx (by simpa using hu'), by simpa [P] using hu'⟩, ?_⟩
  rintro w ⟨_, hw⟩
  apply label.injective
  rw [label.apply_symm_apply]
  exact unique (label w) ((coeff_succ _ P 1).symm.trans hw)

/-- Four-sets cut out by the degree-two coefficient on the projective line. -/
noncomputable def blocks [Fintype V] (label : V ≃ Option K) : Finset (Finset V) := by
  classical
  exact univ.filter fun B ↦ B.card = 4 ∧ (∏ x ∈ B, pointFactor (label x)).coeff 2 = 0

theorem blocks_isBlockDesign [CharP K 3] [Fintype V] (label : V ≃ Option K) :
    (blocks label).IsBlockDesign 3 4 := by
  classical
  have mem_blocks (B : Finset V) :
      B ∈ blocks label ↔ B.card = 4 ∧ (∏ x ∈ B, pointFactor (label x)).coeff 2 = 0 := by
    simp [blocks]
  refine ⟨fun B hB ↦ ((mem_blocks B).mp hB).1, ?_⟩
  intro S hS
  obtain ⟨w, ⟨hf, hw⟩, unique⟩ := existsUnique_completion label S hS
  refine ⟨insert w S, ⟨(mem_blocks _).mpr ⟨by rw [card_insert_of_notMem hf, hS],
    by rwa [prod_insert hf]⟩, subset_insert _ _⟩, ?_⟩
  rintro B ⟨hB, hSB⟩
  obtain ⟨hcard, hzero⟩ := (mem_blocks _).mp hB
  obtain ⟨z, hz, rfl⟩ := exists_eq_insert_iff.mpr ⟨hSB, by rw [hS, hcard]⟩
  rw [prod_insert hz] at hzero
  rw [unique z ⟨hz, hzero⟩]

/-- The ternary projective construction gives the conclusion of Erdős 722 at
`r = 3`, `k = 4`, and every order `3 ^ d + 1` with positive `d`. -/
theorem exists_ternary_quadruple_design (d : ℕ) (hd : 0 < d) :
    ∃ H : Finset (Finset (Fin (3 ^ d + 1))), H.IsBlockDesign 3 4 := by
  classical
  let K := GaloisField 3 d
  let : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card (Option K) = 3 ^ d + 1 := by
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card]
    exact congrArg (· + 1) (GaloisField.card 3 d hd.ne')
  let label : Fin (3 ^ d + 1) ≃ Option K := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨blocks label, blocks_isBlockDesign label⟩

/-- Starting with order ten, every order in the ternary family lies outside
the binary construction. -/
theorem order_ne_power_of_two {d : ℕ} (hd : 2 ≤ d) (e : ℕ) : 3 ^ d + 1 ≠ 2 ^ e := by
  have residues (n : ℕ) : 3 ^ n % 8 = 1 ∨ 3 ^ n % 8 = 3 := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> decide
  have hlarge : 9 ≤ 3 ^ d := pow_le_pow_right' (by decide : 1 ≤ (3 : ℕ)) hd
  intro he
  have he3 : 3 ≤ e := by
    by_contra! hsmall
    have hle := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (show e ≤ 2 by omega)
    change 2 ^ e ≤ 4 at hle
    omega
  have h8 : 8 ∣ 3 ^ d + 1 := he ▸ pow_dvd_pow 2 he3
  rcases residues d with h | h <;> omega

/-- The construction supplies unbounded orders outside the binary family. -/
theorem arbitrarily_large_nonbinary_orders (N : ℕ) :
    ∃ n > N, (∀ e : ℕ, n ≠ 2 ^ e) ∧ ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 4 := by
  let d := N + 2
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hN : N < 3 ^ d + 1 := by
    have growth (k : ℕ) : k < 3 ^ k := by
      induction k with
      | zero => decide
      | succ k ih => rw [pow_succ]; omega
    have := growth d
    dsimp [d] at *
    omega
  exact ⟨_, hN, order_ne_power_of_two hd, exists_ternary_quadruple_design d (by omega)⟩

#print axioms existsUnique_completion
#print axioms blocks_isBlockDesign
#print axioms exists_ternary_quadruple_design
#print axioms order_ne_power_of_two
#print axioms arbitrarily_large_nonbinary_orders

end Erdos722.Harmonic
