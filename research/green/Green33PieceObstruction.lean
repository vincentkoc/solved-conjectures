import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Bounds on two-bases covered by finitely many sets with small self-sums. -/

open Finset Filter
open scoped Pointwise Topology

namespace Green33PieceObstruction

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

private lemma insert_piece (P U : Finset G) :
    ((P ∪ U) + (P ∪ U)).card ≤ (P + P).card + (U + U).card + P.card * U.card := by
  have h : (P ∪ U) + (P ∪ U) = ((P + P) ∪ (U + U)) ∪ (P + U) := by
    rw [union_add, add_union, add_union, add_comm U P]
    ext a; simp only [mem_union]; tauto
  rw [h]
  exact (card_union_le _ _).trans (Nat.add_le_add (card_union_le _ _) card_add_le)

private lemma union_sum_bound {ι : Type*} (s : Finset ι) (P : ι → Finset G) :
    2 * (s.biUnion P + s.biUnion P).card + ∑ i ∈ s, (P i).card^2 ≤
      (∑ i ∈ s, (P i).card)^2 + 2 * ∑ i ∈ s, (P i + P i).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [biUnion_insert, sum_insert hi]
    have hcard : (s.biUnion P).card ≤ ∑ j ∈ s, (P j).card := card_biUnion_le
    have h := insert_piece (P i) (s.biUnion P)
    nlinarith only [ih, h, Nat.mul_le_mul_left (P i).card hcard]

/-- Covering a basis by `r` sets costs at least this much total self-sumset size.
The covering sets may overlap and may extend beyond the basis. -/
theorem cover_count {r : ℕ} (A : Finset G) (P : Fin r → Finset G)
    (hcover : ∀ a ∈ A, ∃ i, a ∈ P i) :
    2 * r * (A + A).card + A.card^2 ≤ r * A.card^2 + 2 * r * ∑ i, (P i + P i).card := by
  classical
  by_cases h0 : r = 0
  · subst r
    have ha : A = ∅ := eq_empty_iff_forall_notMem.mpr (fun a ha =>
      let ⟨i, _⟩ := hcover a ha; Fin.elim0 i)
    simp [ha]
  have : NeZero r := ⟨h0⟩
  let color (a : G) : Fin r := if h : a ∈ A then (hcover a h).choose else 0
  let B (i : Fin r) := A.filter (fun a => color a = i)
  have hBA (i : Fin r) : B i ⊆ P i := by
    intro a ha
    have hm : a ∈ A := (mem_filter.mp ha).1
    have hi : color a = i := (mem_filter.mp ha).2
    rw [← hi]
    simpa only [color, dif_pos hm] using (hcover a hm).choose_spec
  have hparts : univ.biUnion B = A := by
    ext a
    simp [B]
  have hmass : ∑ i, (B i).card = A.card := by
    simpa [B] using sum_card_fiberwise_eq_card_filter A univ color
  have he := union_sum_bound univ B
  rw [hparts, hmass] at he
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin r))) (f := fun i => (B i).card)
  rw [hmass, card_univ, Fintype.card_fin] at hcs
  have hsmall : ∑ i, (B i + B i).card ≤ ∑ i, (P i + P i).card :=
    sum_le_sum fun i _ => card_le_card (add_subset_add (hBA i) (hBA i))
  nlinarith only [Nat.mul_le_mul_left r he, hcs, Nat.mul_le_mul_left r hsmall]

/-- The limiting lower bound for a fixed number of covering pieces whose
total self-sumset size is negligible compared with the modulus. -/
theorem limiting_piece_bound {ι : Type*} {l : Filter ι} [NeBot l] (r : ℕ)
    (q : ι → ℕ+) (A : (i : ι) → Finset (ZMod (q i)))
    (P : (i : ι) → Fin r → Finset (ZMod (q i)))
    (hA : ∀ i, A i + A i = univ) (hc : ∀ i a, a ∈ A i → ∃ j, a ∈ P i j)
    {L : ℝ} (hL : Tendsto (fun i => ((A i).card : ℝ) / Real.sqrt (q i)) l (𝓝 L))
    (hs : Tendsto (fun i => (∑ j, ((P i j + P i j).card : ℝ)) / (q i : ℝ)) l (𝓝 0)) :
    2 * (r : ℝ) ≤ (r - 1 : ℝ) * L ^ 2 := by
  let x (i : ι) : ℝ := (A i).card / Real.sqrt (q i)
  have h (i : ι) : 2 * (r : ℝ) + x i ^ 2 ≤
      r * x i ^ 2 + 2 * r * ((∑ j, ((P i j + P i j).card : ℝ)) / (q i : ℝ)) := by
    have hf := cover_count (A i) (P i) (hc i)
    rw [hA i, card_univ, ZMod.card] at hf
    have hh : 2 * (r : ℝ) * (q i : ℝ) + ((A i).card : ℝ)^2 ≤
        r * ((A i).card : ℝ)^2 + 2 * r * ∑ j, ((P i j + P i j).card : ℝ) := by exact_mod_cast hf
    have hpos : 0 < (q i : ℝ) := by exact_mod_cast (q i).pos
    dsimp only [x]
    rw [div_pow, Real.sq_sqrt hpos.le]
    field_simp [hpos.ne']
    linarith only [hh]
  have hx : Tendsto x l (𝓝 L) := hL
  have hl := le_of_tendsto_of_tendsto' (tendsto_const_nhds.add (hx.pow 2))
    (((hx.pow 2).const_mul (r : ℝ)).add (hs.const_mul (2 * (r : ℝ)))) h
  nlinarith only [hl]

/-- An arithmetic progression in an additive monoid, with repetitions removed. -/
def progression (a d : G) (n : ℕ) : Finset G :=
  (range n).image fun t => a + t • d

/-- Every self-sum is in a translate of the progression by its first or last term.
This also applies when the progression wraps around a finite cyclic group. -/
theorem progression_sum_le (a d : G) (n : ℕ) :
    (progression a d n + progression a d n).card ≤ 2 * (progression a d n).card := by
  let P := progression a d n
  let U (e : ℕ) := P.image fun x => (a + e • d) + x
  have h : P + P ⊆ U 0 ∪ U (n - 1) := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_add.mp hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have memP (t : ℕ) (ht : t < n) : a + t • d ∈ P :=
      mem_image_of_mem _ (mem_range.mpr ht)
    by_cases hij : i + j < n
    · apply mem_union_left
      exact mem_image.mpr ⟨_, memP _ hij, by simp [add_nsmul]; abel⟩
    · apply mem_union_right
      refine mem_image.mpr ⟨_, memP (i + j - (n - 1)) (by omega), ?_⟩
      calc
        _ = (a + a) + ((n - 1) + (i + j - (n - 1))) • d := by rw [add_nsmul]; abel
        _ = _ := by rw [show (n - 1) + (i + j - (n - 1)) = i + j by omega, add_nsmul]; abel
  calc
    (P + P).card ≤ (U 0 ∪ U (n - 1)).card := card_le_card h
    _ ≤ (U 0).card + (U (n - 1)).card := card_union_le _ _
    _ ≤ P.card + P.card := Nat.add_le_add card_image_le card_image_le
    _ = _ := by change P.card + P.card = 2 * P.card; omega

/-- A fixed number of progressions whose union is the basis forces the same
limiting bound. Neither disjointness nor injectivity of their parametrizations is required. -/
theorem progression_basis_bound {ι : Type*} {l : Filter ι} [NeBot l] (r : ℕ)
    (q : ι → ℕ+) (A : (i : ι) → Finset (ZMod (q i)))
    (a d : (i : ι) → Fin r → ZMod (q i)) (n : ι → Fin r → ℕ)
    (hA : ∀ i, A i + A i = univ) (hq : Tendsto (fun i => (q i : ℕ)) l atTop)
    (hP : ∀ i, A i = univ.biUnion (fun j => progression (a i j) (d i j) (n i j)))
    {L : ℝ} (hL : Tendsto (fun i => ((A i).card : ℝ) / Real.sqrt (q i)) l (𝓝 L)) :
    2 * (r : ℝ) ≤ (r - 1 : ℝ) * L ^ 2 := by
  let P (i : ι) (j : Fin r) := progression (a i j) (d i j) (n i j)
  apply limiting_piece_bound (l := l) r q A P hA
  · intro i x hx
    rw [hP i] at hx
    simpa only [mem_biUnion, mem_univ, true_and] using hx
  · exact hL
  · have hs := Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hq)
    have hsq (i : ι) : Real.sqrt (q i)^2 = (q i : ℝ) := Real.sq_sqrt (by positivity)
    have hlin : Tendsto (fun i => ((A i).card : ℝ) / (q i : ℝ)) l (𝓝 0) := by
      simpa only [Function.comp_apply, div_div, ← sq, hsq] using hL.div_atTop hs
    have hup : Tendsto (fun i => (2 * (r : ℝ)) * (((A i).card : ℝ) / (q i : ℝ))) l (𝓝 0) := by
      simpa only [mul_zero] using hlin.const_mul (2 * (r : ℝ))
    refine squeeze_zero (fun i => div_nonneg (sum_nonneg fun j _ => Nat.cast_nonneg _)
      (Nat.cast_nonneg _)) ?_ hup
    intro i
    have hc (j : Fin r) : (P i j).card ≤ (A i).card := by
      apply card_le_card
      rw [hP i]
      exact subset_biUnion_of_mem _ (mem_univ j)
    have hf (j : Fin r) : (P i j + P i j).card ≤ 2 * (A i).card :=
      (progression_sum_le _ _ _).trans (Nat.mul_le_mul_left 2 (hc j))
    have hh := sum_le_sum (s := univ) (fun j _ => hf j)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hh
    have hreal : (∑ j, ((P i j + P i j).card : ℝ)) ≤ r * (2 * ((A i).card : ℝ)) := by
      exact_mod_cast hh
    have hpos : 0 < (q i : ℝ) := by exact_mod_cast (q i).pos
    field_simp [hpos.ne']
    linarith only [hreal]

/-- At bounded additive slack, a cover with total self-sumset size at most `Kk`
must use linearly many pieces in the basis size `k`. -/
theorem pieces_of_bounded_slack [Fintype G] (A : Finset G) (hA : A + A = univ)
    {r : ℕ} (P : Fin r → Finset G) (hc : ∀ a ∈ A, ∃ i, a ∈ P i) (C K : ℕ)
    (hslack : A.card^2 ≤ 2 * Fintype.card G + C * A.card)
    (hcost : ∑ i, (P i + P i).card ≤ K * A.card) : A.card ≤ r * (C + 2 * K) := by
  have hf := cover_count A P hc
  rw [hA, card_univ] at hf
  by_cases hz : A.card = 0
  · simp [hz]
  · by_contra! h
    have hh := Nat.mul_lt_mul_of_pos_right h (Nat.pos_of_ne_zero hz)
    nlinarith only [hh, hf, Nat.mul_le_mul_left r hslack, Nat.mul_le_mul_left (2 * r) hcost]

#print axioms cover_count
#print axioms limiting_piece_bound
#print axioms progression_sum_le
#print axioms progression_basis_bound
#print axioms pieces_of_bounded_slack

end Green33PieceObstruction
