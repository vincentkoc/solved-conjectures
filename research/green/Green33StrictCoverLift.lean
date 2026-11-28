import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A cyclic two-basis obtained by lifting Haanpää's strict sum cover modulo 56. -/

open Finset Filter
open scoped Pointwise Topology

namespace Green33StrictCoverLift

-- The low digit of x in a mixed expansion with q = c * l + 1.
private lemma digits (c l q x : ℤ) (hq : 0 < q) (hql : c * l + 1 = q) :
    ∃ a b : ℤ, 0 ≤ a ∧ a < q ∧ x = c * a + q * b := by
  let y := -l * x
  refine ⟨y % q, x + c * (y / q), Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq, ?_⟩
  calc
    x = c * y + q * x := by dsimp [y]; rw [← hql]; ring
    _ = c * (y % q + q * (y / q)) + q * x := by rw [Int.emod_add_mul_ediv]
    _ = _ := by ring

/-- Two progressions with weights s+iq and s+(i+d)q cover the square modulus
when d divides s and q is one more than a multiple of s. -/
theorem pair_lifts (s i d h q l x : ℤ) (hs : 0 < s) (hh : 0 < h) (hhs : h ≤ s)
    (hdh : d * h = s) (hq : 0 < q) (hql : s * l + 1 = q) :
    ∃ t u : ℤ, 0 ≤ t ∧ t < q + s ∧ 0 ≤ u ∧ u < q + s ∧
      ∃ e : ℤ, x = (s + i * q) * t + (s + (i + d) * q) * u + q ^ 2 * e := by
  obtain ⟨a, b, ha, haq, hx⟩ := digits s l q x hq hql
  obtain ⟨v, e, hv, hvq, hb⟩ := digits d (h * l) q (b - i * a - s) hq
    (by rw [← mul_assoc, hdh, hql])
  by_cases hcarry : v + h ≤ a
  · refine ⟨a - v - h, v + h, by omega, by omega, by omega, by omega, e, ?_⟩
    linear_combination hx + q * hb - q * hdh
  · refine ⟨a + q - v, v, by omega, by omega, by omega, by omega, e - i, ?_⟩
    linear_combination hx + q * hb

/-- Any two distinct slopes with gap dividing s cover the square modulus. Both
coefficients can be taken in the same short interval. -/
theorem progression_pair {s i j Q l : ℕ} [NeZero Q] (hs : 0 < s) (hij : i < j)
    (hgap : j - i ∣ s) (hQ : s * l + 1 = Q) (x : ZMod (Q ^ 2)) :
    ∃ t < s + Q, ∃ u < s + Q,
      ((s + i * Q : ℕ) : ZMod (Q ^ 2)) * (t : ZMod (Q ^ 2)) +
        ((s + j * Q : ℕ) : ZMod (Q ^ 2)) * (u : ZMod (Q ^ 2)) = x := by
  obtain ⟨h, hdh⟩ := hgap
  have hd : 0 < j - i := Nat.sub_pos_of_lt hij
  have hh : 0 < h := by by_contra! hn; simp [Nat.eq_zero_of_le_zero hn] at hdh; omega
  have hhs : h ≤ s := hdh ▸ Nat.le_mul_of_pos_left h hd
  obtain ⟨t, u, ht, htq, hu, huq, e, he⟩ := pair_lifts s i (j - i : ℕ) h Q l x.val
    (by exact_mod_cast hs) (by exact_mod_cast hh) (by exact_mod_cast hhs) (by exact_mod_cast hdh.symm)
    (by exact_mod_cast NeZero.pos Q) (by exact_mod_cast hQ)
  have hzero : ((Q : ZMod (Q ^ 2)) ^ 2) = 0 :=
    (Nat.cast_pow Q 2).symm.trans (ZMod.natCast_self _)
  have hij' : (i : ℤ) + ((j - i : ℕ) : ℤ) = j := by exact_mod_cast (Nat.add_sub_of_le hij.le)
  rw [hij'] at he
  have hcast := congrArg (fun k : ℤ => (k : ZMod (Q ^ 2))) he
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, Int.cast_pow,
    ZMod.natCast_zmod_val, hzero, zero_mul, add_zero] at hcast
  refine ⟨t.toNat, by omega, u.toNat, by omega, ?_⟩
  push_cast
  rw [show ((t.toNat : ℕ) : ZMod (Q ^ 2)) = (t : ZMod (Q ^ 2)) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg ht],
      show ((u.toNat : ℕ) : ZMod (Q ^ 2)) = (u : ZMod (Q ^ 2)) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hu]]
  exact hcast.symm

private def label : Fin 12 → ZMod 56 := ![0, 1, 12, 15, 22, 29, 32, 43, 44, 48, 50, 52]

set_option maxRecDepth 10000 in
private lemma label_cover : ∀ z : ZMod 56, ∃ i j : Fin 12, i < j ∧ label i + label j = z := by
  decide +kernel

private lemma label_inj : Function.Injective label := by
  intro i j
  decide +revert

private abbrev s : ℕ := 27720
@[irreducible] private def q (n : ℕ) := s * (n + 1) + 1
private instance (n : ℕ) : NeZero (q n) := ⟨by unfold q; omega⟩
private abbrev G (Q : ℕ) := ZMod (Q ^ 2) × ZMod 56

private lemma gaps : ∀ i j : Fin 12, i < j →
    let d := j.val - i.val
    0 < s / d ∧ s / d ≤ s ∧ d * (s / d) = s := by decide +kernel

private def weight (Q : ℕ) (i : Fin 12) := s + i.val * Q

private def arm (Q : ℕ) (p : Fin 12 × Fin (s + Q)) : G Q :=
  ((weight Q p.1 : ZMod (Q ^ 2)) * (p.2.val : ZMod (Q ^ 2)), label p.1)

@[irreducible] private def arms (Q : ℕ) : Finset (G Q) := univ.image (arm Q)

private lemma arms_cover (Q n : ℕ) [NeZero Q] (hQ : s * (n + 1) + 1 = Q) :
    arms Q + arms Q = univ := by
  apply eq_univ_of_forall
  intro g
  apply Finset.mem_add.mpr
  obtain ⟨i, j, hij, hz⟩ := label_cover g.2
  obtain ⟨_, _, hdh⟩ := gaps i j hij
  obtain ⟨t, ht, u, hu, hsum⟩ := progression_pair (by decide : 0 < s) hij
    ⟨_, hdh.symm⟩ hQ g.1
  have hmem (p : Fin 12 × Fin (s + Q)) : arm Q p ∈ arms Q := by
    rw [arms]; exact mem_image_of_mem _ (mem_univ _)
  refine ⟨_, hmem (i, ⟨t, ht⟩), _, hmem (j, ⟨u, hu⟩), ?_⟩
  exact Prod.ext hsum hz

private lemma arm_inj (Q n : ℕ) (hQ : s * (n + 1) + 1 = Q) : Function.Injective (arm Q) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  have hij : i = j := label_inj (congrArg Prod.snd he)
  subst j
  have hw : (weight Q i).Coprime (Q ^ 2) := by
    rw [Nat.coprime_pow_right_iff (by decide), weight, Nat.coprime_add_mul_right_left]
    rw [← hQ]
    rw [Nat.coprime_mul_left_add_right]
    simp
  have h := ((ZMod.isUnit_iff_coprime _ _).mpr hw).mul_left_cancel (congrArg Prod.fst he)
  have hlen : s + Q ≤ Q ^ 2 := by
    have hq : 27720 < Q := by change 27720 * (n + 1) + 1 = Q at hQ; omega
    change 27720 + Q ≤ Q ^ 2
    nlinarith [Nat.mul_le_mul_left Q (show 2 ≤ Q by omega)]
  have hab := ((ZMod.natCast_eq_natCast_iff a.val b.val (Q ^ 2)).mp h).eq_of_lt_of_lt
    (a.isLt.trans_le hlen) (b.isLt.trans_le hlen)
  rw [Fin.ext hab]

private lemma coprime_factors (n : ℕ) : (q n ^ 2).Coprime 56 := by
  apply Nat.Coprime.pow_left
  rw [q, show s * (n + 1) = 56 * (495 * (n + 1)) by rw [← mul_assoc]; rfl]
  rw [Nat.coprime_mul_left_add_left]
  decide

/-- The cyclic group has order 56 Q², for Q = 27720(n+1)+1. -/
def modulus (n : ℕ) : ℕ+ := ⟨q n ^ 2 * 56, by unfold q; positivity⟩

private def crt (n : ℕ) : ZMod (modulus n) ≃+ G (q n) :=
  (ZMod.chineseRemainder (coprime_factors n)).toAddEquiv

/-- The twelve labelled arithmetic progressions, transported along CRT. -/
def basis (n : ℕ) : Finset (ZMod (modulus n)) := (arms (q n)).map (crt n).symm.toEmbedding

private lemma map_cover {H K : Type*} [AddGroup H] [AddGroup K] [DecidableEq H] [DecidableEq K]
    [Fintype H] [Fintype K] (e : H ≃+ K) (A : Finset K) (hA : A + A = univ) :
    A.map e.symm.toEmbedding + A.map e.symm.toEmbedding = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (show e x ∈ A + A by simp [hA])
  refine mem_add.mpr ⟨_, mem_map.mpr ⟨_, ha, rfl⟩, _, mem_map.mpr ⟨_, hb, rfl⟩, ?_⟩
  change e.symm a + e.symm b = x
  rw [← map_add, hab, AddEquiv.symm_apply_apply]

theorem basis_add_basis (n : ℕ) : basis n + basis n = univ :=
  map_cover (crt n) _ (arms_cover (q n) n (by rw [q]))

theorem basis_card (n : ℕ) : (basis n).card = 12 * (27720 * (n + 1) + 1 + 27720) := by
  unfold basis arms
  rw [card_map, card_image_of_injective _ (arm_inj (q n) n (by rw [q]))]
  simp [q, Nat.add_comm]

private lemma ratio (n : ℕ) :
    ((basis n).card : ℝ) / Real.sqrt (modulus n) =
      Real.sqrt (18 / 7) * (1 + 27720 / (q n : ℝ)) := by
  have hq : 0 < (q n : ℝ) := by exact_mod_cast (show 0 < q n by unfold q; omega)
  have hc : Real.sqrt (18 / 7) * Real.sqrt 56 = 12 := by
    rw [← Real.sqrt_mul (by norm_num), show (18 / 7 : ℝ) * 56 = 144 by norm_num]
    norm_num
  rw [basis_card]
  rw [← show q n = 27720 * (n + 1) + 1 by rw [q]]
  change ((12 * (q n + s) : ℕ) : ℝ) / Real.sqrt ((q n ^ 2 * 56 : ℕ) : ℝ) = _
  push_cast
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq.le]
  field_simp
  linear_combination -hc

/-- The normalized sizes of this infinite family tend to √(18/7). -/
theorem basis_ratio_limit :
    Tendsto (fun n => ((basis n).card : ℝ) / Real.sqrt (modulus n)) atTop
      (𝓝 (Real.sqrt (18 / 7))) := by
  have hq : Tendsto q atTop atTop := tendsto_atTop.mpr fun m =>
    (eventually_ge_atTop m).mono fun n hn => by unfold q s; omega
  have ht : Tendsto (fun n => 27720 / (q n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hq)
  have hl := (tendsto_const_nhds.mul (tendsto_const_nhds.add ht) :
    Tendsto (fun n => Real.sqrt (18 / 7) * (1 + 27720 / (q n : ℝ))) atTop
      (𝓝 (Real.sqrt (18 / 7) * (1 + 0))))
  simpa [ratio] using hl

/-- The quantifiers of Green 33 with attainable constant √(18/7). -/
theorem frequently_cyclic_basis (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ N : ℕ+ in atTop, ∃ A : Finset (ZMod N),
      A + A = univ ∧ |(A.card : ℝ) / Real.sqrt N - Real.sqrt (18 / 7)| < ε := by
  apply frequently_atTop.mpr
  intro M
  obtain ⟨n, hn, he⟩ := ((eventually_ge_atTop (M : ℕ)).and
    (Metric.tendsto_nhds.mp basis_ratio_limit ε hε)).exists
  refine ⟨modulus n, ?_, basis n, basis_add_basis n, he⟩
  change (M : ℕ) ≤ q n ^ 2 * 56
  have hnq : n ≤ q n := by unfold q s; omega
  nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) (q n)]

#print axioms pair_lifts
#print axioms progression_pair
#print axioms basis_add_basis
#print axioms basis_card
#print axioms basis_ratio_limit
#print axioms frequently_cyclic_basis

end Green33StrictCoverLift
