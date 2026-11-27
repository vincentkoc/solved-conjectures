import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A cyclic two-basis from Bevan–Erskine–Lewis, Theorem 10(a), arXiv:1506.04962. -/

open Finset Filter
open scoped Pointwise Topology

namespace Green33BELConstruction

private abbrev p (n : ℕ) := 6 * n + 5
private abbrev q (n : ℕ) := p n + 2
private abbrev G (n : ℕ) := (ZMod (q n) × ZMod (p n)) × ZMod 6

private def horizontal (n : ℕ) (x : ZMod (q n)) : G n := ((x, 0), 0)
private def vertical (n : ℕ) (y : ZMod (p n)) : G n := ((0, y), 1)
private def diagonal (n t : ℕ) : G n := ((t, t), 2)
private def slopeTwo (n u : ℕ) : G n := ((u, 2 * (u : ZMod (p n))), 4)

private def arms (n : ℕ) : Finset (G n) :=
  ((univ.image (horizontal n) ∪ univ.image (vertical n)) ∪
    (range (p n + 4)).image (diagonal n)) ∪ (range (q n)).image (slopeTwo n)

-- Lifts for the diagonal and slope-two arms in the layer 2 + 4 = 0.
private lemma diagonal_lifts (m a b : ℕ) (hm : 3 ≤ m) (ha : a < m + 2) (hb : b < m) :
    ∃ t < m + 4, ∃ u < m + 2,
      t + u ≡ a [MOD m + 2] ∧ t + 2 * u ≡ a + b [MOD m] := by
  by_cases h : b ≤ a
  · refine ⟨a - b, by omega, b, by omega, ?_, ?_⟩
    · rw [show a - b + b = a by omega]
    · rw [show a - b + 2 * b = a + b by omega]
  by_cases hb' : 2 ≤ b
  · let u := b - 2
    let t := a + (m + 2) - u
    have h₁ : t + u = a + (m + 2) := by dsimp [t, u]; omega
    have h₂ : t + 2 * u = (a + b) + m := by dsimp [t, u]; omega
    exact ⟨t, by dsimp [t, u]; omega, u, by dsimp [u]; omega,
      by simp [h₁, Nat.ModEq], by simp [h₂, Nat.ModEq]⟩
  · have h₁ : 3 + (m - 1) = m + 2 := by omega
    have h₂ : 3 + 2 * (m - 1) = (a + b) + m + m := by omega
    exact ⟨3, by omega, m - 1, by omega, by simp [h₁, show a = 0 by omega, Nat.ModEq],
      by simp [h₂, Nat.ModEq]⟩

set_option maxHeartbeats 500000 in
private lemma arms_cover (n : ℕ) : arms n + arms n = univ := by
  apply eq_univ_of_forall
  rintro ⟨⟨x, y⟩, z⟩
  have hX (v : ZMod (q n)) : horizontal n v ∈ arms n := by simp [arms]
  have hY (v : ZMod (p n)) : vertical n v ∈ arms n := by simp [arms]
  have hD (t : ℕ) (ht : t < p n + 4) : diagonal n t ∈ arms n := by
    exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ (mem_range.mpr ht)))
  have hH (u : ℕ) (hu : u < q n) : slopeTwo n u ∈ arms n := by
    exact mem_union_right _ (mem_image_of_mem _ (mem_range.mpr hu))
  have hz : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 := by decide +revert
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · let b := (y - (x.val : ZMod (p n))).val
    obtain ⟨t, ht, u, hu, h₁, h₂⟩ := diagonal_lifts (p n) x.val b (by dsimp [p]; omega)
      x.val_lt (ZMod.val_lt _)
    have hx := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h₁
    have hy := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h₂
    push_cast at hx hy
    rw [ZMod.natCast_zmod_val] at hx
    simp [b] at hy
    exact mem_add.mpr ⟨_, hD t ht, _, hH u hu, Prod.ext (Prod.ext hx hy) (show (2 : ZMod 6) + 4 = 0 by decide)⟩
  · exact mem_add.mpr ⟨_, hX x, _, hY y, by simp [horizontal, vertical]⟩
  · refine mem_add.mpr ⟨_, hX (x - y.val), _, hD y.val (by have := y.val_lt; omega), ?_⟩
    simp [horizontal, diagonal]
  · refine mem_add.mpr ⟨_, hY (y - x.val), _, hD x.val (by have := x.val_lt; dsimp [q] at *; omega), ?_⟩
    simp [vertical, diagonal]
    decide
  · let u := (((3 * n + 3 : ℕ) : ZMod (p n)) * y).val
    have hu : u < q n := by have := ZMod.val_lt (((3 * n + 3 : ℕ) : ZMod (p n)) * y); dsimp [u, q]; omega
    have hi : (2 : ZMod (p n)) * ((3 * n + 3 : ℕ) : ZMod (p n)) = 1 := by
      calc
        _ = ((2 * (3 * n + 3) : ℕ) : ZMod (p n)) := by push_cast; rfl
        _ = ((p n + 1 : ℕ) : ZMod (p n)) := by congr 1; dsimp [p]; omega
        _ = 1 := by simp
    have hy : 2 * (u : ZMod (p n)) = y := by
      dsimp only [u]; rw [ZMod.natCast_zmod_val, ← mul_assoc, hi, one_mul]
    refine mem_add.mpr ⟨_, hX (x - u), _, hH u hu, ?_⟩
    simp [horizontal, slopeTwo, hy]
  · refine mem_add.mpr ⟨_, hY (y - 2 * (x.val : ZMod (p n))), _, hH x.val x.val_lt, ?_⟩
    simp [vertical, slopeTwo]
    decide

private lemma coprime_factors (n : ℕ) : (q n).Coprime (p n) ∧ (q n * p n).Coprime 6 := by
  constructor
  · rw [q, Nat.coprime_self_add_left, Nat.coprime_two_left]
    exact ⟨3 * n + 2, by dsimp [p]; omega⟩
  · rw [Nat.coprime_mul_iff_left]
    constructor
    · change (6 * n + 5 + 2).Coprime 6
      rw [Nat.add_assoc, Nat.coprime_mul_left_add_left]; decide
    · change (6 * n + 5).Coprime 6
      rw [Nat.coprime_mul_left_add_left]; decide

/-- The modulus in Theorem 10(a), with the paper's parameter equal to `6n + 7`. -/
def modulus (n : ℕ) : ℕ+ :=
  ⟨(q n * p n) * 6, by dsimp [p, q]; positivity⟩

private def crt (n : ℕ) : ZMod (modulus n) ≃+ G n :=
  (ZMod.chineseRemainder (coprime_factors n).2).toAddEquiv.trans
    ((ZMod.chineseRemainder (coprime_factors n).1).toAddEquiv.prodCongr (AddEquiv.refl _))

/-- The four tagged arms of the construction, transported to the cyclic group by CRT. -/
def basis (n : ℕ) : Finset (ZMod (modulus n)) := (arms n).map (crt n).symm.toEmbedding

theorem basis_add_basis (n : ℕ) : basis n + basis n = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp (show crt n x ∈ arms n + arms n by simp [arms_cover])
  refine mem_add.mpr ⟨_, mem_map.mpr ⟨_, ha, rfl⟩, _, mem_map.mpr ⟨_, hb, rfl⟩, ?_⟩
  change (crt n).symm a + (crt n).symm b = x
  rw [← map_add, hab, AddEquiv.symm_apply_apply]

private lemma disjoint_labels {α β : Type*} {n : ℕ} {s : Finset α} {t : Finset β}
    {f : α → G n} {g : β → G n} {c d : ZMod 6} (h : c ≠ d)
    (hf : ∀ x, (f x).2 = c) (hg : ∀ x, (g x).2 = d) :
    Disjoint (s.image f) (t.image g) := by
  apply disjoint_left.mpr
  intro v hv hw
  obtain ⟨x, _, rfl⟩ := mem_image.mp hv
  obtain ⟨y, _, he⟩ := mem_image.mp hw
  exact h ((hf x).symm.trans ((congrArg Prod.snd he.symm).trans (hg y)))

/-- The four arms have respective sizes `q`, `q−2`, `q+2`, and `q`. -/
theorem basis_card (n : ℕ) : (basis n).card = 4 * (6 * n + 7) := by
  have hd : Set.InjOn (diagonal n) (range (p n + 4)) := by
    intro a ha b hb h
    simp only [coe_range, Set.mem_Iio] at ha hb
    have hq := (ZMod.natCast_eq_natCast_iff a b (q n)).mp (congrArg (fun v : G n => v.1.1) h)
    have hp := (ZMod.natCast_eq_natCast_iff a b (p n)).mp (congrArg (fun v : G n => v.1.2) h)
    have hm := (Nat.modEq_and_modEq_iff_modEq_mul (coprime_factors n).1).mp ⟨hq, hp⟩
    have hl : p n + 4 ≤ q n * p n := by dsimp [q, p]; nlinarith
    exact hm.eq_of_lt_of_lt (ha.trans_le hl) (hb.trans_le hl)
  have hh : Set.InjOn (slopeTwo n) (range (q n)) := by
    intro a ha b hb h
    exact ((ZMod.natCast_eq_natCast_iff a b (q n)).mp (congrArg (fun v : G n => v.1.1) h)
      ).eq_of_lt_of_lt (mem_range.mp ha) (mem_range.mp hb)
  unfold basis arms
  rw [card_map, card_union_of_disjoint, card_union_of_disjoint, card_union_of_disjoint]
  · rw [card_image_of_injective _ (show Function.Injective (horizontal n) from
          fun a b h => congrArg (fun v : G n => v.1.1) h),
        card_image_of_injective _ (show Function.Injective (vertical n) from
          fun a b h => congrArg (fun v : G n => v.1.2) h),
        card_image_of_injOn hd, card_image_of_injOn hh]
    simp [q, p, ZMod.card]; omega
  · exact disjoint_labels (by decide : (0 : ZMod 6) ≠ 1) (fun _ => rfl) (fun _ => rfl)
  · exact disjoint_union_left.mpr
      ⟨disjoint_labels (by decide : (0 : ZMod 6) ≠ 2) (fun _ => rfl) (fun _ => rfl),
       disjoint_labels (by decide : (1 : ZMod 6) ≠ 2) (fun _ => rfl) (fun _ => rfl)⟩
  · exact disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨disjoint_labels (by decide : (0 : ZMod 6) ≠ 4) (fun _ => rfl) (fun _ => rfl),
       disjoint_labels (by decide : (1 : ZMod 6) ≠ 4) (fun _ => rfl) (fun _ => rfl)⟩,
       disjoint_labels (by decide : (2 : ZMod 6) ≠ 4) (fun _ => rfl) (fun _ => rfl)⟩

private lemma ratio (n : ℕ) :
    ((basis n).card : ℝ) / Real.sqrt (modulus n) =
      Real.sqrt ((8 / 3 : ℝ) * (1 + 2 / (p n : ℝ))) := by
  have hp : 0 < (p n : ℝ) := by dsimp [p]; positivity
  have hq : 0 < (q n : ℝ) := by dsimp [q, p]; positivity
  rw [basis_card]
  change ((4 * (6 * n + 7) : ℕ) : ℝ) / Real.sqrt (((q n * p n) * 6 : ℕ) : ℝ) = _
  rw [← Real.sqrt_sq (show 0 ≤ ((4 * (6 * n + 7) : ℕ) : ℝ) / _ by positivity)]
  congr 1
  rw [div_pow, Real.sq_sqrt (by positivity)]
  have he : 6 * n + 7 = q n := rfl
  rw [he]
  push_cast
  field_simp
  ring

/-- The construction attains the asymptotic size constant `√(8/3)`. -/
theorem basis_ratio_limit :
    Tendsto (fun n => ((basis n).card : ℝ) / Real.sqrt (modulus n)) atTop
      (𝓝 (Real.sqrt (8 / 3))) := by
  have hp : Tendsto p atTop atTop := tendsto_atTop.mpr fun m =>
    (eventually_ge_atTop m).mono fun n hn => by dsimp [p]; omega
  have ht : Tendsto (fun n => 2 / (p n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hp)
  have hl := Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_const_nhds.mul (tendsto_const_nhds.add ht) :
      Tendsto (fun n => (8 / 3 : ℝ) * (1 + 2 / (p n : ℝ))) atTop (𝓝 ((8 / 3) * (1 + 0))))
  simpa [ratio, Function.comp_def] using hl

/-- The quantifiers and sumset predicate of Green 33, with the BEL constant. -/
theorem frequently_cyclic_basis (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ N : ℕ+ in atTop, ∃ A : Finset (ZMod N),
      A + A = univ ∧ |(A.card : ℝ) / Real.sqrt N - Real.sqrt (8 / 3)| < ε := by
  apply frequently_atTop.mpr
  intro M
  obtain ⟨n, hn, he⟩ := ((eventually_ge_atTop (M : ℕ)).and
    (Metric.tendsto_nhds.mp basis_ratio_limit ε hε)).exists
  refine ⟨modulus n, ?_, basis n, basis_add_basis n, he⟩
  change (M : ℕ) ≤ (q n * p n) * 6
  dsimp [q, p]; nlinarith

/-- For four labels whose distinct pairs cover a finite cyclic label group, its order is at
most six (the diameter-two label count in Bevan–Erskine–Lewis, Observation 11). -/
theorem four_label_bound (w : ℕ+) (B : Finset (ZMod w)) (hB : B.card = 4)
    (h : ∀ z : ZMod w, ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ a + b = z) : (w : ℕ) ≤ 6 := by
  let S := (B.powersetCard 2).image (fun T => ∑ t ∈ T, t)
  have hS : S = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := h z
    exact mem_image.mpr ⟨{a, b}, mem_powersetCard.mpr
      ⟨insert_subset ha (singleton_subset_iff.mpr hb), by simp [hab]⟩, by simp [hab]⟩
  have hc : S.card ≤ (B.powersetCard 2).card := card_image_le
  rw [hS, card_univ, ZMod.card, card_powersetCard, hB] at hc
  exact hc

#print axioms basis_add_basis
#print axioms basis_card
#print axioms basis_ratio_limit
#print axioms frequently_cyclic_basis
#print axioms four_label_bound

end Green33BELConstruction
