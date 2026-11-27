import Green33TailEnergy

open Finset Green33Multiplicity Green33TailEnergy
open scoped Pointwise

namespace Green33ReflectionRigidity

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Those elements of a basis whose partners under the reflection about sum s
also belong to the basis. -/
def reflectedPart (A : Finset G) (s : G) : Finset G :=
  A.filter fun a => s - a ∈ A

omit [Fintype G] in
theorem card_reflectedPart (A : Finset G) (s : G) :
    (reflectedPart A s).card = reps A s := by
  classical
  apply card_bij' (fun a _ => (a, s - a)) (fun p _ => p.1)
  · intro a ha
    obtain ⟨ha, hpartner⟩ := mem_filter.mp ha
    simp [ha, hpartner]
  · rintro ⟨a,b⟩ h
    obtain ⟨hp, hab⟩ := mem_filter.mp h
    obtain ⟨ha,hb⟩ := mem_product.mp hp
    change a + b = s at hab
    exact mem_filter.mpr ⟨ha, by simpa [← hab] using hb⟩
  · intros; rfl
  · rintro ⟨a,b⟩ h
    have hab : a + b = s := (mem_filter.mp h).2
    simp [← hab]

private def P (x : ℝ) : ℝ := (x - 1) * (x - 2)

private lemma P_nonneg (n : ℕ) : 0 ≤ P n := by
  by_cases h : 2 ≤ n
  · have hn : (2 : ℝ) ≤ n := by exact_mod_cast h
    exact mul_nonneg (by linarith) (by linarith)
  · interval_cases n <;> norm_num [P]

/-- Consecutive integer roots isolate the contribution of the zero difference. -/
private lemma polynomial_floor (A : Finset G) : P A.card ≤ ∑ s, P (reps A s) := by
  have rewriteP (x : ℝ) : P x = (x - 3/2)^2 - 1/4 := by unfold P; ring
  have he : ∑ s, P (reps A s) = ∑ s, P (diffReps A s) := by
    simp only [rewriteP, sum_sub_distrib, centered_energy_eq]
  have hz : diffReps A 0 = A.card := by simp only [diffReps, sub_eq_zero, ← diag_eq_filter, diag_card]
  rw [he, ← hz]
  exact single_le_sum (fun s _ => P_nonneg (diffReps A s)) (mem_univ 0)

/-- The number of diagonal ordered representations of a group element. -/
def diagonalReps (A : Finset G) (s : G) : ℕ := (A.filter fun a => a + a = s).card

private lemma sum_reps (A : Finset G) : ∑ t, reps A t = A.card ^ 2 := by
  simpa [reps, sq] using
    sum_card_fiberwise_eq_card_filter (A ×ˢ A) univ (fun p : G × G => p.1 + p.2)

private lemma sum_diagonalReps (A : Finset G) : ∑ t, diagonalReps A t = A.card := by
  simpa [diagonalReps] using sum_card_fiberwise_eq_card_filter A univ (fun a => a + a)

private lemma two_le (A : Finset G) (hA : A + A = univ) (s : G) :
    0 < reps A s ∧ 2 ≤ reps A s + diagonalReps A s := by
  obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp (show s ∈ A + A from hA ▸ mem_univ _)
  have hp : (a,b) ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = s) := by simp [ha, hb, hab]
  have hr : 0 < reps A s := card_pos.mpr ⟨_, hp⟩
  refine ⟨hr, ?_⟩
  by_cases he : a = b
  · subst b
    exact Nat.add_le_add hr (show 0 < diagonalReps A s from card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hab⟩⟩)
  · have hp' : (b,a) ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = s) := by
      simp [ha, hb, add_comm b a, hab]
    have : 1 < reps A s := one_lt_card.mpr ⟨_, hp, _, hp', fun h => he (congrArg Prod.fst h)⟩
    omega

/-- A cap on all sum fibers bounds the consecutive-root moment by the
unordered-pair surplus. All operations in the inequality are real. -/
theorem cap_surplus (A : Finset G) (hA : A + A = univ) (R : ℕ)
    (hR : ∀ s, reps A s ≤ R) :
    ((A.card : ℝ) - 1) * (A.card - 2 : ℝ) ≤
      (R - 1 : ℝ) * ((A.card : ℝ) ^ 2 + A.card - 2 * Fintype.card G) := by
  have point (s : G) : P (reps A s) ≤
      ((R : ℝ) - 1) * ((reps A s : ℝ) + diagonalReps A s - 2) := by
    obtain ⟨hr, hd⟩ := two_le A hA s
    have hpos : (1 : ℝ) ≤ (reps A s : ℝ) := by exact_mod_cast hr
    have hle : (reps A s : ℝ) ≤ R := by exact_mod_cast hR s
    have hd' : (2 : ℝ) ≤ (reps A s : ℝ) + diagonalReps A s := by exact_mod_cast hd
    unfold P
    by_cases h : 2 ≤ reps A s
    · have h' : (2 : ℝ) ≤ reps A s := by exact_mod_cast h
      exact mul_le_mul (by linarith) (by linarith [Nat.cast_nonneg (α := ℝ) (diagonalReps A s)])
        (by linarith) (by linarith)
    · have : reps A s = 1 := by omega
      rw [this]
      norm_num
      exact mul_nonneg (by linarith) (by rw [this] at hd'; push_cast at hd'; linarith)
  have hr : ∑ s, (reps A s : ℝ) = (A.card : ℝ) ^ 2 := by
    exact_mod_cast sum_reps A
  have hd : ∑ s, (diagonalReps A s : ℝ) = A.card := by exact_mod_cast sum_diagonalReps A
  have h := (polynomial_floor A).trans (sum_le_sum (s := univ) fun s _ => point s)
  simpa only [P, ← mul_sum, sum_sub_distrib, sum_add_distrib, hr, hd, sum_const,
    card_univ, nsmul_eq_mul, mul_comm (Fintype.card G : ℝ) 2] using h

omit [Fintype G] in
private lemma reps_le_card (A : Finset G) (s : G) : reps A s ≤ A.card := by
  rw [← card_reflectedPart]
  exact card_filter_le ..

/-- The order of a group admitting a two-basis of size k is at most (k²+2)/2. -/
theorem order_bound (A : Finset G) (hA : A + A = univ) :
    2 * Fintype.card G ≤ A.card ^ 2 + 2 := by
  by_cases hk : A.card ≤ 1
  · have hq : Fintype.card G ≤ A.card * A.card := by
      simpa only [hA, card_univ] using (card_add_le : (A + A).card ≤ A.card * A.card)
    nlinarith
  · have h := cap_surplus A hA A.card (reps_le_card A)
    have hk' : (1 : ℝ) < A.card := by exact_mod_cast Nat.lt_of_not_ge hk
    have hn := le_of_mul_le_mul_left (a := (A.card : ℝ) - 1) h (by linarith)
    have : (2 : ℝ) * Fintype.card G ≤ (A.card : ℝ) ^ 2 + 2 := by linarith
    exact_mod_cast this

omit [Fintype G] in
/-- The reflected part is invariant under the reflection a ↦ s − a. -/
theorem reflect_mem_iff (A : Finset G) (s a : G) :
    s - a ∈ reflectedPart A s ↔ a ∈ reflectedPart A s := by
  simp [reflectedPart, and_comm]

/-- Some reflection misses at most one element plus the positive part of k²−2q. -/
theorem exists_reflection (A : Finset G) (hA : A + A = univ) :
    ∃ s : G, (A \ reflectedPart A s).card ≤ (A.card ^ 2 - 2 * Fintype.card G) + 1 := by
  classical
  obtain ⟨s, _, hmax⟩ := exists_max_image univ (reps A) univ_nonempty
  let R := reps A s
  let k := A.card
  let q := Fintype.card G
  let u := k ^ 2 - 2 * q
  have hR : (1 : ℝ) ≤ R := by exact_mod_cast (two_le A hA s).1
  have hk : (R : ℝ) ≤ k := by exact_mod_cast reps_le_card A s
  have hu : (k : ℝ) ^ 2 ≤ u + 2 * (q : ℝ) := by
    exact_mod_cast (show k ^ 2 ≤ u + 2 * q by dsimp [u]; omega)
  have h := cap_surplus A hA R (fun t => hmax t (mem_univ t))
  change ((k : ℝ) - 1) * (k - 2 : ℝ) ≤ ((R : ℝ) - 1) * ((k : ℝ) ^ 2 + k - 2 * q) at h
  have herr : ((R : ℝ) - 1) * ((k : ℝ) ^ 2 - 2 * q) ≤ (k : ℝ) * u := calc
    _ ≤ ((R : ℝ) - 1) * u := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  refine ⟨s, ?_⟩
  have hsub : reflectedPart A s ⊆ A := filter_subset _ _
  rw [card_sdiff_of_subset hsub, card_reflectedPart]
  change k - R ≤ u + 1
  by_contra! hn
  have hgap : (R : ℝ) + u + 2 ≤ k := by exact_mod_cast (show R + u + 2 ≤ k by omega)
  nlinarith only [h, herr, mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg k)]

/-- When k² ≤ 2q, deleting at most one element leaves a reflection-invariant set. -/
theorem exists_reflection_of_sq_le (A : Finset G) (hA : A + A = univ)
    (hk : A.card ^ 2 ≤ 2 * Fintype.card G) :
    ∃ s : G, (A \ reflectedPart A s).card ≤ 1 := by
  simpa [Nat.sub_eq_zero_of_le hk] using exists_reflection A hA

private lemma center_of_order_eq (A : Finset G) (hA : A + A = univ)
    (he : 2 * Fintype.card G = A.card ^ 2 + 2) : ∃ s, reflectedPart A s = A := by
  classical
  by_cases hk : 2 < A.card
  · obtain ⟨s, _, hmax⟩ := exists_max_image univ (reps A) univ_nonempty
    have h := cap_surplus A hA (reps A s) (fun t => hmax t (mem_univ t))
    have he' : 2 * (Fintype.card G : ℝ) = (A.card : ℝ) ^ 2 + 2 := by exact_mod_cast he
    have hk' : (2 : ℝ) < A.card := by exact_mod_cast hk
    rw [he', show (A.card : ℝ)^2 + A.card - ((A.card : ℝ)^2 + 2) = A.card - 2 by ring] at h
    have hle := le_of_mul_le_mul_right h (show 0 < (A.card : ℝ) - 2 by linarith)
    refine ⟨s, eq_of_subset_of_card_le (filter_subset _ _) ?_⟩
    rw [card_reflectedPart]
    exact_mod_cast (show (A.card : ℝ) ≤ reps A s by linarith)
  · have hq : Fintype.card G ≤ A.card * A.card := by
      simpa only [hA, card_univ] using (card_add_le : (A + A).card ≤ A.card * A.card)
    have hk₂ : A.card = 2 := by
      rcases (show A.card = 0 ∨ A.card = 1 ∨ A.card = 2 by omega) with h | h | h
      · simp [h] at hq he
      · simp [h] at he
        omega
      · exact h
    obtain ⟨a,b,_,rfl⟩ := card_eq_two.mp hk₂
    refine ⟨a + b, filter_eq_self.mpr ?_⟩
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · simp
    · obtain rfl := mem_singleton.mp hx
      simp

/-- At equality the basis is exactly reflection-invariant. Every other group
element has exactly one unordered representation, and the center has no diagonal pair. -/
theorem extremal_profile (A : Finset G) (hA : A + A = univ)
    (he : 2 * Fintype.card G = A.card ^ 2 + 2) :
    ∃ s : G, reflectedPart A s = A ∧ diagonalReps A s = 0 ∧
      ∀ t ≠ s, reps A t + diagonalReps A t = 2 := by
  classical
  obtain ⟨s, hsym⟩ := center_of_order_eq A hA he
  have hs : reps A s = A.card := by rw [← card_reflectedPart, hsym]
  let e (t : G) := reps A t + diagonalReps A t - 2
  have hlocal (t : G) : e t + 2 = reps A t + diagonalReps A t :=
    Nat.sub_add_cancel (two_le A hA t).2
  have htotal := sum_congr (s₁ := univ) rfl fun t _ => hlocal t
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, sum_reps, sum_diagonalReps,
    mul_comm (Fintype.card G) 2] at htotal
  have hcenter := hlocal s
  rw [hs] at hcenter
  have hrest := univ.sum_erase_add e (mem_univ s)
  refine ⟨s, hsym, by omega, ?_⟩
  intro t hne
  have ht := single_le_sum (fun j _ => Nat.zero_le (e j)) (mem_erase.mpr ⟨hne, mem_univ t⟩)
  have := hlocal t
  omega

/-- A cyclic example attaining the additive constant in the order bound. -/
theorem sharp_mod_nine :
    ∃ A : Finset (ZMod 9), A.card = 4 ∧ A + A = univ := by
  exact ⟨{0, 1, 3, 4}, by decide⟩

#print axioms card_reflectedPart
#print axioms cap_surplus
#print axioms order_bound
#print axioms reflect_mem_iff
#print axioms exists_reflection
#print axioms exists_reflection_of_sq_le
#print axioms extremal_profile
#print axioms sharp_mod_nine

end Green33ReflectionRigidity
