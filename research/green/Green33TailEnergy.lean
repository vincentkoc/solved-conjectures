import Green33Multiplicity
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Finset Green33Multiplicity
open scoped Pointwise Topology

namespace Green33TailEnergy

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The number of ordered differences equal to a given group element. -/
def diffReps (A : Finset G) (s : G) : ℕ :=
  ((A ×ˢ A).filter fun p => p.1 - p.2 = s).card

omit [AddCommGroup G] in
private lemma sum_fibers {α : Type*} (B : Finset α) (f : α → G) :
    (∑ s, (B.filter fun b => f b = s).card) = B.card := by
  simpa using sum_card_fiberwise_eq_card_filter B univ f

private lemma sum_reps (A : Finset G) : ∑ s, reps A s = A.card ^ 2 := by
  simp only [reps, sum_fibers, card_product, sq]

private lemma sum_diff_sq (A : Finset G) :
    ∑ s, diffReps A s ^ 2 = ∑ s, reps A s ^ 2 := by
  let B := A ×ˢ A
  let f (p : G × G) := p.1 - p.2
  let Q := (B ×ˢ B).filter fun p => f p.1 = f p.2
  calc
    ∑ s, diffReps A s ^ 2 = ∑ s, (Q.filter fun p => f p.1 = s).card := by
      refine sum_congr rfl fun s _ => ?_
      rw [sq, diffReps, ← card_product]
      congr 1
      ext p
      simp only [Q, B, f, mem_product, mem_filter]
      grind
    _ = Q.card := sum_fibers Q _
    _ = A.addEnergy A := by
      apply card_equiv ((Equiv.refl (G × G)).prodCongr (Equiv.prodComm G G))
      rintro ⟨⟨a, b⟩, c, d⟩
      simp only [Q, B, f, mem_filter, mem_product, sub_eq_sub_iff_add_eq_add]
      change _ ↔ (((a ∈ A ∧ b ∈ A) ∧ d ∈ A ∧ c ∈ A) ∧ a + d = b + c)
      rw [add_comm c b]
      tauto
    _ = ∑ s, reps A s ^ 2 := addEnergy_eq_sum_sq A A

/-- Ordered sum and difference counts have the same second moment about any real center. -/
theorem centered_energy_eq (A : Finset G) (c : ℝ) :
    ∑ s, ((reps A s : ℝ) - c) ^ 2 = ∑ s, ((diffReps A s : ℝ) - c) ^ 2 := by
  have hsum : ∑ s, diffReps A s = ∑ s, reps A s := by
    simp only [diffReps, sum_fibers, card_product, sum_reps, sq]
  have h₁ : ∑ s, (diffReps A s : ℝ) = ∑ s, (reps A s : ℝ) := by exact_mod_cast hsum
  have h₂ : ∑ s, (diffReps A s : ℝ) ^ 2 = ∑ s, (reps A s : ℝ) ^ 2 := by
    exact_mod_cast sum_diff_sq A
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, h₁, h₂]

/-- The zero difference alone contributes the displayed lower bound. -/
theorem variance_floor (A : Finset G) (c : ℝ) :
    ((A.card : ℝ) - c) ^ 2 ≤ ∑ s, ((reps A s : ℝ) - c) ^ 2 := by
  have hzero : diffReps A 0 = A.card := by
    simp only [diffReps, sub_eq_zero, ← diag_eq_filter, diag_card]
  rw [centered_energy_eq, ← hzero]
  exact single_le_sum (fun s _ => sq_nonneg ((diffReps A s : ℝ) - c)) (mem_univ 0)

/-- Ordered representation energy on precisely those residues above the cutoff. -/
def tailEnergy (A : Finset G) (M : ℕ) : ℕ :=
  ∑ s ∈ univ.filter (fun s => M < reps A s), reps A s ^ 2

private def diagCount (A : Finset G) (s : G) : ℕ :=
  (A.filter fun a => a + a = s).card

private lemma cover_counts (A : Finset G) (hA : A + A = univ) (s : G) :
    0 < reps A s ∧ 2 ≤ reps A s + diagCount A s := by
  obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp (show s ∈ A + A from hA ▸ mem_univ _)
  have hp : (a, b) ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = s) := by simp [ha, hb, hab]
  have hr : 0 < reps A s := card_pos.mpr ⟨_, hp⟩
  refine ⟨hr, ?_⟩
  by_cases h : a = b
  · subst b
    exact Nat.add_le_add hr (show 0 < diagCount A s from card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hab⟩⟩)
  · have hp' : (b, a) ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = s) := by
      simp [ha, hb, add_comm b a, hab]
    have htwo : 1 < reps A s := one_lt_card.mpr ⟨_, hp, _, hp', fun he => h (congrArg Prod.fst he)⟩
    omega

private lemma split_square (r d M : ℕ) (hr : 0 < r) (hd : 2 ≤ r + d) :
    ((r : ℝ) - 2) ^ 2 ≤ (if M < r then (r : ℝ) ^ 2 else 0) +
      (M : ℝ) * (r + d - 2 : ℝ) + d := by
  have he : 0 ≤ (r : ℝ) + d - 2 := by
    have : (2 : ℝ) ≤ (r : ℝ) + d := by exact_mod_cast hd
    linarith
  have hm := mul_nonneg (Nat.cast_nonneg (α := ℝ) M) he
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  split_ifs with h
  · nlinarith [Nat.cast_nonneg (α := ℝ) d]
  · by_cases htwo : 2 ≤ r
    · have h₂ : (2 : ℝ) ≤ r := by exact_mod_cast htwo
      have hM : (r : ℝ) ≤ M := by exact_mod_cast Nat.le_of_not_gt h
      nlinarith [mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr hM),
        mul_nonneg (Nat.cast_nonneg (α := ℝ) M) (Nat.cast_nonneg (α := ℝ) d),
        Nat.cast_nonneg (α := ℝ) d]
    · have hr1 : r = 1 := by omega
      subst r
      norm_num at he hm ⊢
      linarith

/-- Above any cutoff, at least the zero-difference contribution survives after
subtracting the bounded-fiber cost and the allowance for diagonal sums. -/
theorem tail_energy_bound (A : Finset G) (hA : A + A = univ) (M : ℕ) :
    ((A.card : ℝ) - 2) ^ 2 ≤ (tailEnergy A M : ℝ) +
      M * ((A.card : ℝ) ^ 2 + A.card - 2 * Fintype.card G) + A.card := by
  have h (s : G) := split_square (reps A s) (diagCount A s) M
    (cover_counts A hA s).1 (cover_counts A hA s).2
  have ht : ∑ s, (if M < reps A s then (reps A s : ℝ) ^ 2 else 0) = (tailEnergy A M : ℝ) := by
    simp [tailEnergy, sum_filter]
  have hr : ∑ s, (reps A s : ℝ) = (A.card : ℝ) ^ 2 := by exact_mod_cast sum_reps A
  have hd : ∑ s, (diagCount A s : ℝ) = A.card := by
    exact_mod_cast sum_fibers A (fun a => a + a)
  have hs := (variance_floor A 2).trans (sum_le_sum (s := univ) fun s _ => h s)
  simpa only [sum_add_distrib, ← mul_sum, sum_sub_distrib, ht, hr, hd, sum_const,
    card_univ, nsmul_eq_mul, mul_comm (Fintype.card G : ℝ) 2] using hs

private lemma card_limits {ι : Type*} {l : Filter ι} (q : ι → ℕ+) (k : ι → ℕ)
    (hq : Tendsto (fun i => (q i : ℕ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ) / Real.sqrt (q i)) l (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => (k i : ℝ) / (q i : ℝ)) l (𝓝 0) ∧
    Tendsto (fun i => (k i : ℝ) ^ 2 / (q i : ℝ)) l (𝓝 2) := by
  have hs := Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hq)
  have hsq (i : ι) : Real.sqrt (q i) ^ 2 = (q i : ℝ) := Real.sq_sqrt (by positivity)
  constructor
  · simpa only [Function.comp_apply, div_div, ← sq, hsq] using hk.div_atTop hs
  · simpa only [div_pow, hsq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hk.pow 2

/-- Cutoffs may vary if their product with the normalized unordered-pair
surplus tends to zero. Every constant below 2 eventually bounds the normalized
tail energy from below. -/
theorem eventually_lt_tail_energy_of_cost {ι : Type*} {l : Filter ι} (q : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (q i))) (M : ι → ℕ)
    (hq : Tendsto (fun i => (q i : ℕ)) l atTop) (hA : ∀ i, A i + A i = univ)
    (hd : Tendsto (fun i => ((A i).card : ℝ) / Real.sqrt (q i)) l (𝓝 (Real.sqrt 2)))
    (hcost : Tendsto (fun i => (M i : ℝ) *
      ((((A i).card : ℝ) ^ 2 + (A i).card) / (q i : ℝ) - 2)) l (𝓝 0))
    {c : ℝ} (hc : c < 2) :
    ∀ᶠ i in l, c < (tailEnergy (A i) (M i) : ℝ) / (q i : ℝ) := by
  obtain ⟨hk, hk₂⟩ := card_limits q (fun i => (A i).card) hq hd
  have hq₄ := (tendsto_const_nhds (x := (4 : ℝ))).div_atTop
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hq)
  have hlim := ((((hk₂.sub (hk.const_mul 4)).add hq₄).sub hcost).sub hk)
  norm_num at hlim
  filter_upwards [hlim.eventually_const_lt hc] with i hi
  apply hi.trans_le
  have h := tail_energy_bound (A i) (hA i) (M i)
  rw [ZMod.card] at h
  have hpos : 0 < (q i : ℝ) := by exact_mod_cast (q i).pos
  field_simp [hpos.ne']
  nlinarith only [h]

/-- At Green's proposed density, residues above any fixed ordered multiplicity
carry at least (2 − o(1))q of the sum energy. -/
theorem eventually_lt_tail_energy {ι : Type*} {l : Filter ι} (q : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (q i))) (M : ℕ)
    (hq : Tendsto (fun i => (q i : ℕ)) l atTop) (hA : ∀ i, A i + A i = univ)
    (hd : Tendsto (fun i => ((A i).card : ℝ) / Real.sqrt (q i)) l (𝓝 (Real.sqrt 2)))
    {c : ℝ} (hc : c < 2) :
    ∀ᶠ i in l, c < (tailEnergy (A i) M : ℝ) / (q i : ℝ) := by
  apply eventually_lt_tail_energy_of_cost q A (fun _ => M) hq hA hd _ hc
  obtain ⟨hk, hk₂⟩ := card_limits q (fun i => (A i).card) hq hd
  simpa only [add_div, add_zero, sub_self, mul_zero] using
    (((hk₂.add hk).sub (tendsto_const_nhds (x := (2 : ℝ)))).const_mul (M : ℝ))

#print axioms centered_energy_eq
#print axioms variance_floor
#print axioms tail_energy_bound
#print axioms eventually_lt_tail_energy_of_cost
#print axioms eventually_lt_tail_energy

end Green33TailEnergy
