import FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS

/-! The pointwise congruence for odd primes in Berndt et al., arXiv:2501.03234v1,
Corollary 6.3 (v3, Proposition 7.1). -/

namespace Arxiv.«2501.03234»

open Finset

/-- Modulo four, the sign is linear in its exponent. -/
private lemma sign_mod_four (a : ℕ) : (-1 : ℤ) ^ a ≡ 1 - 2 * (a : ℤ) [ZMOD 4] := by
  induction a with
  | zero => decide
  | succ a ih =>
    rw [pow_succ, mul_neg_one, Nat.cast_succ]
    unfold Int.ModEq at *
    omega

/-- Complementary numerators give one carry when the two remainders are added. -/
private lemma reflected_quotients {p h j : ℕ} (hp : p.Prime)
    (hh : h ∈ Ico 1 p) (hj : j ∈ Ico 1 p) :
    h * j / p + (p - h) * j / p + 1 = j := by
  obtain ⟨hh₀, hh₁⟩ := mem_Ico.mp hh
  obtain ⟨hj₀, hj₁⟩ := mem_Ico.mp hj
  have hsum : h * j + (p - h) * j = p * j := by
    rw [← add_mul, Nat.add_sub_of_le hh₁.le]
  have hn : h * j % p ≠ 0 := by
    intro hz
    rcases hp.dvd_mul.mp (Nat.dvd_of_mod_eq_zero hz) with hd | hd
    · exact hh₁.not_ge (Nat.le_of_dvd hh₀ hd)
    · exact hj₁.not_ge (Nat.le_of_dvd hj₀ hd)
  have carry : p ≤ h * j % p + ((p - h) * j) % p := by
    by_contra! hlt
    have he := Nat.add_mod (h * j) ((p - h) * j) p
    rw [hsum, Nat.mul_mod_right, Nat.mod_eq_of_lt hlt] at he
    omega
  have he := Nat.add_div (a := h * j) (b := (p - h) * j) hp.pos
  rwa [hsum, Nat.mul_div_cancel_left _ hp.pos, if_pos carry, eq_comm] at he

/-- Pair the rows indexed by `h` and `p - h`, before summing over columns. -/
private lemma row_pair {p h : ℕ} (hp : p.Prime) (hh : h ∈ Ico 1 p) :
    S' h p + S' (p - h) p ≡ ∑ j ∈ Ico 1 p, 2 * (j : ℤ) [ZMOD 4] := by
  simp only [S', ← sum_add_distrib, ← Nat.cast_mul, Nat.floor_div_eq_div]
  apply Int.ModEq.sum
  intro j hj
  have hq := reflected_quotients hp hh hj
  have hs := (sign_mod_four (j + 1 + h * j / p)).add
    (sign_mod_four (j + 1 + (p - h) * j / p))
  simp only [Nat.cast_add, Nat.cast_one] at hs
  unfold Int.ModEq at *
  omega

private lemma column_sum (m : ℕ) :
    (∑ j ∈ Ico 1 (2 * m + 1), 2 * (j : ℤ)) ≡ 2 * (m : ℤ) [ZMOD 4] := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1 + 1) + 1 by omega,
      sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega)]
    push_cast
    unfold Int.ModEq at *
    omega

/-- For every odd prime `p`, the full theta sum has residue `p - 1` modulo four. -/
theorem S_mod_four (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    S p ≡ (p : ℤ) - 1 [ZMOD 4] := by
  obtain ⟨m, hm⟩ := hodd
  have hpm : p = 2 * m + 1 := by omega
  have href := sum_Ico_reflect (fun h => S' h p) 1 (m := m + 1) (n := p) (by omega)
  rw [show p + 1 - (m + 1) = m + 1 by omega, Nat.add_sub_cancel] at href
  have hsplit : S p = ∑ h ∈ Ico 1 (m + 1), (S' h p + S' (p - h) p) := by
    rw [S, sum_add_distrib, href, sum_Ico_consecutive _ (by omega) (by omega)]
  rw [hsplit]
  have hr : ∀ h ∈ Ico 1 (m + 1), S' h p + S' (p - h) p ≡ 2 * (m : ℤ) [ZMOD 4] := by
    intro h hh
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hh
    refine (row_pair hp (mem_Ico.mpr ⟨hlo, by omega⟩)).trans ?_
    rw [hpm]
    exact column_sum m
  have hs := Int.ModEq.sum hr
  simp only [sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul] at hs
  refine hs.trans ?_
  -- There are m row pairs, each contributing 2m. Now 2m² ≡ 2m modulo four.
  obtain ⟨a, ha⟩ := Int.even_mul_pred_self (m : ℤ)
  rw [hpm]
  push_cast
  rw [Int.modEq_iff_dvd]
  exact ⟨-a, by linarith only [ha]⟩

/-- The positivity conjecture therefore has no zero value at a prime congruent to three modulo four. -/
theorem S_ne_zero_of_three_mod_four {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) : S p ≠ 0 := by
  have ho : Odd p := ⟨p / 2, by omega⟩
  have hc := S_mod_four p hp ho
  unfold Int.ModEq at hc
  omega

end Arxiv.«2501.03234»

#print axioms Arxiv.«2501.03234».S_mod_four
#print axioms Arxiv.«2501.03234».S_ne_zero_of_three_mod_four
