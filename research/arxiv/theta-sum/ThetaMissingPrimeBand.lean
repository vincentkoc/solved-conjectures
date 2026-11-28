import ThetaPrimeDensity

/-! Prime conductors that a period of bounded logarithmic size must miss. -/
namespace Arxiv.«2501.03234».ThetaMissingPrimeBand
open Finset Filter ThetaPrimeDensity
noncomputable section

def band (Y m : ℕ) := (Nat.primesLE (128*Y)).filter (fun p => Y<p ∧ ¬p∣m)

private lemma prime_divisor_log {m : ℕ} (hm : 0 < m) (s : Finset ℕ) (hs : ∀ p∈s,p.Prime ∧ p∣m) :
    ∑ p∈s,Real.log p≤Real.log m := by
  classical
  have hsub : s⊆m.primeFactors := fun p hp => Nat.mem_primeFactors.mpr ⟨(hs p hp).1,(hs p hp).2,hm.ne'⟩
  have hd : (∏ p∈s,p)∣m := (prod_dvd_prod_of_subset s m.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd m)
  have hpos := Finset.prod_pos (fun p hp => (hs p hp).1.pos)
  have hc : (0:ℝ)<↑(∏ p∈s,p) := by exact_mod_cast hpos
  have H := Real.log_le_log hc (show (↑(∏ p∈s,p):ℝ)≤ m by exact_mod_cast Nat.le_of_dvd hm hd)
  rwa [Nat.cast_prod,Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (hs p hp).1.ne_zero)] at H

/-- Uniformly in m with log m at most 6Y, at least Y/log Y prime bases in
(Y,128Y] are missing. -/
theorem omitted : ∀ᶠ Y : ℕ in atTop,∀ m : ℕ, 0 < m → Real.log m≤6*Y →
    (Y:ℝ)≤((band Y m).card:ℝ)*Real.log Y := by
  classical
  have hi := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Chebyshev.eventually_primeCounting_le zero_lt_one)
  simp only [Nat.floor_natCast] at hi
  obtain ⟨K,hK⟩ := eventually_atTop.mp prime_count_lower
  filter_upwards [hi,eventually_ge_atTop K,eventually_ge_atTop 128] with Y hi hYK hY
  intro m hm hb
  have hy : (1:ℝ)<Y := by exact_mod_cast (show 2≤Y by omega)
  have hlog := Real.log_pos hy
  have hhi := hK (128*Y) (by omega)
  have hcompare : Real.log (128*Y:ℕ)≤2*Real.log Y := by
    have hle : (128:ℝ)≤Y := by exact_mod_cast hY
    push_cast; rw [Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<128) hle]
  have hlog2 : (1:ℝ)/2≤Real.log 2 := by have H := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2); norm_num at H; linarith
  have hlog4 : Real.log 4≤2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num only [Nat.cast_ofNat]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hcap : 16*(Y:ℝ)≤Nat.primeCounting (128*Y)*Real.log Y := by
    have H := mul_le_mul_of_nonneg_left hcompare (Nat.cast_nonneg (Nat.primeCounting (128*Y)))
    push_cast at hhi H
    nlinarith only [hhi,H,mul_le_mul_of_nonneg_right hlog2 (Nat.cast_nonneg (α:=ℝ) Y)]
  have hlow : (Nat.primeCounting Y:ℝ)*Real.log Y≤3*Y := by
    have H := (le_div_iff₀ hlog).mp hi
    nlinarith only [H,mul_le_mul_of_nonneg_right hlog4 (Nat.cast_nonneg (α:=ℝ) Y)]
  let b := (Nat.primesLE (128*Y)).filter (fun p => Y<p ∧ p∣m)
  have hpb : (b.card:ℝ)*Real.log Y≤6*Y := calc
    _ = ∑ _∈b,Real.log Y := by simp
    _ ≤ ∑ p∈b,Real.log p := sum_le_sum (fun p hp => Real.log_le_log (by linarith)
      (by exact_mod_cast (mem_filter.mp hp).2.1.le))
    _ ≤ Real.log m := prime_divisor_log hm b (fun p hp =>
      ⟨Nat.prime_of_mem_primesLE (mem_filter.mp hp).1,(mem_filter.mp hp).2.2⟩)
    _ ≤ _ := hb
  have hsub : Nat.primesLE (128*Y)⊆Nat.primesLE Y ∪ (b ∪ band Y m) := by
    intro p hp
    by_cases hl : p≤Y
    · exact mem_union_left _ (Nat.mem_primesLE.mpr ⟨hl,Nat.prime_of_mem_primesLE hp⟩)
    · apply mem_union_right
      by_cases hd : p∣m
      · exact mem_union_left _ (mem_filter.mpr ⟨hp,lt_of_not_ge hl,hd⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hp,lt_of_not_ge hl,hd⟩)
  have hcard : Nat.primeCounting (128*Y)≤Nat.primeCounting Y+b.card+(band Y m).card := by
    rw [←Nat.primesLE_card_eq_primeCounting,←Nat.primesLE_card_eq_primeCounting]
    have H := (card_le_card hsub).trans (card_union_le ..)
    have H' := card_union_le b (band Y m)
    omega
  have hh : (Nat.primeCounting (128*Y):ℝ)≤Nat.primeCounting Y+(b.card:ℝ)+(band Y m).card := by exact_mod_cast hcard
  linarith only [hcap,hlow,hpb,mul_le_mul_of_nonneg_right hh hlog.le, Nat.cast_nonneg (α:=ℝ) Y]

end
end Arxiv.«2501.03234».ThetaMissingPrimeBand
#print axioms Arxiv.«2501.03234».ThetaMissingPrimeBand.omitted
