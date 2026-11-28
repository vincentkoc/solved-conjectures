import ThetaPointwiseCutoff

/-! Pointwise power saving after removing all multiplicative characters of
order at most p^(1/2−ε), and equivalence with the original growth conjecture. -/
namespace Arxiv.«2501.03234».ThetaHighOrderGrowth
open Finset Filter Real ThetaPointwiseCutoff ThetaPointwiseOrders
open scoped Topology
noncomputable section

def highAt (ε : ℝ) (p : ℕ) : ℝ :=
  if h : p.Prime then letI : Fact p.Prime := ⟨h⟩; high p ((p:ℝ)^(1/2-ε)) else 0

theorem power_saving {ε : ℝ} (he : 0< ε) :
    ∃ C : ℝ, 0< C ∧ ∀ᶠ p : ℕ in atTop, p.Prime → _root_.Odd p →
      |(S p:ℝ)-highAt ε p|≤ C*(p:ℝ)^(1-ε/2) := by
  let δ := ε/8
  have hd : 0< δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,H⟩ := divisor_bound hd
  refine ⟨64*C,by positivity,?_⟩
  have hl := (isLittleO_log_rpow_atTop hd).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [eventually_ge_atTop 2,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hl] with p hp hl
  intro hp' ho
  let : Fact p.Prime := ⟨hp'⟩
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp'.pos
  have hx1 : 1≤ (p:ℝ) := by exact_mod_cast hp'.pos
  have hlp := log_nonneg hx1
  have hpd := rpow_pos_of_pos hx δ
  simp only [Real.norm_eq_abs,abs_of_nonneg hlp,abs_of_pos hpd,one_mul] at hl
  have hpow := one_le_rpow hx1 hd.le
  have hdv : ((p-1).divisors.card:ℝ)≤ C*(p:ℝ)^δ :=
    (H (p-1) (by omega)).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.sub_le p 1)) hd.le) hC.le)
  have hr : (1+log p)^3 ≤ (2*(p:ℝ)^δ)^3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  rw [highAt,dif_pos hp']
  apply (ThetaPointwiseCutoff.finite ho (Real.rpow_nonneg (Nat.cast_nonneg p) (1/2-ε))).trans
  calc
    _ ≤ 8*(p:ℝ)^(1/2-ε)*(C*(p:ℝ)^δ)*Real.sqrt p*(2*(p:ℝ)^δ)^3 := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_eq_rpow,show 1-ε/2=(1/2-ε)+δ+1/2+δ+δ+δ by dsimp [δ]; ring]
      simp only [Real.rpow_add hx]
      ring

/-- Uniformly on the odd primes, the discarded part is little-o of p. -/
theorem negligible {ε b : ℝ} (he : 0< ε) (hb : 0< b) :
    ∀ᶠ p : ℕ in atTop,p.Prime → _root_.Odd p → |(S p:ℝ)-highAt ε p|≤ b*p := by
  obtain ⟨C,hC,H⟩ := power_saving he
  have h := ((tendsto_rpow_neg_atTop (by linarith : 0< ε/2)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul C
  rw [mul_zero] at h
  filter_upwards [H,h.eventually_le_const hb] with p hs hp
  intro hprime ho
  have hx : 0 < (p:ℝ) := Nat.cast_pos.mpr hprime.pos
  apply (hs hprime ho).trans
  rw [sub_eq_add_neg,Real.rpow_add hx,Real.rpow_one]
  change C*((p:ℝ)^(-(ε/2)))≤ b at hp
  linarith only [mul_le_mul_of_nonneg_right hp hx.le]

/-- At a nonpositive candidate in the unresolved residue class, the large-order
sum is bounded above by every fixed positive multiple of p, eventually. -/
theorem nonpositive_obstruction {ε b : ℝ} (he : 0 < ε) (hb : 0 < b) :
    ∀ᶠ p : ℕ in atTop, p.Prime → p % 8 = 1 → S p ≤ 0 → highAt ε p ≤ b*p := by
  filter_upwards [negligible he hb] with p H
  intro hp h8 hS
  have ho : _root_.Odd p := Nat.odd_iff.mpr (by omega)
  have hs : (S p : ℝ) ≤ 0 := by exact_mod_cast hS
  linarith only [hs,(abs_le.mp (H hp ho)).1]

/-- Equivalence with the complete family of pinned Conjecture 4.4 lower
bounds. The lower-bound hypothesis concerns only the retained cubic sum. -/
theorem growth_iff {ε : ℝ} (he : 0< ε) :
    (∀ n : ℕ, ∀ᶠ p : ℕ in atTop,p.Prime → _root_.Odd p → (n:ℤ)*p < S p) ↔
    (∀ n : ℕ, ∀ᶠ p : ℕ in atTop,p.Prime → _root_.Odd p → (n:ℝ)*p < highAt ε p) := by
  have hm := negligible he (by norm_num : (0:ℝ)<1)
  constructor
  · intro H n
    filter_upwards [H (n+1),hm] with p hg hd
    intro hprime ho
    have hx : (((n+1:ℕ):ℝ))*(p:ℝ)<(S p:ℝ) := by exact_mod_cast hg hprime ho
    push_cast at hx
    linarith only [hx,(abs_le.mp (hd hprime ho)).2]
  · intro H n
    filter_upwards [H (n+1),hm] with p hg hd
    intro hprime ho
    have hx := hg hprime ho
    push_cast at hx
    have h : (n:ℝ)*p<(S p:ℝ) := by linarith only [hx,(abs_le.mp (hd hprime ho)).1]
    exact_mod_cast h

/-- The pinned statement, read at the level of its type. -/
theorem pinned_growth_iff {ε : ℝ} (he : 0 < ε) :
    (∀ n : ℕ, type_of% (conjecture_4_4 n)) ↔
    (∀ n : ℕ, ∀ᶠ p : ℕ in atTop,p.Prime → _root_.Odd p → (n:ℝ)*p < highAt ε p) := by
  simpa only [Nat.cast_mul] using growth_iff he

#print axioms nonpositive_obstruction
#print axioms pinned_growth_iff
#print axioms power_saving
#print axioms negligible
#print axioms growth_iff
end
end Arxiv.«2501.03234».ThetaHighOrderGrowth
