import HosoyaDetectedPowerRelations

/-! A density-one estimate uniform in the initial index, with a growing range of power exponents. -/

namespace Arxiv.«2211.10788».PowerGaps
open Finset Filter HosoyaPowerIsolation
open scoped Classical Topology

/-- At scale N this cutoff grows as a positive power of N for fixed S and H. -/
def exponentCutoff (S : Finset ℕ) (H N : ℕ) :=
  2^(Nat.log 4 N / ((excluded S H).card+2))

def regularWindow (S : Finset ℕ) (H K n : ℕ) : Prop :=
  ∀ T : Finset (HosoyaNeighbor × ℕ), (∀ u∈T, n≤u.2 ∧ u.2≤n+H) →
    ∀ (e : HosoyaNeighbor × ℕ → ℤ) (k : ℕ), 0<k → k≤K →
      ((∃ a z : ℚˣ, IsRationalSUnit S a ∧ (∏ u∈T, siteUnit u ^ e u) = a*z^(k:ℤ)) ↔
        ∀ u∈T, (k:ℤ)∣e u)

private lemma normalized_bound (b K r H : ℕ) (kp : 1≤K) :
    (H+1)*K*(2*(K^b*(16+32*K*(2*r)))) ≤ 160*(H+1)*(r+1)*K^(b+2) := by
  have inside : 16+32*K*(2*r) ≤ 80*K*(r+1) := by nlinarith only [kp,Nat.zero_le (K*r)]
  calc
    _ ≤ (H+1)*K*(2*(K^b*(80*K*(r+1)))) := by gcongr
    _ = _ := by rw [pow_add];ring

/-- Explicit exceptional count for every interval and the local exponent cutoff. -/
theorem regular_exception_count (S : Finset ℕ) (H a : ℕ) {N : ℕ} (np : 0<N) :
    ((Ico a (a+N)).filter fun n => ¬regularWindow S H (exponentCutoff S H N) n).card ≤
      160*(H+1)*(Nat.log 4 N+1)*2^(Nat.log 4 N) := by
  let r := Nat.log 4 N
  let b := (excluded S H).card
  let K := exponentCutoff S H N
  have extent : N≤16*2^(2*r) := by
    have upper := Nat.lt_pow_succ_log_self (by decide : 1<4) N
    change N<4^(r+1) at upper
    rw [pow_succ,show (4:ℕ)=2^2 by decide,←pow_mul] at upper
    omega
  have sub : (Ico a (a+N)).filter (fun n => ¬regularWindow S H K n) ⊆
      (Ico a (a+16*2^(2*r))).filter (fun n => ¬goodWindow S H K n) := by
    intro n hn
    obtain ⟨inside,fail⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨(mem_Ico.mp inside).1,(mem_Ico.mp inside).2.trans_le (by omega)⟩,
      fun good => fail fun T within e _ kp ks => detected_power_iff S good T within e kp ks⟩
  have kp : 1≤K := Nat.one_le_two_pow
  have small : K^(b+2)≤2^r := by
    change (2^(r/(b+2)))^(b+2)≤2^r
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self r (b+2))
  exact (card_le_card sub).trans ((window_exception_bound S a (2*r) H K).trans
    ((normalized_bound b K r H kp).trans (Nat.mul_le_mul_left _ small)))

/-- Every moving interval has a vanishing exceptional fraction, uniformly over
all products, signed multiplicities and positive power moduli up to the cutoff. -/
theorem regular_window_density (S : Finset ℕ) (H : ℕ) (a : ℕ → ℕ) :
    Tendsto (fun N : ℕ => (((Ico (a N) (a N+N)).filter fun n =>
      ¬regularWindow S H (exponentCutoff S H N) n).card:ℝ)/N) atTop (𝓝 0) := by
  have rlim : Tendsto (Nat.log 4) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (4^b)] with N hn
    exact (Nat.le_log_iff_pow_le (by decide : 1<4) ((pow_pos (by decide : 0<(4:ℕ)) b).trans_le hn).ne').mpr hn
  have lin := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)
  have inv := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)
  have dec : Tendsto (fun t : ℕ => (160*((H:ℝ)+1))*(((t:ℝ)+1)/2^t)) atTop (𝓝 0) := by
    simpa only [pow_one,pow_zero,←add_div,add_zero,mul_zero] using
      (lin.add inv).const_mul (160*((H:ℝ)+1))
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ (dec.comp rlim)
  filter_upwards [eventually_gt_atTop 0] with N np
  let r := Nat.log 4 N
  let C := ((Ico (a N) (a N+N)).filter fun n => ¬regularWindow S H (exponentCutoff S H N) n).card
  have cn : (C:ℝ)≤160*((H:ℝ)+1)*((r:ℝ)+1)*2^r := by exact_mod_cast regular_exception_count S H (a N) np
  have size : (2:ℝ)^r*2^r ≤ N := by
    have lo := Nat.pow_log_le_self 4 np.ne'
    change 4^r≤N at lo
    rw [show (4:ℕ)=2*2 by decide,mul_pow] at lo
    exact_mod_cast lo
  change (C:ℝ)/N ≤ 160*((H:ℝ)+1)*(((r:ℝ)+1)/2^r)
  rw [mul_div_assoc',div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_right cn (by positivity : (0:ℝ)≤2^r),
    mul_le_mul_of_nonneg_left size (by positivity : (0:ℝ)≤160*((H:ℝ)+1)*((r:ℝ)+1))]

#print axioms regular_exception_count
#print axioms regular_window_density
end Arxiv.«2211.10788».PowerGaps
