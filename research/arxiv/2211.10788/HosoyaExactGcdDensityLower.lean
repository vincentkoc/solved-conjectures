import HosoyaExactGcdMassBound
import HosoyaRoughCofactorMass

/-! A uniform quantitative lower bound for every inhabited index–value gcd class. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Real Topology

/-- The Euler product and the large-common-prime tail give a uniform lower bound
from one realizing residue, with a free prime cutoff K². -/
theorem exact_fiber_log_tail : ∀ᶠ K : ℕ in atTop, ∀ {A m a d t : ℕ}, 0 < A →
    A ∣ Nat.fib A → m ∣ A → t<A → t ≡ a [MOD m] → residueGcd A t=d →
    ∀ {δ : ℝ}, Tendsto (sampleFreq (gcdFiber m a d)) atTop (𝓝 δ) →
      1/(2*exp 4*A*log ((K:ℝ)^2))-4/K ≤ δ := by
  obtain ⟨Y,euler⟩ := eventually_atTop.mp rough_totient_log_lower
  filter_upwards [eventually_ge_atTop (max Y 64)] with K large A m a d t ap ret ma small cl val δ lim
  let L := A/(t.gcd A)
  let P := roughProduct L (K^2)
  have hk : 64≤K := by omega
  have yk : Y≤K := by omega
  have k2 : Y≤K^2 := by nlinarith
  have prod := euler (K^2) k2 L
  push_cast at prod
  have low := exact_fiber_rough_lower ap ret ma small cl val lim hk
  change (P.totient:ℝ)/(A*P)-4/K ≤ δ at low
  calc 1/(2*exp 4*A*log ((K:ℝ)^2))-4/K
      = (1/(2*exp 4*log ((K:ℝ)^2)))/A-4/K := by ring
    _ ≤ ((P.totient:ℝ)/P)/A-4/K :=
      sub_le_sub_right (div_le_div_of_nonneg_right prod (Nat.cast_nonneg A)) _
    _ = (P.totient:ℝ)/(A*P)-4/K := by ring
    _ ≤ δ := low

/-- Every realizing residue of modulus A supplies density at least a constant
multiple of 1/(A log(2A)), uniformly over all exact gcds and progressions. -/
theorem uniform_exact_fiber_lower : ∃ B : ℕ, 2≤B ∧ ∀ {A m a d t : ℕ}, 0 < A →
    A ∣ Nat.fib A → m ∣ A → t<A → t ≡ a [MOD m] → residueGcd A t=d →
    ∀ {δ : ℝ}, Tendsto (sampleFreq (gcdFiber m a d)) atTop (𝓝 δ) →
      1/(16*exp 4*A*log ((B:ℝ)*A)) ≤ δ := by
  obtain ⟨K,cut⟩ := eventually_atTop.mp exact_fiber_log_tail
  obtain ⟨B,big⟩ := exists_nat_gt (max (K:ℝ) (64*exp 4+2))
  have bk : K < B := by exact_mod_cast (lt_of_le_of_lt (le_max_left ..) big : (K:ℝ)<B)
  have br : 64*exp 4+2 < (B:ℝ) := (le_max_right ..).trans_lt big
  have bp : 2≤B := by
    have : (2:ℝ)<B := by linarith [exp_pos 4]
    exact_mod_cast this.le
  refine ⟨B,bp,?_⟩
  intro A m a d t ap ret ma small cl val δ lim
  let j := B*A
  have bj : B≤j := Nat.le_mul_of_pos_right B ap
  have jpos : 0 < (j:ℝ) := by exact_mod_cast (show 0<j by omega)
  have jone : 1 < (j:ℝ) := by exact_mod_cast (show 1<j by omega)
  have apos : 0 < (A:ℝ) := by exact_mod_cast ap
  have lj : 0 < log (j:ℝ) := log_pos jone
  have low := cut (j^2) (show K≤j^2 by nlinarith) ap ret ma small cl val lim
  push_cast at low
  rw [Real.log_pow,Real.log_pow] at low
  have lc : log (j:ℝ) ≤ j := (Real.log_le_sub_one_of_pos jpos).trans (by linarith)
  have bj' : 64*exp 4*A ≤ (j:ℝ) := by
    dsimp [j]
    push_cast
    gcongr
    linarith
  have tail : 4/(j:ℝ)^2 ≤ 1/(16*exp 4*A*log (j:ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc 4*(16*exp 4*A*log (j:ℝ)) = (64*exp 4*A)*log (j:ℝ) := by ring
         _ ≤ (j:ℝ)*j := mul_le_mul bj' lc lj.le jpos.le
         _ = _ := by ring
  change 1/(16*exp 4*A*log ((B:ℝ)*A)) ≤ δ
  rw [←Nat.cast_mul]
  change 1/(16*exp 4*A*log (j:ℝ)) ≤ δ
  have double : 1/(2*exp 4*A*(2*(2*log (j:ℝ))))=2*(1/(16*exp 4*A*log (j:ℝ))) := by ring
  norm_num only [Nat.cast_ofNat] at low
  rw [double] at low
  linarith

#print axioms exact_fiber_log_tail
#print axioms uniform_exact_fiber_lower

end Arxiv.«2211.10788».IndexDivisors
