import ThetaLocalMomentApproximation

/-! Elementary stability estimates for signed moments with an arbitrary
bounded multiplier. -/
namespace Arxiv.«2501.03234».ThetaLocalPowerStability
open Real Finset
noncomputable section

theorem gap (k : ℕ) {ε : ℝ} (hε : 0<ε) : ∃ D : ℝ, 0<D ∧ ∀ a b : ℝ,
    |a^k-b^k|≤ε*(1+|b|^k)+D*|a-b|^k := by
  cases k with
  | zero => exact ⟨1,by norm_num,fun a b => by simp;linarith⟩
  | succ k =>
    let C := ((k:ℝ)+1)*(2:ℝ)^k*(2:ℝ)^k
    have hC : 0<C := by dsimp [C];positivity
    let v := min 1 (ε/C)
    have hv : 0<v := lt_min (by norm_num) (div_pos hε hC)
    have hv1 : v≤1 := min_le_left ..
    have hvC := (le_div_iff₀ hC).mp (min_le_right 1 (ε/C))
    let D := 2*(1+1/v)^(k+1)
    refine ⟨D,by dsimp [D];positivity,?_⟩
    intro a b
    let W := 1+|b|
    have hW : 0≤W := by dsimp [W];positivity
    have ha := abs_sub_le a b 0
    simp only [sub_zero] at ha
    have huv : 0≤1+1/v := by positivity
    by_cases h : |a-b|≤v*W
    · have hmax : max |a| |b|≤2*W := by
        have hs := mul_le_mul_of_nonneg_right hv1 hW
        apply max_le <;> dsimp [W] at * <;> linarith only [ha,h,hs,abs_nonneg b]
      have h := mul_le_mul_of_nonneg_right h (show 0≤((k:ℝ)+1)*(2*W)^k by positivity)
      have h₀ := abs_pow_sub_pow_le a b (k+1)
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at h₀
      have h₁ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg a)) hmax k)
        (show 0≤|a-b| *((k:ℝ)+1) by positivity)
      have h₂ : |a^(k+1)-b^(k+1)|≤v*((k:ℝ)+1)*2^k*W^(k+1) := by
        rw [mul_pow] at h h₁
        rw [pow_succ W k]
        nlinarith only [h₀,h₁,h]
      have hpow : W^(k+1)≤2^k*(1+|b|^(k+1)) := by
        simpa [W] using add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg b) (k+1)
      apply h₂.trans
      have hh := mul_le_mul_of_nonneg_left hpow (show 0≤v*((k:ℝ)+1)*2^k by positivity)
      have hs := mul_le_mul_of_nonneg_right hvC (show 0≤1+|b|^(k+1) by positivity)
      change v*C≤ε at hvC
      change v*C*(1+|b|^(k+1))≤_ at hs
      dsimp only [C] at hs
      nlinarith only [hh,hs,mul_nonneg (show 0≤D by dsimp [D];positivity) (pow_nonneg (abs_nonneg (a-b)) (k+1))]
    · have hb : |b|≤|a-b|/v := by
        rw [le_div_iff₀ hv]; dsimp [W] at h;linarith only [lt_of_not_ge h,hv]
      have hsize : max |a| |b|≤(1+1/v)*|a-b| := by
        rw [add_mul,one_mul,one_div_mul_eq_div]
        apply max_le <;> linarith only [ha,hb,abs_nonneg (a-b)]
      have h₁ := pow_le_pow_left₀ (abs_nonneg a) ((le_max_left ..).trans hsize) (k+1)
      have h₂ := pow_le_pow_left₀ (abs_nonneg b) ((le_max_right ..).trans hsize) (k+1)
      have H := abs_sub (a^(k+1)) (b^(k+1))
      rw [←pow_abs,←pow_abs] at H
      rw [mul_pow] at h₁ h₂
      dsimp [D]
      linarith only [H,h₁,h₂,mul_nonneg hε.le (show 0≤1+|b|^(k+1) by positivity)]

/-- Small mean power error transfers the signed moment against any bounded test. -/
theorem mixed {s : Finset ℕ} (f b w : ℕ → ℝ) (k : ℕ) (hw : ∀ n,|w n|≤1)
    {ε D : ℝ} (hD : ∀ a b : ℝ, |a^k-b^k|≤ε*(1+|b|^k)+D*|a-b|^k) :
    |(∑ n∈s,w n*(f n)^k)-(∑ n∈s,w n*(b n)^k)|≤
      ε*((s.card:ℝ)+∑ n∈s,|b n|^k)+D*∑ n∈s,|f n-b n|^k := by
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  have h (n : ℕ) (_ : n∈s) :
      |w n*(f n)^k-w n*(b n)^k|≤ε*(1+|b n|^k)+D*|f n-b n|^k := by
    rw [←mul_sub,abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hw n)).trans (hD ..)
  apply (sum_le_sum h).trans_eq
  rw [sum_add_distrib,←mul_sum,←mul_sum,sum_add_distrib]
  simp

theorem upper {s : Finset ℕ} (f b : ℕ → ℝ) (k : ℕ) :
    (∑ n∈s,|b n|^k)≤2^(k-1)*((∑ n∈s,|f n|^k)+∑ n∈s,|f n-b n|^k) := by
  rw [←sum_add_distrib,mul_sum]
  apply sum_le_sum; intro n _
  have h := abs_sub_le (b n) (f n) 0
  rw [sub_zero,sub_zero,abs_sub_comm] at h
  exact (pow_le_pow_left₀ (abs_nonneg _) (h.trans_eq (add_comm ..)) k).trans
    (add_pow_le (abs_nonneg _) (abs_nonneg _) k)

theorem half_error {s : Finset ℕ} (f b : ℕ → ℝ) (k : ℕ) {M t : ℝ} (ht : 0<t)
    (hsize : (s.card:ℝ)≤2*M) (hE : (∑ n∈s,|f n-b n|^(2*k))≤t^2*M) :
    (∑ n∈s,|f n-b n|^k)≤2*t*M := by
  have hM : 0≤M := by linarith only [hsize,Nat.cast_nonneg (α:=ℝ) s.card]
  have h := sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun n => |f n-b n|^k)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,←pow_mul] at h
  rw [Nat.mul_comm k 2] at h
  have hs := mul_le_mul hsize hE (sum_nonneg (fun _ _ => pow_nonneg (abs_nonneg _) _)) (by positivity : 0≤2*M)
  by_contra! bad
  have HH := pow_lt_pow_left₀ bad (show 0≤2*t*M by positivity) (by decide : 2≠0)
  nlinarith only [HH,h,hs,sq_nonneg (t*M)]

#print axioms gap
#print axioms mixed
#print axioms upper
#print axioms half_error
end
end Arxiv.«2501.03234».ThetaLocalPowerStability
