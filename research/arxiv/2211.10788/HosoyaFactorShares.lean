import HosoyaFactorMassIntervals

/-! Uniform bounds for the fraction of a term accounted for by a chosen set of primes. -/

namespace Arxiv.«2211.10788».FactorMass

open Finset Real Filter
open scoped Topology

noncomputable def share (S : Finset ℕ) (n : ℕ) := logPart S n / log n

theorem share_bounds (S : Finset ℕ) (n : ℕ) : 0 ≤ share S n ∧ share S n≤1 := by
  have nn := log_natCast_nonneg n
  refine ⟨div_nonneg (logPart_nonneg ..) nn,?_⟩
  rcases nn.eq_or_lt with z|pos
  · simp [share,←z]
  · exact (div_le_iff₀ pos).mpr (by simpa using logPart_le S n)

private lemma logValue_lower {f : ℕ → ℕ} (bnd : FibonacciSupportBounds f) (n : ℕ) :
    (n:ℝ)*log 2 ≤ 2*log (f n) := by
  have h := log_le_log (by positivity : 0<(2:ℝ)^n) (by exact_mod_cast bnd.lower n : (2:ℝ)^n ≤ (f n:ℝ)^2)
  simpa only [log_pow,Nat.cast_ofNat] using h

/-- Once the starting index exceeds K block lengths, this estimate for the
sum of the shares is independent of the starting point. -/
theorem block_share {f : ℕ → ℕ} (bnd : FibonacciSupportBounds f) (S : Finset ℕ)
    {r d a B K : ℕ} (hd : 0<d) (hb : 0<B) (hk : 0<K) (far : K*B≤a) :
    (K:ℝ)*(∑ t∈Ico a (a+B), share S (f (r+d*t))) ≤ 10*K*S.card+2*B := by
  let n := r+d*a
  let T := Ico a (a+B)
  let W := ∑ t∈T, share S (f (r+d*t))
  have aPos : 0<a := (Nat.mul_pos hk hb).trans_le far
  have nPos : 0<n := (Nat.mul_pos hd aPos).trans_le (Nat.le_add_left ..)
  have C : 0<(n:ℝ)*log 2 := mul_pos (by exact_mod_cast nPos) (log_pos (by norm_num))
  have le (t) (ht : t∈T) :
      (n:ℝ)*log 2*share S (f (r+d*t)) ≤ 2*logPart S (f (r+d*t)) := by
    have b : n≤r+d*t := Nat.add_le_add_left (Nat.mul_le_mul_left d (mem_Ico.mp ht).1) _
    have lo := (mul_le_mul_of_nonneg_right (by exact_mod_cast b : (n:ℝ)≤(r+d*t:ℕ))
      (log_pos (by norm_num : (1:ℝ)<2)).le).trans (logValue_lower bnd _)
    have lp : 0<log (f (r+d*t)) := by linarith only [C,lo]
    have sc := mul_le_mul_of_nonneg_right lo (share_bounds S (f (r+d*t))).1
    rw [show 2*log (f (r+d*t))*share S (f (r+d*t))=2*logPart S (f (r+d*t)) by
      unfold share;field_simp] at sc
    exact sc
  have lo := sum_le_sum le
  rw [←mul_sum,←mul_sum] at lo
  have up := interval_logPart bnd T S (r:=r) hd (a:=a) (L:=B) (by rfl)
  have bd : B≤a := (Nat.le_mul_of_pos_left B hk).trans far
  have dn : d*B≤n := (Nat.mul_le_mul_left d bd).trans (Nat.le_add_left ..)
  have cap : r+d*(a+B)+3≤5*n := by dsimp [n] at *;rw [Nat.mul_add];omega
  have cost : (n:ℝ)*W ≤ 2*((r+d*(a+B)+3:ℕ):ℝ)*S.card+2*d*B^2 := by
    apply le_of_mul_le_mul_right (a:=(log 2)) _ (log_pos (by norm_num))
    change (n:ℝ)*W*log 2 ≤ _
    change (n:ℝ)*log 2*W≤_ at lo
    nlinarith only [lo,up]
  have depth : d*(K*B)≤n := (Nat.mul_le_mul_left d far).trans (Nat.le_add_left ..)
  have nR : 0<(n:ℝ) := by exact_mod_cast nPos
  apply le_of_mul_le_mul_left (a:=(n:ℝ)) _ nR
  change (n:ℝ)*(K*W)≤_
  have capR : ((r+d*(a+B)+3:ℕ):ℝ) ≤ 5*(n:ℝ) := by exact_mod_cast cap
  have depthR : (d:ℝ)*(K*B)≤(n:ℝ) := by exact_mod_cast depth
  nlinarith only [mul_le_mul_of_nonneg_left cost (Nat.cast_nonneg (α:=ℝ) K),
    mul_le_mul_of_nonneg_right capR (by positivity : 0≤2*(K:ℝ)*S.card),
    mul_le_mul_of_nonneg_right depthR (by positivity : 0≤2*(B:ℝ))]

#print axioms share_bounds
#print axioms block_share

end Arxiv.«2211.10788».FactorMass
