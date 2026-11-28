import HosoyaFactorShares

/-! Moving sets of o(N) primes capture a vanishing mean logarithmic share
on both Hosoya diagonals, uniformly in the offset and positive step. -/

namespace Arxiv.«2211.10788».FactorMass

open Finset Real Filter
open scoped Topology

private theorem tiled {f : ℕ → ℕ} (bnd : FibonacciSupportBounds f) (S : Finset ℕ)
    {r d K B : ℕ} (hd : 0<d) (hk : 0<K) (hb : 0<B) :
    (K:ℝ)*(∑ t∈range (K^2*B), share S (f (r+d*t))) ≤ 3*K^2*B+10*K^3*S.card := by
  let g (t) := share S (f (r+d*t))
  let W (j : ℕ) := ∑ t∈range (j*B), g t
  let C : ℝ := 10*K*S.card+2*B
  have early : W K≤(K:ℝ)*B := by
    have le := sum_le_sum (s:=range (K*B)) fun t _ => (share_bounds S (f (r+d*t))).2
    simpa only [W,g,sum_const,card_range,nsmul_eq_mul,mul_one,Nat.cast_mul] using le
  have step (j) (hj : K≤j) : (K:ℝ)*W (j+1)≤K*W j+C := by
    have bound := block_share bnd S (r:=r) hd hb hk (Nat.mul_le_mul_right B hj)
    have eq : W (j+1)=W j+∑ t∈Ico (j*B) (j*B+B), g t := by
      dsimp only [W]
      rw [Nat.add_mul,one_mul]
      exact (sum_range_add_sum_Ico _ (by omega)).symm
    rw [eq,mul_add]
    exact add_le_add_right bound _
  have go (m) : (K:ℝ)*W (K+m)≤K*(K*B)+m*C := by
    induction m with
    | zero => simp; exact mul_le_mul_of_nonneg_left early (by positivity)
    | succ m ih =>
      have add := step (K+m) (Nat.le_add_right ..)
      rw [←Nat.add_assoc]
      push_cast
      linarith only [ih,add]
  have big : K≤K^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right K hk
  have res := go (K^2-K)
  rw [Nat.add_sub_of_le big] at res
  have cle : 0≤C := by dsimp [C];positivity
  have le : ((K^2-K:ℕ):ℝ)≤(K:ℝ)^2 := by exact_mod_cast Nat.sub_le (K^2) K
  dsimp only [C] at res cle
  change (K:ℝ)*W (K^2)≤_
  nlinarith only [res,mul_le_mul_of_nonneg_right le cle]

/-- The bound is simultaneous over every offset and positive step, including
those chosen after the prime support and the window length are known. -/
theorem finite_mean_share {f : ℕ → ℕ} (bnd : FibonacciSupportBounds f)
    (S : Finset ℕ) {r d N K : ℕ} (hd : 0<d) (hk : 0<K) (large : K^2≤N) :
    (∑ t∈range N, share S (f (r+d*t)))/(N:ℝ) ≤ 6/(K:ℝ)+10*K^2*((S.card:ℝ)/N) := by
  let B := N/K^2+1
  have k2 : 0<K^2 := pow_pos hk _
  have cover : N≤K^2*B := (Nat.lt_mul_div_succ N k2).le
  have length : K^2*B ≤ 2*N := by
    dsimp only [B];rw [Nat.mul_add_one]
    have := Nat.mul_div_le N (K^2)
    omega
  have Np : 0<(N:ℝ) := by exact_mod_cast (k2.trans_le large)
  have Kp : 0<(K:ℝ) := by exact_mod_cast hk
  have h := tiled bnd S (r:=r) (d:=d) hd hk (Nat.succ_pos _ : 0<B)
  have sub : (∑ t∈range N, share S (f (r+d*t))) ≤ ∑ t∈range (K^2*B), share S (f (r+d*t)) :=
    sum_le_sum_of_subset_of_nonneg (range_mono cover) (fun t _ _ => (share_bounds ..).1)
  have br : (K:ℝ)^2*B≤2*N := by exact_mod_cast length
  field_simp
  nlinarith only [h,br,mul_le_mul_of_nonneg_left sub Kp.le]

/-- The set of primes, starting index and positive step can all vary with
the sample size. The only restriction on the set is sublinear cardinality. -/
theorem sparse_mean_share {f : ℕ → ℕ} (bnd : FibonacciSupportBounds f)
    (S : ℕ → Finset ℕ) (r d : ℕ → ℕ) (hd : ∀ N, 0<d N)
    (small : Tendsto (fun N : ℕ => ((S N).card:ℝ)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ t∈range N, share (S N) (f (r N+d N*t)))/(N:ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  obtain ⟨K,less⟩ := exists_nat_gt (12/ε)
  have kp : 0<(K:ℝ) := (div_pos (by norm_num) ep).trans less
  have hk : 0<K := by exact_mod_cast kp
  have first : 6/(K:ℝ)<ε/2 := by
    rw [div_lt_iff₀ kp]
    have := (div_lt_iff₀ ep).mp less
    linarith
  have remainder := (small.const_mul (10*(K:ℝ)^2)).eventually_lt_const
    (show 10*(K:ℝ)^2*0<ε/2 by simpa using half_pos ep)
  filter_upwards [remainder,eventually_ge_atTop (K^2)] with N rest high
  have nn : 0≤(∑ t∈range N, share (S N) (f (r N+d N*t)))/(N:ℝ) :=
    div_nonneg (sum_nonneg fun _ _ => (share_bounds ..).1) (by positivity)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg nn]
  exact (finite_mean_share bnd (S N) (r:=r N) (hd N) hk high).trans_lt (by linarith only [first,rest])

#print axioms finite_mean_share
#print axioms sparse_mean_share

end Arxiv.«2211.10788».FactorMass
