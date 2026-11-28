import Mathlib

/-! Finite signed autocorrelation on short multiples of a prescribed period.
No primality input is needed for this sliding-window inequality. -/
namespace Arxiv.«2501.03234».ThetaSlidingCorrelation
open Finset
noncomputable section

def lag (N h : ℕ) (f : ℕ → ℝ) := ∑ n∈range N,f n*f (n+h)
def shift (i : ℕ) (f : ℕ → ℝ) (n : ℕ) := if i≤n then f (n-i) else 0

private theorem shifted_sum {N M i : ℕ} (hi : i≤M) (f : ℕ → ℝ) (hf : ∀ n≥N,f n=0) :
    (∑ n∈range (N+M),shift i f n)=∑ n∈range N,f n := by
  have hset : (range (N+M)).filter (fun n => i≤n)=Ico i (N+M) := by ext n;simp;omega
  rw [show (∑ n∈range (N+M),shift i f n)=(∑ n∈(range (N+M)).filter (fun n => i≤n),f (n-i)) by
    rw [sum_filter];rfl,hset,sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  symm
  apply sum_subset_zero_on_sdiff
  · exact range_mono (by omega)
  · intro n hn
    obtain ⟨_,hh⟩ := mem_sdiff.mp hn
    exact hf n (by simpa using hh)
  · intro n _;rfl

theorem twisted {N q L : ℕ} (f v : ℕ → ℝ) (hf : ∀ n≥N,f n=0) (hv : ∀ n,|v n|≤1)
    (hper : ∀ n j,v (n+q*j)=v n) :
    ((L:ℝ)*(∑ n∈range N,v n*f n))^2 ≤
      (N+q*L:ℕ)*∑ n∈range (N+q*L),(∑ j∈range L,shift (q*j) f n)^2 := by
  let B := range (N+q*L)
  let F (n : ℕ) := ∑ j∈range L,shift (q*j) f n
  have eqn : (∑ n∈B,v n*F n)=L*(∑ n∈range N,v n*f n) := by
    dsimp only [F]
    simp_rw [mul_sum]
    rw [sum_comm]
    have H (j : ℕ) (hj : j∈range L) : (∑ n∈B,v n*shift (q*j) f n)=∑ n∈range N,v n*f n := by
      rw [←shifted_sum (N:=N) (M:=q*L) (i:=q*j) (Nat.mul_le_mul_left q (mem_range.mp hj).le)
        (fun n => v n*f n) (fun n hn => by rw [hf n hn,mul_zero])]
      apply sum_congr rfl;intro n _
      dsimp only [shift]
      split_ifs with h
      · rw [←hper (n-q*j) j,Nat.sub_add_cancel h]
      · simp
    rw [sum_congr rfl H];simp [mul_sum]
  rw [←eqn]
  have hsq := sum_mul_sq_le_sq_mul_sq B v F
  have hsum : (∑ n∈B,v n^2)≤B.card := by
    apply le_trans (sum_le_sum (g:=fun _ => (1:ℝ)) (fun n _ => by
      have ht := pow_le_pow_left₀ (abs_nonneg _) (hv n) 2
      simpa only [sq_abs,one_pow] using ht)) (by simp)
  exact hsq.trans (mul_le_mul_of_nonneg_right (by simpa [B] using hsum) (sum_nonneg fun _ _ => sq_nonneg _))

private theorem cross {N M i j : ℕ} (hi : i≤j) (hj : j≤M) (f : ℕ → ℝ) (hf : ∀ n≥N,f n=0) :
    (∑ n∈range (N+M),shift i f n*shift j f n)=lag N (j-i) f := by
  change _=∑ n∈range N,f n*f (n+(j-i))
  rw [←shifted_sum hj (fun n => f n*f (n+(j-i))) (fun n hn => by rw [hf n hn,zero_mul])]
  apply sum_congr rfl;intro n _
  unfold shift
  by_cases h : j≤n
  · rw [if_pos (hi.trans h),if_pos h,if_pos h];dsimp only
    rw [show n-j+(j-i)=n-i by omega,mul_comm]
  · simp [h]

theorem gram {N q L : ℕ} (f : ℕ → ℝ) (hf : ∀ n≥N,f n=0) :
    (∑ n∈range (N+q*L),(∑ j∈range L,shift (q*j) f n)^2)=
      ∑ i∈range L,∑ j∈range L,lag N (q*(max i j-min i j)) f := by
  simp_rw [sq,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl;intro i hi
  rw [sum_comm]
  apply sum_congr rfl;intro j hj
  rcases le_total i j with h|h
  · rw [max_eq_right h,min_eq_left h,Nat.mul_sub]
    exact cross (Nat.mul_le_mul_left q h) (Nat.mul_le_mul_left q (mem_range.mp hj).le) f hf
  · rw [max_eq_left h,min_eq_right h,Nat.mul_sub]
    simp_rw [mul_comm (shift (q*i) f _)]
    exact cross (Nat.mul_le_mul_left q h) (Nat.mul_le_mul_left q (mem_range.mp hi).le) f hf

theorem bound {N q L : ℕ} (f v : ℕ → ℝ) (hf : ∀ n≥N,f n=0) (hv : ∀ n,|v n|≤1)
    (hper : ∀ n j,v (n+q*j)=v n) :
    ((L:ℝ)*(∑ n∈range N,v n*f n))^2 ≤ (N+q*L:ℕ)*
      ∑ i∈range L,∑ j∈range L,lag N (q*(max i j-min i j)) f := by
  simpa only [gram f hf] using twisted (L:=L) f v hf hv hper

#print axioms bound
end
end Arxiv.«2501.03234».ThetaSlidingCorrelation
