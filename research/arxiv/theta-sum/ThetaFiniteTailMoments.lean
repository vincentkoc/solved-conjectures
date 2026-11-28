import ThetaPrimeQuantiles

/-! Moments of a finite sample from simultaneous exponential quantile bounds. -/
namespace Arxiv.«2501.03234».ThetaFiniteTailMoments
open Finset Real
noncomputable section

private theorem decay {m j : ℕ} (hm : 1 ≤ m) :
    ((j:ℝ)+1)^(4*m)*exp (-(16*(m:ℝ)*j))≤(1/2:ℝ)^j := by
  have hp : 0≤(j:ℝ)+1 := by positivity
  have h₁ := pow_le_pow_left₀ hp (add_one_le_exp (j:ℝ)) (4*m)
  have h₂ : exp (-(j:ℝ))≤(1/2:ℝ)^j := by
    rw [show -(j:ℝ)=(j:ℝ)*(-1) by ring,exp_nat_mul]
    apply pow_le_pow_left₀ (exp_pos _).le
    rw [exp_neg,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [add_one_le_exp (1:ℝ)])
  apply (mul_le_mul_of_nonneg_right h₁ (exp_pos _).le).trans
  rw [←exp_nat_mul,←exp_add]
  apply (exp_le_exp.mpr ?_).trans h₂
  push_cast
  have hmr : (1:ℝ)≤ m := by exact_mod_cast hm
  nlinarith only [mul_le_mul_of_nonneg_right hmr (Nat.cast_nonneg (α:=ℝ) j),Nat.cast_nonneg (α:=ℝ) j]

/-- A moment bound from exponential counts on the quartic grid Bj⁴. -/
theorem finite {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ) {B : ℝ} (hB : 0<B)
    {m : ℕ} (hm : 1 ≤ m) (hr : ∀ p,0≤r p)
    (hb : ∀ j : ℕ, 1≤j → ((P.filter (fun p => B*(j:ℝ)^4≤r p)).card:ℝ)≤
      P.card*exp (-(16*(m:ℝ)*j))) :
    ∑ p∈P,(r p)^m≤2*(P.card:ℝ)*B^m := by
  classical
  let cap (j : ℕ) := ∑ p∈P,(min (r p) (B*(j:ℝ)^4))^m
  let M := (P.card:ℝ)*B^m
  have hM : 0≤M := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB.le _)
  have step (j : ℕ) (hj : 1≤j) : cap (j+1)≤cap j+M*(1/2:ℝ)^j := by
    let Q := P.filter (fun p => B*(j:ℝ)^4≤r p)
    let v := (B*((j:ℝ)+1)^4)^m
    have hsum : cap (j+1)≤cap j+Q.card*v := by
      have hh (p : α) : (min (r p) (B*((j+1:ℕ):ℝ)^4))^m ≤
          (min (r p) (B*(j:ℝ)^4))^m+if B*(j:ℝ)^4≤r p then v else 0 := by
        push_cast
        split_ifs with h
        · have h₁ := pow_le_pow_left₀ (le_min (hr p) (by positivity : 0≤B*((j:ℝ)+1)^4))
              (min_le_right (r p) (B*((j:ℝ)+1)^4)) m
          have h₂ := pow_nonneg (le_min (hr p) (by positivity : 0≤B*(j:ℝ)^4)) m
          dsimp only [v];linarith only [h₁,h₂]
        · rw [min_eq_left (le_of_not_ge h),add_zero]
          exact pow_le_pow_left₀ (le_min (hr p) (by positivity)) (min_le_left ..) _
      apply (sum_le_sum (s:=P) (fun p _ => hh p)).trans_eq
      rw [sum_add_distrib,←sum_filter,sum_const,nsmul_eq_mul]
    have hv : 0≤v := by dsimp [v];positivity
    apply hsum.trans (add_le_add_right ?_ _)
    apply (mul_le_mul_of_nonneg_right (hb j hj) hv).trans
    have hd := mul_le_mul_of_nonneg_left (decay (j:=j) hm) hM
    dsimp only [M,v] at *
    rw [mul_pow,←pow_mul]
    linarith only [hd]
  have gridBound (n : ℕ) : cap (n+1)≤M*(2-(1/2:ℝ)^n) := by
    induction n with
    | zero =>
      have h := sum_le_sum (s:=P) (fun p (_ : p∈P) => pow_le_pow_left₀
        (le_min (hr p) hB.le) (min_le_right (r p) B) m)
      simpa [cap,M,show (2:ℝ)-1=1 by norm_num] using h
    | succ n ih =>
      have hs := step (n+1) (by omega)
      rw [pow_succ] at hs ⊢
      linarith only [hs,ih]
  obtain ⟨n,hn⟩ := exists_nat_ge ((∑ p∈P,r p)/B)
  have hmax (p) (hp : p∈P) : r p≤B*((n+1:ℕ):ℝ)^4 := by
    have h := (div_le_iff₀ hB).mp hn
    have hh := single_le_sum (f:=r) (fun i _ => hr i) hp
    have hn' : (n:ℝ)≤((n+1:ℕ):ℝ)^4 := by
      have := pow_le_pow_right₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) n] : (1:ℝ)≤(n:ℝ)+1) (by decide : 1≤4)
      push_cast;simp only [pow_one] at this;linarith
    linarith only [hh,h,mul_le_mul_of_nonneg_left hn' hB.le]
  have heq : cap (n+1)=∑ p∈P,(r p)^m := by
    apply sum_congr rfl; intro p hp;rw [min_eq_left (hmax p hp)]
  rw [←heq]
  apply (gridBound n).trans
  dsimp only [M]
  nlinarith only [mul_nonneg hM (pow_nonneg (by norm_num : (0:ℝ)≤1/2) n)]

#print axioms finite
end
end Arxiv.«2501.03234».ThetaFiniteTailMoments
