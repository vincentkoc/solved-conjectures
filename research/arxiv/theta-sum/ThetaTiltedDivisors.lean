import ThetaDivisorBudget

/-! A small positive power tilt of the reciprocal divisor weights. -/
namespace Arxiv.«2501.03234».ThetaTiltedDivisors
open Real Finset ThetaDivisorLogMean ThetaDivisorTriangle
open scoped Classical
noncomputable section

def wt (s : ℝ) (d : ℕ) := (d:ℝ)^(s-1)
def total (s : ℝ) (m : ℕ) := ∑ d∈m.divisors,wt s d

theorem nonneg (s : ℝ) (d : ℕ) : 0≤wt s d := Real.rpow_nonneg (Nat.cast_nonneg _) _
theorem total_nonneg (s : ℝ) (m : ℕ) : 0≤total s m := sum_nonneg fun d _ => nonneg s d

theorem mult (s : ℝ) (a b : ℕ) : wt s (a*b)=wt s a*wt s b := by
  simp only [wt,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

theorem powers (s : ℝ) (p n : ℕ) : wt s (p^n)=wt s p^n := by
  induction n with
  | zero => simp [wt]
  | succ n ih => rw [pow_succ,mult,ih,pow_succ]

theorem multiple (s : ℝ) (m t : ℕ) :
    ∑ g∈m.divisors.filter (t∣·),wt s g ≤ wt s t*total s m := by
  let F := m.divisors.filter (t∣·)
  have hd {g : ℕ} (hg : g∈F) : t∣g := (mem_filter.mp hg).2
  have inj : Set.InjOn (fun g : ℕ => g/t) F := by
    intro x hx y hy h;simpa only [Nat.div_mul_cancel (hd hx),Nat.div_mul_cancel (hd hy)] using congrArg (·*t) h
  have sub : F.image (·/t)⊆m.divisors := by
    rintro _ hy;obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨hm,h₀⟩ := Nat.mem_divisors.mp (mem_filter.mp hx).1
    exact Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd (hd hx)).trans hm,h₀⟩
  calc _ = ∑ g∈F,wt s t*wt s (g/t) := by
             apply sum_congr rfl;intro g hg;rw [←mult,Nat.mul_div_cancel' (hd hg)]
       _ = wt s t*∑ g∈F.image (·/t),wt s g := by rw [sum_image inj,mul_sum]
       _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg sub (fun d _ _ => nonneg s d)) (nonneg s t)

private theorem geom {r : ℝ} (hr : 0≤r) (h : r≤3/4) (k : ℕ) :
    ∑ i∈range k,r^(i+1)≤4*r := by
  induction k with
  | zero => simp [hr]
  | succ k ih =>
    rw [sum_range_succ']
    have he (i : ℕ) : r^(i+1+1)=r^(i+1)*r := pow_succ ..
    simp_rw [he,←sum_mul]
    norm_num only [zero_add,pow_one]
    nlinarith only [mul_le_mul_of_nonneg_right ih hr,mul_le_mul_of_nonneg_right h hr]

theorem primeWt {s : ℝ} {U p : ℕ} (hs : 0≤s) (hlog : s*log U≤log (3/2)) (hp : p.Prime) (hl : p≤U) :
    wt s p ≤ (3/2)/(p:ℝ) := by
  have hpp : 0<(p:ℝ) := by exact_mod_cast hp.pos
  rw [wt,Real.rpow_sub hpp,Real.rpow_one]
  apply div_le_div_of_nonneg_right _ hpp.le
  rw [Real.rpow_def_of_pos hpp]
  apply (Real.exp_le_exp.mpr ((mul_comm (log p) s).le.trans ?_)).trans_eq (Real.exp_log (by norm_num : (0:ℝ)<3/2))
  exact (mul_le_mul_of_nonneg_left (Real.log_le_log hpp (by exact_mod_cast hl)) hs).trans hlog

theorem valuation {s : ℝ} {m U p : ℕ} (hs : 0≤s) (hlog : s*log U≤log (3/2)) (hp : p.Prime) (hl : p≤U) :
    ∑ g∈m.divisors,(g.factorization p:ℝ)*wt s g ≤ total s m*(6/(p:ℝ)) := by
  let e := m.factorization p
  have layer (g : ℕ) (hg : g∈m.divisors) : (g.factorization p:ℝ)*wt s g =
      ∑ i∈range e, if p^(i+1)∣g then wt s g else 0 := by
    have hg0 := (Nat.pos_of_mem_divisors hg).ne'
    have he : g.factorization p≤e := (Nat.factorization_le_iff_dvd hg0 (Nat.mem_divisors.mp hg).2).mpr (Nat.mem_divisors.mp hg).1 p
    simp_rw [hp.pow_dvd_iff_le_factorization hg0,Nat.succ_le_iff]
    rw [←sum_filter]
    have hh : (range e).filter (·<g.factorization p)=range (g.factorization p) := by ext i;simp;omega
    simp [hh]
  have hwt := primeWt hs hlog hp hl
  have pp : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hq : wt s p≤3/4 := hwt.trans ((div_le_iff₀ (by positivity)).mpr (by linarith))
  calc _ = ∑ i∈range e,∑ g∈m.divisors,if p^(i+1)∣g then wt s g else 0 := (sum_congr rfl layer).trans (sum_comm ..)
       _ ≤ ∑ i∈range e,total s m*(wt s p)^(i+1) := by
             apply sum_le_sum;intro i _;rw [←sum_filter,←powers,mul_comm];exact multiple ..
       _ = total s m*∑ i∈range e,(wt s p)^(i+1) := (mul_sum ..).symm
       _ ≤ total s m*(6/(p:ℝ)) := by
             apply mul_le_mul_of_nonneg_left _ (total_nonneg ..)
             exact (geom (nonneg ..) hq e).trans ((mul_le_mul_of_nonneg_left hwt (by norm_num : (0:ℝ)≤4)).trans_eq (by ring))

#print axioms valuation
end
end Arxiv.«2501.03234».ThetaTiltedDivisors
