import ThetaShortTernaryCounts

/-! A power-logarithmic interval threshold for deleting any fixed relative theta error. -/
namespace Arxiv.«2501.03234».ThetaTernaryErrorBudget
open Filter Finset Real ThetaStrongDeviation ThetaShortPrimeInterval ThetaStrongOriginalTail
noncomputable section

def width (X : ℕ) := 1+log (X:ℝ)
def bad (ε : ℝ) (p : ℕ) : Prop := ε*(p:ℝ)*log p ≤ |(S p:ℝ)-p*log p/2|

theorem thin {α : ℝ} (hα : 0≤α) (hex : ExceptionalPower α) {ε σ : ℝ} (hε : 0<ε) (hσ : 0<σ) (m : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ X : ℕ in atTop,∀ H : ℕ,
      K*(X:ℝ)^α*(width X)^(8+m)≤H → H≤X →
      (((primes X H (bad ε)).card:ℝ)+1)*(width X)^m ≤ σ*H := by
  obtain ⟨C,hC,hE⟩ := hex hε
  let K := 2*(C+1)/σ
  refine ⟨K,by dsimp [K];positivity,?_⟩
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  filter_upwards [hE,absorb_log_power (by positivity : 0<2/σ) (by norm_num : 0<(1536:ℝ)) m,
    (tendsto_log_atTop.comp hn).eventually_ge_atTop 1,hn.eventually_ge_atTop 1] with X he htail hL hx H hsize hH
  let V := width X
  let B := (X:ℝ)^α
  have hV : 1≤V := by dsimp [V,width];change 1≤log (X:ℝ) at hL;linarith
  have hB : 1≤B := one_le_rpow hx hα
  have hVm : 0<V^m := pow_pos (by linarith) _
  have hV₈ : 1≤V^8 := one_le_pow₀ hV
  change (2/σ)*V^m≤exp (rate X/1536) at htail
  have hsmall : exp (-rate X/1536)*V^m ≤ σ/2 := by
    rw [neg_div,exp_neg]
    rw [inv_mul_eq_div,div_le_iff₀ (exp_pos _)]
    have h := mul_le_mul_of_nonneg_left htail hσ.le
    have hcancel : σ*(2/σ*V^m)=2*V^m := by field_simp
    rw [hcancel] at h
    linarith
  have hlog : (H:ℝ)/log X≤H := div_le_self (Nat.cast_nonneg _) hL
  have hpart : ((H:ℝ)/log X*exp (-rate X/1536))*V^m ≤ σ*H/2 := by
    rw [mul_assoc]
    calc _ ≤ (H:ℝ)*(σ/2) := mul_le_mul hlog hsmall (by positivity) (Nat.cast_nonneg _)
         _ = _ := by ring
  have hb1 : 1≤B*V^8 := one_le_mul_of_one_le_of_one_le hB hV₈
  have hsum : C*B*V^8+1 ≤ (C+1)*B*V^8 := by linarith only [hb1]
  change K*B*V^(8+m) ≤ H at hsize
  have hmul := mul_le_mul_of_nonneg_left hsize hσ.le
  have hcancel : σ*(K*B*V^(8+m))=2*((C+1)*B*V^8*V^m) := by dsimp [K];rw [pow_add];field_simp
  rw [hcancel] at hmul
  have hoff : (C*B*V^8+1)*V^m ≤ σ*H/2 := by linarith only [hmul,mul_le_mul_of_nonneg_right hsum hVm.le]
  have h := he H hH
  change ((primes X H (bad ε)).card:ℝ) ≤ H/log X*exp (-rate X/1536)+C*B*V^8 at h
  change (((primes X H (bad ε)).card:ℝ)+1)*V^m ≤ σ*H
  linarith only [hpart,hoff,mul_le_mul_of_nonneg_right h hVm.le]

#print axioms thin
end
end Arxiv.«2501.03234».ThetaTernaryErrorBudget
