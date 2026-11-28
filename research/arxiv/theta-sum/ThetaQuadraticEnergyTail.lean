import ThetaQuadraticEnergy

/-! Effective conductor truncation of the quadratic part of the limiting variance. -/
namespace Arxiv.«2501.03234».ThetaQuadraticEnergyTail
open Finset Filter Topology ThetaSpectrumDecay ThetaQuadraticEnergy ThetaNaturalPrimeMeans

private lemma log_majorant {y x : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hlog : 2 ≤ Real.log y) :
    (2+Real.log x)^4 ≤ (2+Real.log y)^4*(x/y) := by
  have hx : 0 < x := hy.trans_le hyx
  let t := (x/y)^((1:ℝ)/4)
  have h₁ : 1 ≤ t := Real.one_le_rpow ((one_le_div hy).2 hyx) (by norm_num)
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one h₁
  have h₄ : t^4=x/y := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hl := Real.log_le_sub_one_of_pos ht
  dsimp only [t] at hl
  rw [Real.log_rpow (div_pos hx hy),Real.log_div hx.ne' hy.ne'] at hl
  change 1/4*(Real.log x-Real.log y) ≤ t-1 at hl
  have hcomp : 2+Real.log x ≤ (2+Real.log y)*t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (sub_nonneg.mpr h₁)]
  have hxlog := (Real.log_le_log hy hyx)
  calc (2+Real.log x)^4 ≤ ((2+Real.log y)*t)^4 := by gcongr; linarith
       _ = _ := by rw [mul_pow,h₄]

private theorem coefficient_tail {Y : ℕ} (hy : 0 < Y) (hlog : 2 ≤ Real.log Y)
    (hAP : ProgressionMangoldt) (r : OddPrime) (hr : Y ≤ r.val) :
    coefficient r^2 ≤ 20736*(2+Real.log Y)^4/Y * (1/(r.val:ℝ)^2) := by
  have hy' : 0 < (Y:ℝ) := by exact_mod_cast hy
  have hr' : 0 < (r.val:ℝ) := by exact_mod_cast r.property.1.pos
  have hs := Real.sq_sqrt hr'.le
  have h := coefficient_bound hAP r
  have he : (coefficient r)^2 ≤ (144*(2+Real.log r.val)^2/((r.val:ℝ)*Real.sqrt r.val))^2 := by
    rw [← sq_abs]; gcongr
  have hlog' := log_majorant (x := (r.val:ℝ)) hy' (by exact_mod_cast hr) hlog
  simp only [div_pow,mul_pow,hs] at he
  calc (coefficient r)^2 ≤ 20736*(2+Real.log r.val)^4/(r.val:ℝ)^3 := by
         convert he using 1; ring
       _ ≤ 20736*((2+Real.log Y)^4*((r.val:ℝ)/Y))/(r.val:ℝ)^3 := by gcongr
       _ = _ := by field_simp

private lemma square_sum (Y : ℕ) (hy : 0 < Y) (s : Finset ℕ) (hs : ∀ n ∈ s, Y < n) :
    ∑ n∈s, 1/(n:ℝ)^2 ≤ 1/(Y:ℝ) := by
  have hI (B : ℕ) : ∑ n∈Ico (Y+1) (Y+B+1), 1/(n:ℝ)^2 ≤ 1/(Y:ℝ)-1/(Y+B:ℕ) := by
    induction B with
    | zero => simp
    | succ B ih =>
      rw [show Y+(B+1)+1=(Y+B+1)+1 by omega,sum_Ico_succ_top (by omega)]
      have hz : 0<(Y+B:ℕ) := by omega
      have hreal : (0:ℝ)<(Y+B:ℕ) := by exact_mod_cast hz
      have hstep : 1/((Y+B:ℕ)+1:ℝ)^2 ≤ 1/(Y+B:ℕ)-1/((Y+B:ℕ)+1:ℝ) := by
        field_simp
        nlinarith
      push_cast at ih hstep ⊢
      rw [← add_assoc (Y:ℝ) (B:ℝ) 1]
      linarith
  let B := ∑ n∈s,n
  have hsub : s ⊆ Ico (Y+1) (Y+B+1) := by
    intro n hn
    have hle : n ≤ B := single_le_sum (f:=fun k : ℕ => k) (by simp) hn
    exact mem_Ico.mpr ⟨by have := hs n hn; omega,by omega⟩
  apply (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans
  exact (hI B).trans (sub_le_self _ (by positivity))

/-- Odd prime conductors up to and including the natural cutoff. -/
def conductorsThrough (Y : ℕ) : Finset OddPrime :=
  (range (Y+1)).subtype (fun q : ℕ => q.Prime ∧ Odd q)

/-- Effective two-sided enclosure of the full prime-quadratic variance sum. -/
theorem energy_truncation (hAP : ProgressionMangoldt) {Y : ℕ} (hy : 0 < Y)
    (hlog : 2 ≤ Real.log Y) :
    0 < quadraticEnergy-∑ r∈conductorsThrough Y,(coefficient r)^2 ∧
      quadraticEnergy-∑ r∈conductorsThrough Y,(coefficient r)^2 ≤ 20736*(2+Real.log Y)^4/(Y:ℝ)^2 := by
  classical
  let s := conductorsThrough Y
  refine ⟨sub_pos.mpr (finite_energy_strict hAP _),sub_le_iff_le_add.mpr ?_⟩
  apply le_of_tendsto (coefficient_squares_summable hAP).hasSum
  filter_upwards [eventually_ge_atTop s] with t ht
  let u := t \ s
  have hgt (r : OddPrime) (h : r∈u) : Y < r.val := by
    have hn := (mem_sdiff.mp h).2
    simpa [s,conductorsThrough] using hn
  let K := 20736*(2+Real.log Y)^4/(Y:ℝ)
  have htail : ∑ r∈u,(coefficient r)^2 ≤ K*(1/(Y:ℝ)) := by
    calc ∑ r∈u,(coefficient r)^2 ≤ ∑ r∈u,K*(1/(r.val:ℝ)^2) :=
           sum_le_sum fun r hr => coefficient_tail hy hlog hAP r (hgt r hr).le
         _ = K*∑ n∈u.image Subtype.val,1/(n:ℝ)^2 := by
           rw [mul_sum,sum_image]
           exact fun _ _ _ _ h => Subtype.val_injective h
         _ ≤ _ := by
           apply mul_le_mul_of_nonneg_left _ (by dsimp [K]; positivity)
           apply square_sum Y hy
           intro n hn
           obtain ⟨r,hr,rfl⟩ := mem_image.mp hn
           exact hgt r hr
  have hsum := sum_sdiff ht (f:=fun r => (coefficient r)^2)
  change ∑ r∈u,(coefficient r)^2 + _ = _ at hsum
  have hK : K*(1/(Y:ℝ))=20736*(2+Real.log Y)^4/(Y:ℝ)^2 := by dsimp [K]; ring
  rw [hK] at htail
  change ∑ r∈t,(coefficient r)^2 ≤ _+∑ r∈s,(coefficient r)^2
  linarith

#print axioms energy_truncation
end Arxiv.«2501.03234».ThetaQuadraticEnergyTail
