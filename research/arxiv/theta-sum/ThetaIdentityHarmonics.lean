import ThetaOddHarmonicTriangle
import ThetaIdentityRow

/-! Quantitative positive mass from the first half of the identity row. -/
namespace Arxiv.«2501.03234».ThetaIdentityHarmonics
open Finset ThetaOddHarmonicTriangle ThetaRowCorrelations ThetaCotangentTriangle
noncomputable section

private theorem wave_first {d w : ℕ} (hd : 1 < d) (ho : Odd d) (hwd : w≤ d) :
    wave 1 d w=(if Odd w ∧ w.Coprime d then 1 else 0) := by
  by_cases h : Odd w ∧ w.Coprime d
  · have hlt : w< d := lt_of_le_of_ne hwd (by rintro rfl; have hh := h.2; rw [Nat.coprime_self] at hh; omega)
    simp [wave,Nat.odd_iff.mp ho,Nat.odd_iff.mp h.1,h,reciprocalSign,ZMod.val_natCast_of_lt hlt]
  · simp only [wave,Nat.coprime_one_left,Nat.odd_iff.mp ho,true_and,←Nat.odd_iff,if_neg h]
    rw [if_neg (fun H => h H.2)]

private theorem first_sum {d : ℕ} (hd : 1 < d) (ho : Odd d) : row d d 1 = U d := by
  have hr (n : ℕ) (hn : n≤ d) : row d n 1 =
      ∑ w∈(Icc 1 n).filter (fun w => Odd w ∧ w.Coprime d), (w:ℝ)⁻¹ := by
    induction n with
    | zero => simp [row]
    | succ n ih =>
      have hh := ih (by omega)
      rw [sum_filter] at hh ⊢
      rw [sum_Icc_succ_top (by omega),←hh,row,sum_range_succ]
      change row d n 1+_=_
      rw [wave_first hd ho hn]; split_ifs <;> simp
  rw [hr d le_rfl,U,odds,filter_filter]

/-- The identity row loses at most one unit from its full first-half harmonic sum. -/
theorem lower {d K : ℕ} (hd : 1 < d) (ho : Odd d) (hK : d≤ K) : U d-1 ≤ row d K 1 := by
  let A (n : ℕ) : ℝ := ∑ i∈range n,(wave 1 d (i+1):ℝ)
  let F (n : ℕ) : ℝ := row d n 1 - A n/(n+1:ℝ)
  have hA (n : ℕ) : 0≤ A n := ThetaIdentityRow.prefix_pos d hd n
  have hM : Monotone F := monotone_nat_of_le_succ (fun n => by
    have he : A (n+1)=A n+(wave 1 d (n+1):ℝ) := sum_range_succ ..
    have hR : row d (n+1) 1 = row d n 1+((n:ℝ)+1)⁻¹*(wave 1 d (n+1):ℝ) := sum_range_succ ..
    have hQ : A (n+1)/((n:ℝ)+1+1) ≤ A (n+1)/((n:ℝ)+1) :=
      div_le_div_of_nonneg_left (hA _) (by positivity) (by linarith)
    dsimp [F]; rw [hR]
    push_cast
    conv_rhs at hQ => rw [he,add_div,div_eq_inv_mul (wave 1 d (n+1):ℝ)]
    linarith)
  have hcap : A d≤(d:ℝ) := by
    apply le_trans (b:= ∑ i∈range d,(1:ℝ)) (sum_le_sum fun i hi => ?_) (by simp)
    rw [wave_first hd ho (mem_range.mp hi)]
    split_ifs <;> norm_num
  have h := hM hK
  dsimp only [F] at h
  rw [first_sum hd ho] at h
  have h1 : A d/((d:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  linarith [div_nonneg (hA K) (show (0:ℝ)≤ K+1 by positivity)]
#print axioms lower
end
end Arxiv.«2501.03234».ThetaIdentityHarmonics
