import ThetaDiagonalConstant
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Rational bounds for the linear coefficient of the divisible theta diagonal. -/
namespace Arxiv.«2501.03234».ThetaCenterBounds
open Finset Filter Real ThetaDivisibleDiagonal ThetaDiagonalConstant

private noncomputable def term (j : ℕ) : ℝ := log (2*(j:ℝ)+1)/(2*(j:ℝ)+1)^2

private lemma term_nonneg (j : ℕ) : 0≤term j := by
  exact div_nonneg (log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) j])) (sq_nonneg _)

private lemma log_le_sqrt {u : ℝ} (hu : 0<u) : log u ≤ sqrt u := by
  have h := log_le_sub_one_of_pos (show 0<sqrt u/2 by positivity)
  rw [log_div (by positivity) (by norm_num),log_sqrt hu.le] at h
  linarith [log_two_lt_d9]

private noncomputable def v (j : ℕ) := (sqrt (2*(j:ℝ)+1))⁻¹

private lemma step (j : ℕ) : term (j+1) ≤ v j - v (j+1) := by
  let a := sqrt (2*(j:ℝ)+1)
  let b := sqrt (2*((j:ℝ)+1)+1)
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hab : a≤b := sqrt_le_sqrt (by linarith)
  have hasq : a^2=2*(j:ℝ)+1 := sq_sqrt (by positivity)
  have hbsq : b^2=2*((j:ℝ)+1)+1 := sq_sqrt (by positivity)
  have hgap : (b-a)*(b+a)=2 := by nlinarith only [hasq,hbsq]
  have ht : a*(b+a)≤2*b^2 := calc
    _ ≤ b*(b+b) := by gcongr
    _ = _ := by ring
  dsimp only [term,v]; push_cast
  apply (div_le_div_of_nonneg_right (log_le_sqrt (by positivity)) (sq_nonneg _)).trans
  change b/(2*((j:ℝ)+1)+1)^2≤a⁻¹-b⁻¹
  rw [← hbsq]; field_simp
  nlinarith only [mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hab),
    show a*(b+a)*(b-a)=a*2 by rw [mul_assoc,mul_comm (b+a),hgap]]

private lemma sum_bound (n : ℕ) : (∑ j∈range n,term j)≤1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_range_succ']
    have h := sum_le_sum (s:=range n) (fun j _ => step j)
    rw [sum_range_sub'] at h
    have hh : 0≤v n := by dsimp [v]; positivity
    simpa [v,term] using (show (∑ j∈range n,term (j+1))+term 0≤1 by
      have h0 : v 0=1 := by norm_num [v]
      have ht : term 0=0 := by norm_num [term]
      rw [h0] at h; linarith)

private lemma term_summable : Summable term := summable_of_sum_range_le term_nonneg sum_bound

private lemma constant_eq : diagonalConstant =
    (eulerMascheroniConstant+log (4/π))/2-(4/π^2)*∑' j,term j := by
  have h := ((odd_reciprocal_square.mul_right ((eulerMascheroniConstant+log 2)/2)).sub
    (term_summable.hasSum.mul_right (1/2))).tsum_eq
  unfold diagonalConstant
  have he : (∑' j : ℕ,((2*(j:ℝ)+1)^2)⁻¹*((eulerMascheroniConstant+log 2-log (2*(j:ℝ)+1))/2)) =
    (π^2/8)*((eulerMascheroniConstant+log 2)/2)-(∑' j,term j)*(1/2) := by
    rw [← h]; apply tsum_congr; intro j; dsimp [term]; ring
  rw [he,log_div (by norm_num) pi_pos.ne',log_div (by norm_num) pi_pos.ne',
    show log 4=2*log 2 by rw [show (4:ℝ)=2^2 by norm_num,log_pow]; norm_num]
  field_simp; ring

/-- A rational lower estimate from the dyadic exponent and the first
term of the logarithm series in (x-1)/(x+1). -/
private def logLower (u : ℕ) : ℚ :=
  let k := u.log2
  let b : ℚ := 2^k
  k*(69314/100000)+2*(u-b)/(u+b)

private lemma logLower_le {u : ℕ} (hu : 0<u) : (logLower u:ℝ) ≤ log u := by
  let k := u.log2
  let b : ℝ := 2^k
  have hb : 0<b := by dsimp [b]; positivity
  have hub : b≤u := by dsimp only [b]; exact_mod_cast (Nat.le_log2 hu.ne').mp (le_refl k)
  have hz : 0≤(u:ℝ)/b-1 := sub_nonneg.mpr ((one_le_div hb).mpr hub)
  have h := le_log_one_add_of_nonneg hz
  rw [show 1+((u:ℝ)/b-1)=u/b by ring,log_div (by positivity) hb.ne'] at h
  have id' : 2*((u:ℝ)/b-1)/((u:ℝ)/b-1+2) = 2*((u:ℝ)-b)/(u+b) := by
    rw [show (u:ℝ)/b-1+2=(u+b)/b by field_simp; ring,
      show (u:ℝ)/b-1=(u-b)/b by field_simp]
    field_simp
  rw [id'] at h
  have he : log b=k*log 2 := log_pow ..
  rw [he] at h
  have hk := mul_le_mul_of_nonneg_left (show (69314/100000:ℝ)≤log 2 by linarith [log_two_gt_d9]) (Nat.cast_nonneg (α:=ℝ) k)
  dsimp [logLower]; push_cast
  change (k:ℝ)*(69314/100000)+2*((u:ℝ)-b)/(u+b) ≤ log u
  linarith only [h,hk]

private def rationalTerm (j : ℕ) : ℚ :=
  let u := 2*j+1
  logLower u/(u:ℚ)^2

set_option maxRecDepth 8000 in
private lemma certified_partial : (403/1000:ℚ) < ∑ j∈range 128, rationalTerm j := by decide +kernel

private lemma log_moment_lower : (403/1000:ℝ)<∑' j,term j := by
  have H := (Rat.cast_lt (K:=ℝ)).mpr certified_partial
  push_cast at H
  apply H.trans_le
  apply (sum_le_sum (g:=term) (fun j _ => ?_)).trans
    (term_summable.sum_le_tsum (range 128) (fun j _ => term_nonneg j))
  have hh := logLower_le (u:=2*j+1) (by omega)
  dsimp [rationalTerm,term]; push_cast at hh ⊢
  exact div_le_div_of_nonneg_right hh (sq_nonneg _)

private lemma gamma_upper : eulerMascheroniConstant < 586/1000 := by
  have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  have hh : harmonic 64<(4744/1000:ℚ) := by decide +kernel
  have hh' := (Rat.cast_lt (K:=ℝ)).mpr hh
  push_cast at hh'
  have hl : log 64=6*log 2 := by rw [show (64:ℝ)=2^6 by norm_num,log_pow]; norm_num
  norm_num only [eulerMascheroniSeq',Nat.cast_ofNat,OfNat.ofNat_ne_zero,ite_false] at h
  rw [hl] at h
  linarith only [hh',h,log_two_gt_d9]

private lemma log_ratio_upper : log (4/π)<258/1000 := by
  have hp : 0<(4:ℝ)/π := by positivity
  have h := log_le_sub_one_of_pos (sqrt_pos.mpr hp)
  rw [log_sqrt hp.le] at h
  have H : sqrt (4/π)<1129/1000 := (sqrt_lt' (by norm_num)).mpr (by
    rw [div_lt_iff₀ pi_pos]
    nlinarith only [pi_gt_d2])
  linarith

private lemma moment_upper : (∑' j,term j)≤78/100 := by
  apply term_summable.tsum_le_of_sum_range_le; intro n
  have hzero : term 0=0 := by norm_num [term]
  have h1 : term 1≤1/5 := by
    have H := log_le_sqrt (by norm_num : (0:ℝ)<3)
    have h : sqrt 3<(9/5:ℝ) := (sqrt_lt' (by norm_num)).mpr (by norm_num)
    norm_num [term]; linarith
  have hv : v 1≤58/100 := by
    have h : (50/29:ℝ) ≤ sqrt 3 := le_sqrt_of_sq_le (by norm_num)
    norm_num [v]
    apply (inv_le_comm₀ (by positivity) (by norm_num)).mpr
    norm_num [inv_div] at h ⊢
    exact h
  cases n with
  | zero => norm_num
  | succ n =>
    cases n with
    | zero => simp [hzero]; norm_num
    | succ n =>
      rw [sum_range_succ',sum_range_succ' (fun k => term (k+1))]
      have H := sum_le_sum (s:=range n) (fun j _ => step (j+1))
      rw [sum_range_sub' (fun k => v (k+1))] at H
      simp only [zero_add] at H
      have hnon : 0≤v (n+1) := by dsimp [v]; positivity
      have hr : (∑ j∈range n,term (j+1+1))≤v 1 := by linarith only [H,hnon]
      linarith only [hr,h1,hv,hzero]

/-- An explicit enclosure sufficient to compare the diagonal center with
the two signed class excursions. -/
theorem center_bounds : 0<diagonalConstant ∧ diagonalConstant<259/1000 := by
  rw [constant_eq]
  have hπ : 0<π^2 := sq_pos_of_pos pi_pos
  have h1 : 4/π^2<4/9 := (div_lt_div_iff₀ hπ (by norm_num)).mpr (by nlinarith only [pi_gt_three,sq_nonneg (π-3)])
  have hsq := mul_self_lt_mul_self pi_pos.le pi_lt_d4
  have h2 : (405/1000:ℝ)<4/π^2 := (lt_div_iff₀ hπ).mpr (by nlinarith only [hsq])
  have hlo := one_sub_inv_le_log_of_pos (by positivity : 0<(4:ℝ)/π)
  rw [inv_div] at hlo
  have hlog : 1/5<log (4/π) := by linarith only [hlo,pi_lt_d4]
  have hl := mul_le_mul h1.le moment_upper (tsum_nonneg term_nonneg) (by norm_num)
  have hu := mul_le_mul h2.le log_moment_lower.le (by norm_num) (by positivity)
  constructor
  · linarith only [one_half_lt_eulerMascheroniConstant,hlog,hl,h1]
  · linarith only [gamma_upper,log_ratio_upper,hu]

end Arxiv.«2501.03234».ThetaCenterBounds
#print axioms Arxiv.«2501.03234».ThetaCenterBounds.center_bounds
