import ThetaShortReciprocalBlocks

/-! Dyadic discrepancy transfer for the original prime theta sum. -/
namespace Arxiv.«2501.03234».ThetaDyadicDiscrepancy
open Finset Filter Real ThetaShortReciprocalBlocks
noncomputable section
variable {p : ℕ} [Fact p.Prime]

private lemma join (a b c : ℕ) (hab : a≤b) (hbc : b≤c) :
    block p a b+block p b c=block p a c := by
  unfold block
  rw [←mul_add,sum_Ico_consecutive _ hab hbc]

private lemma tiled (n t : ℕ) :
    ∑ i∈range t,block p (2^i) (min n (2^(i+1))) = block p 0 (min n (2^t)) := by
  induction t with
  | zero =>
    simp only [sum_range_zero,pow_zero]
    rcases n with _|n
    · simp [block]
    · simp [block]
  | succ t ih =>
    rw [sum_range_succ,ih]
    have le : 2^t ≤ 2^(t+1) := Nat.pow_le_pow_right (by decide) (by omega)
    by_cases h : 2^t≤n
    · rw [min_eq_right h]; exact join _ _ _ (Nat.zero_le _) (le_min h le)
    · have h' : n≤2^t := by omega
      rw [min_eq_left h',min_eq_left (h'.trans le),show block p (2^t) n=0 by simp [block,Ico_eq_empty (not_lt.mpr h')]]
      simp

private lemma sqrt_sum (t : ℕ) : ∑ i∈range t,1/Real.sqrt ((i:ℝ)+1) ≤ 2*Real.sqrt t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ,Nat.cast_succ]
    have ht : 0≤(t:ℝ) := Nat.cast_nonneg _
    have hp : 0 < (t:ℝ)+1 := by positivity
    have hs := Real.sqrt_le_sqrt (show (t:ℝ)≤t+1 by linarith)
    have ha := Real.sq_sqrt ht
    have hb := Real.sq_sqrt hp.le
    have hd := sub_nonneg.mpr hs
    have hh : 1/Real.sqrt ((t:ℝ)+1) ≤ 2*(Real.sqrt ((t:ℝ)+1)-Real.sqrt t) := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mpr
      nlinarith only [ha,hb,sq_nonneg (Real.sqrt ((t:ℝ)+1)-Real.sqrt t)]
    linarith

theorem dyadic {A B : ℝ} (hA : 0≤A) (hB : 0≤B) (t : ℕ) (ht : p/2≤2^t)
    (H : ∀ i<t,∀ k< min (p/2) (2^(i+1)),∀ a,2^i≤a → a≤ min (p/2) (2^(i+1)) →
      ∀ n≤ min (p/2) (2^(i+1))-a,|∑ j∈range n,sgn p (a+j) k| ≤
        (2:ℝ)^i*(A+B/(((i:ℝ)+1)*Real.sqrt ((i:ℝ)+1)))) :
    |block p 0 (p/2)| ≤ 4*(p:ℝ)*(A*(t:ℝ)^2+2*B*Real.sqrt t) := by
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have one (i : ℕ) (hi : i<t) :
      |block p (2^i) (min (p/2) (2^(i+1)))| ≤
        4*(p:ℝ)*(A*((i:ℝ)+1)+B*(1/Real.sqrt ((i:ℝ)+1))) := by
    let N := min (p/2) (2^(i+1))
    have hN : N≤p/2 := min_le_left ..
    have hNp : 0<N := lt_min (Nat.div_pos (Fact.out : p.Prime).two_le (by decide)) (by positivity)
    have hNc : (N:ℝ)≤(2:ℝ)^(i+1) := by exact_mod_cast min_le_right (p/2) (2^(i+1))
    have hl := log_le_log (Nat.cast_pos.mpr hNp) hNc
    rw [log_pow,Nat.cast_succ] at hl
    have hlog : log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have hh : (harmonic N:ℝ)≤2*((i:ℝ)+1) := by
      have hI : 1 ≤ (i:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) i]
      nlinarith only [harmonic_le_one_add_log N,hl,mul_le_mul_of_nonneg_left hlog (by positivity : 0≤(i:ℝ)+1),hI]
    let v := A+B/(((i:ℝ)+1)*Real.sqrt ((i:ℝ)+1))
    have hv : 0≤v := by dsimp [v]; positivity
    have hI : 0<(i:ℝ)+1 := by positivity
    have hden : 0 < 2*((2^i:ℕ):ℝ)+1 := by positivity
    have hpow : (2:ℝ)^i ≤ 2*((2^i:ℕ):ℝ)+1 := by push_cast; linarith [show (0:ℝ)≤2^i by positivity]
    apply (block_bound (p:=p) (J:=2^i) hN (show 0≤(2:ℝ)^i*v by positivity) (H i hi)).trans
    apply (div_le_iff₀ hden).mpr
    have he : ((i:ℝ)+1)*v = A*((i:ℝ)+1)+B*(1/Real.sqrt ((i:ℝ)+1)) := by
      dsimp [v]; field_simp
    rw [←he]
    have hr := mul_le_mul hh hpow (by positivity : 0≤(2:ℝ)^i) (by positivity : 0≤2*((i:ℝ)+1))
    nlinarith only [mul_le_mul_of_nonneg_left hr (mul_nonneg (by positivity : 0≤2*(p:ℝ)) hv)]
  rw [←min_eq_left ht,←tiled]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum (fun i hi => one i (mem_range.mp hi))).trans
  rw [←mul_sum,sum_add_distrib,←mul_sum,←mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hn : ∑ i∈range t,((i:ℝ)+1) ≤ (t:ℝ)^2 := by
    apply (sum_le_sum (fun i hi => by exact_mod_cast mem_range.mp hi : ∀ i∈range t, (i:ℝ)+1≤t)).trans
    simp [sq]
  linarith only [mul_le_mul_of_nonneg_left hn hA,mul_le_mul_of_nonneg_left (sqrt_sum t) hB]

#print axioms dyadic
end
end Arxiv.«2501.03234».ThetaDyadicDiscrepancy
