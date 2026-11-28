import ThetaManyReciprocalSums
import ThetaSquareRootWindow

/-! Logarithmic packing of separated reciprocal-sum lengths near the square-root scale. -/
namespace Arxiv.«2501.03234».ThetaResonancePacking
open Finset Filter Real ThetaResonantLengths ThetaSquareRootWindow ThetaReciprocalResonance
noncomputable section

theorem packing (E : Finset ℕ) (hE : separated E) {L U : ℝ} (hLU : L≤U)
    (h : ∀ n∈E, 0<n ∧ L≤log n ∧ log n≤U) : (E.card:ℝ) ≤ 2*(U-L)+1 := by
  classical
  induction E using Finset.induction_on_max generalizing U with
  | empty => simp;linarith
  | insert a s hmax ih =>
    have ha := h a (mem_insert_self ..)
    have han : a∉s := fun hm => (lt_irrefl _ (hmax a hm))
    rw [card_insert_of_notMem han,Nat.cast_succ]
    rcases s.eq_empty_or_nonempty with rfl|hs
    · simp;linarith
    have gap (x : ℕ) (hx : x∈s) : log (x:ℝ) ≤ log a-1/2 := by
      have hx₀ := (h x (mem_insert_of_mem hx)).1
      have hg := hE x a (mem_insert_of_mem hx) (mem_insert_self ..) (hmax x hx)
      have hl := log_le_log (show 0<2*(x:ℝ) by exact mul_pos (by norm_num) (Nat.cast_pos.mpr hx₀))
        (show 2*(x:ℝ) ≤ a by exact_mod_cast hg)
      rw [log_mul (by norm_num) (Nat.cast_ne_zero.mpr hx₀.ne')] at hl
      linarith [log_two_gt_d9]
    obtain ⟨x,hx⟩ := hs
    have hl := (h x (mem_insert_of_mem hx)).2.1.trans (gap x hx)
    have hh := ih (fun n m hn hm => hE n m (mem_insert_of_mem hn) (mem_insert_of_mem hm))
      hl (fun n hn => ⟨(h n (mem_insert_of_mem hn)).1,(h n (mem_insert_of_mem hn)).2.1,gap n hn⟩)
    linarith only [hh,ha.2.2]

theorem upper_logs : ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ δ B : ℝ, 0<B → (∀ t a : ZMod p,a≠0 → ‖ThetaReciprocalCutoff.kloosterman t a‖ ≤ 2*B) →
      ∀ N∈lengths p δ,
      0<N ∧ log (N:ℝ) ≤ log B + 32*log (log p) := by
  classical
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop (2048^2),(tendsto_log_atTop.comp ht).eventually_ge_atTop 1]
    with p hp' hv'
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro δ B hB hK N hN
  obtain ⟨_,⟨hlen,_,hn⟩,a,ha,hs⟩ := mem_filter.mp hN
  have hreal : 0<(N:ℝ) := (exp_pos _).trans_le hlen
  have hlog := (le_log_iff_exp_le hreal).mpr hlen
  have hroot := sqrt_le_sqrt hp'
  change sqrt (2048^2:ℝ) ≤ sqrt (log (p:ℝ)) at hroot
  rw [sqrt_sq (by norm_num : (0:ℝ) ≤ 2048)] at hroot
  have hu : 3 ≤ log (N:ℝ) := by linarith
  have hv := (le_log_iff_exp_le (by linarith : 0<log (N:ℝ))).mpr (exp_one_lt_three.le.trans hu)
  have H := length_of_signal (Nat.odd_iff.mp ho) hn hv (by linarith) hs
    (show 0 ≤ 2*B by positivity) (fun t => hK t a ha)
  have hU : log (N:ℝ) ≤ log ((2:ℝ)^30*B*(log p)^2*log (log p)) := by
    apply log_le_log hreal
    change 1≤log (log (p:ℝ)) at hv'
    apply H.le.trans
    norm_num
    have hnn : 0 ≤ B*(Real.log (p:ℝ))^2*Real.log (Real.log (p:ℝ)) := by positivity
    nlinarith only [hnn]
  have hp₀ : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hu₀ : 0<log (p:ℝ) := by change 2048^2≤log (p:ℝ) at hp';linarith
  change 1≤log (log (p:ℝ)) at hv'
  have hv₀ : 0<log (log (p:ℝ)) := by linarith
  rw [log_mul (by positivity) hv₀.ne',log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity),log_pow,log_pow] at hU
  push_cast at hU
  refine ⟨Nat.cast_pos.mp hreal,?_⟩
  linarith [log_two_lt_d9,log_le_sub_one_of_pos hv₀]

#print axioms packing
#print axioms upper_logs
end
end Arxiv.«2501.03234».ThetaResonancePacking
