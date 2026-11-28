import ThetaInitialCompletion

/-! A complete square-root Kloosterman estimate confines the witness to a shorter window. -/
namespace Arxiv.«2501.03234».ThetaSquareRootWindow
open Filter Real ThetaReciprocalCutoff ThetaReciprocalResonance ThetaInitialCompletion
noncomputable section

/-- The classical Weil bound. The multiplier of the inverse is nonzero. -/
def CompleteEstimate (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ t a : ZMod p,a≠0 → ‖kloosterman t a‖ ≤ 2*sqrt p

theorem length_of_signal {p N : ℕ} [Fact p.Prime] (hp : p%2=1) (hN : N<p)
    (hlog : 1 ≤ log (log (N:ℝ))) (hpos : 0<log (N:ℝ)) {a : ZMod p}
    (hs : signal N a) {B : ℝ} (hB : 0 ≤ B) (hK : ∀ t : ZMod p, ‖kloosterman t a‖ ≤ B) :
    (N:ℝ) < 402653184*B*(log p)^2*log (log p) := by
  have hpr := (Fact.out : p.Prime).pos
  have hposN : 0<(N:ℝ) := by
    by_contra! h
    have hn : N=0 := by exact_mod_cast (le_antisymm h (Nat.cast_nonneg N))
    simp [hn] at hpos
  have hu := log_le_log hposN (show (N:ℝ) ≤ p by exact_mod_cast hN.le)
  have hv := log_le_log hpos hu
  have hlogp : 1 ≤ log (p:ℝ) := by linarith [log_le_sub_one_of_pos hpos]
  have hh := (harmonic_le_one_add_log (p/2)).trans
    (add_le_add_right (log_le_log (show 0<((p/2:ℕ):ℝ) by
      exact_mod_cast Nat.div_pos (Fact.out : p.Prime).two_le (by decide))
      (show ((p/2:ℕ):ℝ) ≤ p by exact_mod_cast Nat.div_le_self p 2)) 1)
  have hcoef : 1+(harmonic (p/2):ℝ) ≤ 3*log p := by linarith
  have h := (div_lt_iff₀ (by positivity)).mp (hs.trans_le (bounded hp hN a hB hK))
  apply h.trans_le
  calc
    _ ≤ (3*log p*B)*(134217728*log p*log (log p)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hcoef hB)
        (mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) hv (by linarith) (by positivity))
        (by positivity) (by positivity)
    _ = _ := by ring

theorem square_root_witness :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      CompleteEstimate p → (S p:ℝ) ≤ (p:ℝ)*log p/100 →
        ∃ N : ℕ,exp (sqrt (log p)/512) ≤ N ∧
          (N:ℝ)<805306368*sqrt p*(log p)^2*log (log p) ∧ N<p ∧
          ∃ a : ZMod p,a≠0 ∧ signal N a := by
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [witness (by norm_num : (0:ℝ)<1),ht.eventually_ge_atTop (2048^2)] with p h hhu
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hK hS
  obtain ⟨N,⟨hlen,_,hn⟩,a,ha,hs⟩ := h hp ho hS
  have hreal : 0<(N:ℝ) := (exp_pos _).trans_le hlen
  have hlog := (le_log_iff_exp_le hreal).mpr hlen
  have hroot := sqrt_le_sqrt hhu
  change sqrt (2048^2:ℝ) ≤ sqrt (log (p:ℝ)) at hroot
  rw [sqrt_sq (by norm_num : (0:ℝ) ≤ 2048)] at hroot
  have hu : 3 ≤ log (N:ℝ) := by linarith
  have hv : 1 ≤ log (log (N:ℝ)) := (le_log_iff_exp_le (by linarith)).mpr (exp_one_lt_three.le.trans hu)
  have H := length_of_signal (Nat.odd_iff.mp ho) hn hv (by linarith) hs
    (show 0 ≤ 2*sqrt (p:ℝ) by positivity) (fun t => hK t a ha)
  exact ⟨N,hlen,H.trans_eq (by ring),hn,a,ha,hs⟩

#print axioms length_of_signal
#print axioms square_root_witness
end
end Arxiv.«2501.03234».ThetaSquareRootWindow
