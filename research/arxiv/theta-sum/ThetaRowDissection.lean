import ThetaSmoothConditionalModel
import ThetaDenominatorTails

/-! Exact dissection of the already truncated reciprocal model into consecutive denominator bands. -/
namespace Arxiv.«2501.03234».ThetaRowDissection
open Finset ThetaSmoothConditionalModel ThetaRowCorrelations ThetaDenominatorTails
noncomputable section

def after (T : ℕ) (W : Window) : Window := ⟨above T W.width,W.weightCutoff⟩

theorem zero {T : ℕ} {W : Window} (hz : ∀ d,d ≤ T → W.width d=0) (n : ℕ) : rowModel T W n=0 := by
  unfold rowModel low;apply sum_eq_zero;intro d hd;simp [hz d (mem_Icc.mp hd).2,row]

theorem split {A B : ℕ} (hab : A ≤ B) (W : Window) (n : ℕ) :
    rowModel B W n=rowModel A W n+rowModel B (after A W) n := by
  let f := fun d : ℕ => (ThetaReciprocalBlocks.commonWeight W.weightCutoff d/d)*row d (W.width d) n
  have hs : (Icc 2 B).filter (· ≤ A)=Icc 2 A := by ext d;simp only [mem_filter,mem_Icc];omega
  have hz : rowModel B (after A W) n=∑ d∈(Icc 2 B).filter (fun d => ¬d ≤ A),f d := by
    rw [sum_filter];unfold rowModel low
    apply sum_congr rfl;intro d _;by_cases h : d ≤ A <;> simp [f,after,above,h,row]
  change (∑ d∈Icc 2 B,f d)=(∑ d∈Icc 2 A,f d)+_
  rw [hz,←hs,sum_filter_add_sum_filter_not]

theorem telescoping (c : ℕ → ℕ) (hc : ∀ i,c i ≤ c (i+1)) (W : Window) (n k : ℕ) :
    rowModel (c k) W n=rowModel (c 0) W n+∑ i∈range k,rowModel (c (i+1)) (after (c i) W) n := by
  induction k with
  | zero => simp
  | succ k ih => rw [split (hc k),ih,sum_range_succ,add_assoc]

#print axioms telescoping
end
end Arxiv.«2501.03234».ThetaRowDissection
