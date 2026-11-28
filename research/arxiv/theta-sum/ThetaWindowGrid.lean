import ThetaAlmostPeriodicWindows
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! A grid of O_K(log X) integer lengths upgrades a per-length exceptional
set bound to one set of starts valid for all polynomially long windows. -/
namespace Arxiv.«2501.03234».ThetaWindowGrid
open Real Finset Filter ThetaWindowApproximation ThetaAlmostPeriodicWindows
noncomputable section

def grid (X K : ℕ) : Finset ℕ :=
  ((range (Nat.log 2 X+1)) ×ˢ (range (2*K+1))).image (fun ij => min X (ij.2*2^ij.1))

theorem size (X K : ℕ) : (grid X K).card≤(Nat.log 2 X+1)*(2*K+1) := by
  simpa [grid] using (card_image_le (f:=fun ij : ℕ×ℕ => min X (ij.2*2^ij.1))
    (s:=range (Nat.log 2 X+1) ×ˢ range (2*K+1)))

/-- Lengths bracketing H differ from H by at most H/K. -/
theorem bracket {X K H : ℕ} (hK : 0<K) (hkH : K≤H) (hHX : H≤X) :
    ∃ A∈grid X K, ∃ B∈grid X K, 0<A ∧ A≤H ∧ H≤B ∧ B≤X ∧
      K*(H-A)≤H ∧ K*(B-H)≤H := by
  let i := Nat.log 2 (H/K)
  let u := 2^i
  have hu : 0<u := pow_pos (by decide) _
  have hquot : 0<H/K := Nat.div_pos hkH hK
  have hlow : u≤H/K := Nat.pow_log_le_self _ hquot.ne'
  have hhigh : H/K<2*u := by simpa [u,i,pow_succ,Nat.mul_comm] using Nat.lt_pow_succ_log_self (b:=2) (by decide) (H/K)
  have huK : K*u≤H := (Nat.mul_comm K u).le.trans ((Nat.le_div_iff_mul_le hK).mp hlow)
  have hHtop : H<(2*K)*u := by
    simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using (Nat.div_lt_iff_lt_mul hK).mp hhigh
  let j := H/u
  have hj : j<2*K := (Nat.div_lt_iff_lt_mul hu).mpr hHtop
  have hj₀ : 0<j := Nat.div_pos (by nlinarith only [huK,Nat.mul_le_mul_right u hK]) hu
  have hlo : j*u≤H := Nat.div_mul_le_self H u
  have hhi : H<(j+1)*u := by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ H hu
  have hi : i<Nat.log 2 X+1 := Nat.lt_succ_of_le (Nat.log_mono_right ((Nat.div_le_self H K).trans hHX))
  have member {v : ℕ} (hv : v≤2*K) : min X (v*u)∈grid X K :=
    mem_image.mpr ⟨(i,v),mem_product.mpr ⟨mem_range.mpr hi,mem_range.mpr (by omega)⟩,rfl⟩
  have hlmem := member hj.le
  rw [min_eq_right (hlo.trans hHX)] at hlmem
  refine ⟨j*u,hlmem,min X ((j+1)*u),member (by omega),Nat.mul_pos hj₀ hu,hlo,le_min hHX hhi.le,min_le_left ..,?_,?_⟩
  · apply (Nat.mul_le_mul_left K ?_).trans huK
    rw [Nat.add_mul,one_mul] at hhi;omega
  · apply (Nat.mul_le_mul_left K ?_).trans huK
    have le : min X ((j+1)*u)≤H+u := (min_le_right ..).trans (by rw [Nat.add_mul,one_mul]; omega)
    omega

def PerLength (β : ℝ) (P : ℕ → ℕ → ℕ → Prop) :=
  ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, Admits β X H →
    ((exceptional X (fun n => P X n H)).card:ℝ)≤X/(log X)^2

theorem uniform {β : ℝ} {P : ℕ → ℕ → ℕ → Prop} (h : PerLength β P) (K : ℕ) :
    Almost (fun X n => ∀ H∈grid X K, Admits β X H → P X n H) := by
  classical
  intro ε hε
  let C := (1/log 2+1)*(2*(K:ℝ)+1)
  have hl₂ : 0<log (2:ℝ) := log_pos (by norm_num)
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h,hlog.eventually_ge_atTop 1,hlog.eventually_ge_atTop (C/ε)] with X hh hx hx'
  change 1≤log (X:ℝ) at hx
  change C/ε≤log (X:ℝ) at hx'
  have hl : 0<log (X:ℝ) := by linarith
  let G := (grid X K).filter (Admits β X)
  let bad (H : ℕ) := exceptional X (fun n => P X n H)
  have hs : exceptional X (fun n => ∀ H∈grid X K, Admits β X H → P X n H)⊆G.biUnion bad := by
    intro n hn
    obtain ⟨hn,he⟩ := mem_exceptional.mp hn
    push Not at he
    obtain ⟨H,hgrid,hok,hfail⟩ := he
    exact mem_biUnion.mpr ⟨H,mem_filter.mpr ⟨hgrid,hok⟩,mem_exceptional.mpr ⟨hn,hfail⟩⟩
  have hcard : (G.card:ℝ)≤C*log X := by
    have hsz := (card_le_card (filter_subset (Admits β X) (grid X K))).trans (size X K)
    have hsz' := (Nat.cast_le (α:=ℝ)).mpr hsz
    push_cast at hsz'
    apply hsz'.trans
    have hL := natLog_le_logb X 2
    rw [logb] at hL
    norm_num only [Nat.cast_ofNat] at hL
    have hcoeff : (Nat.log 2 X:ℝ)+1≤(1/log 2+1)*log X := by
      rw [add_mul,one_mul,one_div_mul_eq_div];linarith only [hL,hx]
    dsimp only [C];rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hc := (Nat.cast_le (α:=ℝ)).mpr ((card_le_card hs).trans card_biUnion_le)
  push_cast at hc
  apply hc.trans
  calc (∑ H∈G,((bad H).card:ℝ)) ≤ ∑ _H∈G,(X:ℝ)/(log X)^2 := sum_le_sum (fun H hH => hh H (mem_filter.mp hH).2)
       _ = (G.card:ℝ)*((X:ℝ)/(log X)^2) := by simp
       _ ≤ (C*log X)*((X:ℝ)/(log X)^2) := mul_le_mul_of_nonneg_right hcard (by positivity)
       _ = (C/log X)*X := by field_simp
       _ ≤ ε*X := mul_le_mul_of_nonneg_right ((div_le_iff₀ hl).mpr (by
         have h' := (div_le_iff₀ hε).mp hx';linarith)) (Nat.cast_nonneg _)

#print axioms bracket
#print axioms uniform
end
end Arxiv.«2501.03234».ThetaWindowGrid
