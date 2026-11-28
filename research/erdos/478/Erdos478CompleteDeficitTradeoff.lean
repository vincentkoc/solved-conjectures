import Erdos478ManyCompleteWitnesses
import Erdos478CompleteGapRounding
import Erdos478CompleteCountRounding

/-!
# An every-cutoff tradeoff for missing factorial residues

Increasing the number of primes counted costs part of the logarithmic
prime budget. The saving from the gap cutoff itself permits the
individual-prime coefficient two even when the count tends to infinity.
-/

namespace Erdos478.EffectiveResolvent
open Filter Real Finset
open scoped Classical

/-- The same list of even gap polynomials splits completely and without
repeated roots at each prime counted through X. -/
theorem abundant_complete_gaps {c α β : ℝ} (hc : 0<c) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hline : c/2+2*α ≤ 1) (hsub : β<c/4) :
    ∀ᶠ X : ℕ in atTop, let T := log (log X)
      0<log T ∧ ∃ n : ℕ, 0<n ∧ c*T ≤ (n:ℝ)*(n+1)*log T ∧
        exp (exp (α*T+β*(T/log T)*log (log T))) ≤
          (((range (X+1)).filter (CompleteEvenWitness n)).card : ℝ) := by
  let γ := (2*β+c/2)/2
  have hγ : γ<c/2 := by dsimp [γ]; linarith
  have hslack : 0<γ-2*β := by dsimp [γ]; linarith
  have ht : Tendsto (fun X : ℕ => log (log X)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h₁ := ht.eventually (rounded_complete_gaps hc hγ)
  have ht' := tendsto_log_atTop.comp ht
  have ht'' := tendsto_log_atTop.comp ht'
  filter_upwards [h₁,ht.eventually_ge_atTop 1,ht'.eventually_ge_atTop 1,
    ht''.eventually_ge_atTop (max 0 (2*log 4/(γ-2*β))),eventually_ge_atTop (2:ℕ)]
    with X hX hT hl hs hx
  let T := log (log X)
  change 1 ≤ T at hT
  change 1 ≤ log T at hl
  change max 0 (2*log 4/(γ-2*β)) ≤ log (log T) at hs
  obtain ⟨hll,hs⟩ := max_le_iff.mp hs
  have hpay := (div_le_iff₀ hslack).mp hs
  let w := T/log T
  have hlog : 0<log T := by linarith
  have hw : 1 ≤ w := (le_div_iff₀ hlog).mpr (by linarith [log_le_sub_one_of_pos (by linarith : 0<T)])
  have hws : log (log T) ≤ w*log (log T) := by
    simpa using mul_le_mul_of_nonneg_right hw hll
  have hpay' : 2*log 4 ≤ (γ-2*β)*(w*log (log T)) := by
    nlinarith only [hpay,mul_le_mul_of_nonneg_left hws hslack.le]
  obtain ⟨n,hn,hdef,hcost⟩ := hX
  change ((n:ℝ)*(n+1)+38)*log (2*n+4) ≤ c/2*T-γ*w*log (log T) at hcost
  let a := α*T+β*w*log (log T)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨L,hcount,hL⟩ := rounded_witness_count ha
  have hceil : completeCeiling n L ≤ X := by
    apply nat_ceiling_within (by omega) (by omega)
    push_cast
    change _ ≤ T
    dsimp [a] at hL
    nlinarith only [hcost,hL,hpay',mul_le_mul_of_nonneg_right hline (by linarith : 0 ≤ T)]
  refine ⟨hlog,n,hn,hdef,hcount.trans ?_⟩
  have hcnt : 2^L < ((range (X+1)).filter (CompleteEvenWitness n)).card :=
    (many_complete_witnesses n L hn).trans_le
      (card_le_card (filter_subset_filter _ (range_mono (Nat.add_le_add_right hceil 1))))
  exact_mod_cast hcnt.le

/-- Count primes by the missing nonzero residues of precisely the
factorial image in the pinned Erdős statement. -/
theorem abundant_complete_deficit {c α β : ℝ} (hc : 0<c) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hline : c/2+2*α ≤ 1) (hsub : β<c/4) :
    ∀ᶠ X : ℕ in atTop, let T := log (log X)
      exp (exp (α*T+β*(T/log T)*log (log T))) ≤
        (((range (X+1)).filter fun p => p.Prime ∧ c*T ≤
          (p-1-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ)*log T).card : ℝ) := by
  filter_upwards [abundant_complete_gaps hc hα hβ hline hsub] with X hX
  obtain ⟨hlog,n,_,hsize,hcount⟩ := hX
  apply hcount.trans (Nat.cast_le.mpr (card_le_card ?_))
  intro p hp
  obtain ⟨hpX,hp,_,_,hdef⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨hpX,hp,hsize.trans (mul_le_mul_of_nonneg_right ?_ hlog.le)⟩
  exact_mod_cast (by omega : n*(n+1) ≤ p-1-((Ico 1 p).image (fun j => j.factorial % p)).card)

theorem abundant_double_deficit {β : ℝ} (hβ : 0 ≤ β) (h : β<1/2) :
    ∀ᶠ X : ℕ in atTop, let T := log (log X)
      exp (exp (β*(T/log T)*log (log T))) ≤
        (((range (X+1)).filter fun p => p.Prime ∧ 2*T ≤
          (p-1-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ)*log T).card : ℝ) := by
  simpa using abundant_complete_deficit (c := 2) (α := 0) (by norm_num) le_rfl hβ
    (by norm_num) (by linarith)

#print axioms abundant_complete_gaps
#print axioms abundant_complete_deficit
#print axioms abundant_double_deficit
end Erdos478.EffectiveResolvent
