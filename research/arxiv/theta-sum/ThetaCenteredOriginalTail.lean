import ThetaCenteredEndpoint

/-! An exceptional proportion with exponent three quarters for the original signed sum. -/
namespace Arxiv.«2501.03234».ThetaCenteredOriginalTail
set_option autoImplicit false
open Finset Real Filter ThetaPrimeDensity ThetaCenteredDeviation ThetaCenteredEndpoint
noncomputable section

private theorem absorb (A : ℝ) (hA : 0<A) {a : ℝ} (ha : 0<a) : ∀ᶠ X : ℕ in atTop,
    A*log X≤exp (a*rate X) := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hz := tendsto_log_atTop.comp hlog
  have hsmall := hlog.eventually ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<3/4)).bound (show 0<a/2 by positivity))
  filter_upwards [hsmall,hlog.eventually_ge_atTop 1,hz.eventually_ge_atTop (log A)] with X hs hL hA'
  change 1≤log (X:ℝ) at hL
  change log A≤log (log (X:ℝ)) at hA'
  change ‖log (log (X:ℝ))‖≤a/2*‖(log (X:ℝ))^(3/4:ℝ)‖ at hs
  have hLp : 0<log (X:ℝ) := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (rpow_nonneg hLp.le _),←rate_eq hLp] at hs
  calc _ = exp (log A+log (log (X:ℝ))) := by rw [exp_add,exp_log hA,exp_log hLp]
       _ ≤ _ := exp_le_exp.mpr (by linarith only [hA',hs])

/-- For each fixed relative error, the prime-normalized exception count has a
three-quarter-power logarithmic saving at every sufficiently large endpoint. -/
theorem original {ε : ℝ} (hε : 0<ε) : ∃ a : ℝ, 0<a ∧ ∀ᶠ X : ℕ in atTop,
    ((primeSet (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-(p:ℝ)*log p/2|) X).card:ℝ) ≤
      Nat.primeCounting X*exp (-a*(log X:ℝ)^(3/4:ℝ)) := by
  classical
  obtain ⟨a,D,ha,hD,HH⟩ := endpoint hε
  let c := log 2/2
  have hc : 0<c := div_pos (log_pos (by norm_num)) (by norm_num)
  have hA : 0<D/c := div_pos hD hc
  refine ⟨a/2,by positivity,?_⟩
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [HH,prime_count_lower,absorb (D/c) hA (show 0<a/2 by positivity),hlog.eventually_ge_atTop 1] with X hH hcount habs hL
  rw [←rate_eq (by change 1≤log (X:ℝ) at hL;linarith)]
  have hsub : primeSet (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|) X ⊆
      primeSet (fun p => ε*log p≤|(S p:ℝ)/p-log p/2|) X := by
    intro p hp
    simp only [primeSet,mem_filter,Nat.mem_primesLE] at hp ⊢
    refine ⟨hp.1,?_⟩
    have hp' : 0<(p:ℝ) := by exact_mod_cast hp.1.2.pos
    have he : ((S p:ℝ)/p-log p/2)*p=(S p:ℝ)-p*log p/2 := by field_simp
    apply (mul_le_mul_iff_left₀ hp').mp
    calc ε*log p*(p:ℝ) = ε*(p:ℝ)*log p := by ring
         _ ≤ _ := hp.2
         _ = _ := by rw [← he,abs_mul,abs_of_pos hp']
  have hDX : D*X≤Nat.primeCounting X*(D/c*log X) := by
    have ht := mul_le_mul_of_nonneg_left hcount hA.le
    change D/c*(c*(X:ℝ))≤_ at ht
    calc _ = D/c*(c*(X:ℝ)) := by field_simp
         _ ≤ _ := ht.trans_eq (by ring)
  apply (Nat.cast_le.mpr (card_le_card hsub)).trans (hH.trans ?_)
  calc
    _ ≤ Nat.primeCounting X*exp (a/2*rate X)*exp (-(a*rate X)) :=
      mul_le_mul_of_nonneg_right (hDX.trans (mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg _))) (exp_pos _).le
    _ = _ := by rw [mul_assoc,← exp_add];congr 2;ring

/-- In particular, the same fraction bounds the primes where any fixed lower
coefficient below one half fails, including the nonpositive primes. -/
theorem lower {c : ℝ} (hc : c<1/2) : ∃ a : ℝ, 0<a ∧ ∀ᶠ X : ℕ in atTop,
    ((exceptions c X).card:ℝ) ≤ Nat.primeCounting X*exp (-a*(log X:ℝ)^(3/4:ℝ)) := by
  classical
  obtain ⟨a,ha,h⟩ := original (sub_pos.mpr hc)
  refine ⟨a,ha,?_⟩
  filter_upwards [h] with X hX
  apply (Nat.cast_le.mpr (card_le_card (show exceptions c X⊆_ from ?_))).trans hX
  intro p hp
  simp only [exceptions,primeSet,mem_filter] at hp ⊢
  refine ⟨hp.1,?_⟩
  exact (show (1/2-c)*(p:ℝ)*log p≤-((S p:ℝ)-p*log p/2) by linarith only [hp.2]).trans (neg_le_abs _)

/-- One exponent coefficient works for every integer slope in the pinned lower conjecture. -/
theorem pinned_failures : ∃ a : ℝ, 0<a ∧ ∀ n : ℕ, ∃ M : ℕ, ∀ᶠ X : ℕ in atTop,
    ((primeSet (fun p => Odd p ∧ ¬ (n:ℤ)*p<S p) X).card:ℝ) ≤
      M+Nat.primeCounting X*exp (-a*(log X:ℝ)^(3/4:ℝ)) := by
  classical
  obtain ⟨a,ha,h⟩ := lower (by norm_num : (1:ℝ)/4<1/2)
  refine ⟨a,ha,?_⟩
  intro n
  have ht := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (4*(n:ℝ))
  obtain ⟨M,hM⟩ := eventually_atTop.mp ht
  refine ⟨M,?_⟩
  filter_upwards [h] with X hX
  let E := primeSet (fun p => Odd p ∧ ¬ (n:ℤ)*p<S p) X
  have hsub : E⊆range M ∪ exceptions (1/4) X := by
    intro p hp
    rcases lt_or_ge p M with hl|hl
    · exact mem_union_left _ (mem_range.mpr hl)
    · apply mem_union_right
      simp only [E,primeSet,mem_filter,not_lt] at hp
      simp only [exceptions,primeSet,mem_filter]
      refine ⟨hp.1,?_⟩
      have hlog : 4*(n:ℝ)≤log (p:ℝ) := hM p hl
      have hs : (S p:ℝ)≤(n:ℝ)*(p:ℝ) := by exact_mod_cast hp.2.2
      linarith only [hs,mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg p)]
  have hc : (E.card:ℝ)≤M+((exceptions (1/4) X).card:ℝ) := by
    exact_mod_cast (card_le_card hsub).trans ((card_union_le ..).trans_eq (by rw [card_range]))
  exact hc.trans (add_le_add_right hX _)

#print axioms original
#print axioms lower
#print axioms pinned_failures
end
end Arxiv.«2501.03234».ThetaCenteredOriginalTail
