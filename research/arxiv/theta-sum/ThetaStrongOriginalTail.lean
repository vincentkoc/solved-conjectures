import ThetaStrongPrimeTail

/-! Prime-normalized exceptional counts for the signed theta sum itself. -/
namespace Arxiv.«2501.03234».ThetaStrongOriginalTail
open Finset Filter Real ThetaPrimeDensity ThetaStrongDeviation ThetaStrongPrimeTail
noncomputable section

private theorem absorb (A : ℝ) (hA : 0<A) : ∀ᶠ X : ℕ in atTop,
    A*log X≤exp (rate X/2048) := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hz := tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually_ge_atTop 1,hz.eventually_ge_atTop (log A),
    hz.eventually_ge_atTop (2*4096^2)] with X hL hA' hbig
  simp only [Function.comp_apply] at hL hA' hbig
  let L := log (X:ℝ)
  let z := log L
  have hLp : 0<L := by change 0<log (X:ℝ);linarith
  have hp : 0≤z := log_nonneg hL
  have he := pow_div_factorial_le_exp z hp 2
  rw [exp_log hLp] at he
  norm_num [Nat.factorial] at he
  have hh : 4096^2*z≤L := by
    change 2*4096^2≤z at hbig
    nlinarith only [he,mul_le_mul_of_nonneg_right hbig hp]
  have hg : 4096*z≤rate X := by
    change _ ≤ sqrt (L*z)
    apply (le_sqrt (by positivity) (mul_nonneg hLp.le hp)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hh hp]
  calc
    _ = exp (log A+z) := by rw [exp_add,exp_log hA,show exp z=L from exp_log hLp]
    _ ≤ _ := exp_le_exp.mpr (by change log A≤z at hA';linarith only [hA',hg])

/-- For any fixed relative deviation, the proportion among primes is eventually
at most `exp (-sqrt (log X * log (log X)) / 2048)`. -/
theorem original {ε : ℝ} (hε : 0<ε) : ∀ᶠ X : ℕ in atTop,
    ((primeSet (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-(p:ℝ)*log p/2|) X).card:ℝ) ≤
      Nat.primeCounting X*exp (-rate X/2048) := by
  classical
  obtain ⟨D,hD,HH⟩ := endpoint hε
  let c := log 2/2
  have hc : 0<c := div_pos (log_pos (by norm_num)) (by norm_num)
  have hA : 0<D/c := div_pos hD hc
  filter_upwards [HH,prime_count_lower,absorb (D/c) hA] with X hH hcount habs
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
    _ ≤ Nat.primeCounting X*exp (rate X/2048)*exp (-rate X/1024) :=
      mul_le_mul_of_nonneg_right (hDX.trans (mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg _))) (exp_pos _).le
    _ = _ := by rw [mul_assoc,← exp_add];congr 2;ring

/-- In particular, the same fraction bounds the primes where any fixed lower
coefficient below one half fails, including the nonpositive primes. -/
theorem lower {c : ℝ} (hc : c<1/2) : ∀ᶠ X : ℕ in atTop,
    ((exceptions c X).card:ℝ) ≤ Nat.primeCounting X*exp (-rate X/2048) := by
  classical
  filter_upwards [original (sub_pos.mpr hc)] with X hX
  apply (Nat.cast_le.mpr (card_le_card (show exceptions c X⊆_ from ?_))).trans hX
  intro p hp
  simp only [exceptions,primeSet,mem_filter] at hp ⊢
  refine ⟨hp.1,?_⟩
  exact (show (1/2-c)*(p:ℝ)*log p≤-((S p:ℝ)-p*log p/2) by linarith only [hp.2]).trans (neg_le_abs _)

/-- The exceptional fraction for any lower coefficient beats every fixed
stretched exponential in the square root of the logarithm. -/
theorem every_fixed_rate {c : ℝ} (hc : c<1/2) (A : ℝ) (hA : 0<A) : ∀ᶠ X : ℕ in atTop,
    ((exceptions c X).card:ℝ) ≤ Nat.primeCounting X*exp (-A*sqrt (log X)) := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [lower hc,hlog.eventually_ge_atTop 1,
    (tendsto_log_atTop.comp hlog).eventually_ge_atTop ((2048*A)^2)] with X hX hL hz
  simp only [Function.comp_apply] at hL hz
  apply hX.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (Nat.cast_nonneg _))
  have hh : 2048*A ≤ sqrt (log (log (X:ℝ))) :=
    (le_sqrt (by positivity) (log_nonneg hL)).mpr hz
  rw [rate,sqrt_mul (by linarith : 0≤log (X:ℝ))]
  nlinarith only [mul_le_mul_of_nonneg_left hh (sqrt_nonneg (log (X:ℝ)))]

/-- Count failures of the exact linear comparison in the pinned lower conjecture.
The additive constant depends only on its natural-number parameter. -/
theorem pinned_failures (n : ℕ) : ∃ M : ℕ, ∀ᶠ X : ℕ in atTop,
    ((primeSet (fun p => Odd p ∧ ¬ (n:ℤ)*p<S p) X).card:ℝ) ≤
      M+Nat.primeCounting X*exp (-rate X/2048) := by
  classical
  have ht := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (4*(n:ℝ))
  obtain ⟨M,hM⟩ := eventually_atTop.mp ht
  refine ⟨M,?_⟩
  filter_upwards [lower (by norm_num : (1:ℝ)/4<1/2)] with X hX
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

#print axioms pinned_failures
#print axioms every_fixed_rate
#print axioms original
#print axioms lower
end
end Arxiv.«2501.03234».ThetaStrongOriginalTail
