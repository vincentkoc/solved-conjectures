import HosoyaIndexGcdDensity
import HosoyaSmallRankWeights

/-! Explicit bounds for the density of indices coprime to Fₙ+Lₙ₊₁. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Topology

private theorem small_count (K X : ℕ) :
    (sample (smallCommon K) X:ℝ) ≤ X*(((∑ p ∈ range (K^2), smallScore p : ℕ):ℝ)/1000000)+(K^2:ℕ) := by
  let S := (range (K^2)).filter fun p => p.Prime ∧ p∉excludedBases
  have sub : (Icc 1 X).filter (smallCommon K) ⊆ S.biUnion fun p => commonHits p X := by
    intro n hn
    obtain ⟨hx,hs⟩ := mem_filter.mp hn
    obtain ⟨p,lo,pr,hn,hu⟩ := hs
    have out : p∉excludedBases := fun bad => no_common_excluded bad hn hu
    exact mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨lo,pr,out⟩,mem_filter.mpr ⟨hx,hn,hu⟩⟩
  have c : sample (smallCommon K) X ≤ ∑ p ∈ S, (commonHits p X).card :=
    (card_le_card sub).trans card_biUnion_le
  have weights : ∑ p ∈ S, rankWeight p ≤ ((∑ p ∈ range (K^2), smallScore p : ℕ):ℝ)/1000000 := by
    calc
      _ ≤ ∑ p ∈ S, (smallScore p:ℝ)/1000000 := by
        apply sum_le_sum
        intro p hp
        exact weight_le_smallScore (mem_filter.mp hp).2.1 (mem_filter.mp hp).2.2
      _ = (∑ p ∈ S, (smallScore p:ℝ))/1000000 := by rw [sum_div]
      _ ≤ (∑ p ∈ range (K^2), (smallScore p:ℝ))/1000000 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; positivity)
      _ = _ := by simp only [Nat.cast_sum]
  have total : (S.card:ℝ) ≤ (K^2:ℕ) := by
    exact_mod_cast (show S.card ≤ K^2 by simpa using card_le_card (filter_subset (fun p => p.Prime ∧ p∉excludedBases) (range (K^2))))
  have bound : ∑ p ∈ S, ((commonHits p X).card:ℝ) ≤ ∑ p ∈ S, (X*rankWeight p+1) := by
    apply sum_le_sum
    intro p hp
    obtain ⟨_,pr,out⟩ := mem_filter.mp hp
    exact common_hits_le pr (by rintro rfl; exact out (by decide)) X
  rw [sum_add_distrib,←mul_sum] at bound
  simp only [sum_const,nsmul_eq_mul,mul_one] at bound
  have cc : (sample (smallCommon K) X:ℝ) ≤ ∑ p ∈ S, ((commonHits p X).card:ℝ) := by exact_mod_cast c
  exact cc.trans (bound.trans (add_le_add (mul_le_mul_of_nonneg_left weights (by positivity)) total))

private lemma small_count_4096 (X : ℕ) :
    (sample (smallCommon 64) X:ℝ) ≤ X*(298854/1000000)+4096 := by
  have h := small_count 64 X
  rw [show (64:ℕ)^2=4096 by decide,small_scores_total] at h
  exact_mod_cast h

/-- The large-prime tail plus all small-prime obstructions, with a power-saving
error when X=L³, P=L² and T=L. -/
theorem total_common_count (X P T : ℕ) (cut : X ≤ P*T) :
    (sample allCommon X:ℝ) ≤ (298854/1000000+13/384)*X + 4096 + P + 8*(T:ℝ)^2 := by
  have err : (sample allCommon X:ℝ) ≤ sample (smallCommon 64) X + (largeCommon 64 X).card := by
    exact_mod_cast (small_error 64 X).2
  have tail := large_common_tail (K:=64) (by decide) X P T cut
  norm_num at tail
  linarith [small_count_4096 X]

private def early (n : ℕ) := n%12=3 ∨ n%12=4 ∨ n%12=10
private instance (n : ℕ) : Decidable (early n) := by unfold early; infer_instance

private lemma early_hits {n : ℕ} (h : early n) : allCommon n := by
  have step (p : ℕ) (h₁ : p ∣ 12) (h₂ : p ∣ Nat.fib 12) (pr : p.Prime)
      (a : p ∣ n%12) (b : p ∣ lucasFibonacciSum (n%12)) : allCommon n := by
    have per : Function.Periodic (fun i => p ∣ i ∧ p ∣ lucasFibonacciSum i) 12 := by
      intro i
      apply propext
      change (p ∣ i+12 ∧ p ∣ lucasFibonacciSum (i+12)) ↔ _
      rw [Nat.dvd_add_left h₁,lucasFibonacciSum_dvd_shift_iff h₂]
    have hit := (per.map_mod_nat n) ▸ (show p ∣ n%12 ∧ p ∣ lucasFibonacciSum (n%12) from ⟨a,b⟩)
    intro cop
    exact pr.not_dvd_one (cop ▸ Nat.dvd_gcd hit.1 hit.2)
  have at_residue (p r : ℕ) (e : n%12=r) (h₁ : p ∣ 12) (h₂ : p ∣ Nat.fib 12) (pr : p.Prime)
      (a : p ∣ r) (b : p ∣ lucasFibonacciSum r) : allCommon n :=
    step p h₁ h₂ pr (e ▸ a) (e ▸ b)
  rcases h with h|h|h
  · exact at_residue 3 3 h (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact at_residue 2 4 h (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact at_residue 2 10 h (by decide) (by decide) (by decide) (by decide) (by decide)

private lemma lower_common (X : ℕ) (hx : 0 < X) :
    1/4-(12:ℝ)/X ≤ commonFreq X := by
  have le : sample early X ≤ sample allCommon X := by
    apply card_le_card
    intro n hn
    obtain ⟨hx,h⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hx,early_hits h⟩
  have per : Function.Periodic early 12 := by intro n; simp [early,Nat.add_mod_right]
  have e := (abs_le.mp (periodic_sample_error (by decide : 0 < 12) per X)).1
  rw [show Nat.count early 12=3 by decide +kernel] at e
  have xp : (0:ℝ) < X := by exact_mod_cast hx
  unfold commonFreq
  apply (le_div_iff₀ xp).mpr
  have l : (sample early X:ℝ) ≤ sample allCommon X := by exact_mod_cast le
  have id : (12:ℝ)/X*X=12 := by field_simp
  push_cast at e
  linarith only [e,l,id,show (1/4-12/(X:ℝ))*X=1/4*X-12/(X:ℝ)*X by ring]

private lemma upper_common {X : ℕ} (hx : 0 < X) :
    commonFreq X ≤ (298854/1000000+13/384+1/4096)+(4097+8*4096^2)/(X:ℝ) := by
  have cut : X ≤ (X/4096+1)*4096 := by omega
  have bound := total_common_count X (X/4096+1) 4096 cut
  push_cast at bound
  have d : ((X/4096:ℕ):ℝ) ≤ (X:ℝ)/4096 := by exact_mod_cast (Nat.cast_div_le (α:=ℝ) (m:=X) (n:=4096))
  have xp : (0:ℝ) < X := by exact_mod_cast hx
  apply (div_le_iff₀ xp).mpr
  rw [add_mul,div_mul_cancel₀ _ xp.ne']
  linarith

/-- The positive indices n coprime to their upper value have a natural density
strictly greater than two thirds and at most three quarters. -/
theorem index_coprime_density :
    ∃ δ : ℝ, 2/3 < δ ∧ δ ≤ 3/4 ∧ Tendsto
      (fun X : ℕ => (sample (fun n => n.Coprime (lucasFibonacciSum n)) X:ℝ)/X) atTop (𝓝 δ) := by
  obtain ⟨d,hd⟩ := common_frequency_converges
  have above : 1/4 ≤ d := by
    have lim := (tendsto_const_nhds (x:=(1/4:ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat (12:ℝ))
    apply le_of_tendsto_of_tendsto (by simpa only [sub_zero] using lim) hd
    filter_upwards [eventually_gt_atTop 0] with X hx using lower_common X hx
  have below : d ≤ (298854/1000000+13/384+1/4096:ℝ) := by
    have lim := (tendsto_const_nhds (x:=(298854/1000000+13/384+1/4096:ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (4097+8*4096^2:ℝ))
    apply le_of_tendsto_of_tendsto hd (by simpa only [add_zero] using lim)
    filter_upwards [eventually_gt_atTop 0] with X hx using upper_common hx
  refine ⟨1-d,by linarith,by linarith,?_⟩
  apply ((tendsto_const_nhds (x:=(1:ℝ))).sub hd).congr'
  filter_upwards [eventually_gt_atTop 0] with X hx
  have cnt := (Icc 1 X).card_filter_add_card_filter_not (fun n => n.Coprime (lucasFibonacciSum n))
  change sample (fun n => n.Coprime (lucasFibonacciSum n)) X+sample allCommon X=_ at cnt
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at cnt
  have cp : (sample (fun n => n.Coprime (lucasFibonacciSum n)) X:ℝ)+sample allCommon X=X := by exact_mod_cast cnt
  have nz : (X:ℝ)≠0 := by positivity
  change 1-(sample allCommon X:ℝ)/X=_
  field_simp
  linarith

/-- A prime upper value at a positive index passes the index coprimality test. -/
theorem coprime_of_prime_upper {n : ℕ} (hn : 0 < n) (hp : (lucasFibonacciSum n).Prime) :
    n.Coprime (lucasFibonacciSum n) := by
  have mono : StrictMono lucasFibonacciSum := fun _ _ lt =>
    Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.fib_mono lt.le))
      (Nat.fib_add_two_strictMono lt)
  have bound (j : ℕ) : j < lucasFibonacciSum j := by
    induction j with
    | zero => decide
    | succ j ih =>
      exact (Nat.succ_le_of_lt ih).trans_lt (mono (Nat.lt_succ_self j))
  exact (Nat.coprime_of_lt_prime hn.ne' (bound n) hp).symm

#print axioms coprime_of_prime_upper

#print axioms total_common_count
#print axioms index_coprime_density

end Arxiv.«2211.10788».IndexDivisors
