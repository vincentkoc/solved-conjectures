import Erdos478LeastPrimeCollision
import Erdos478HitSetDensities
import Erdos478FrobeniusBandVariance
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # The shortest factorial collision has a limiting probability distribution -/

namespace Erdos478.FirstCollision
open Finset Filter Topology BinaryGap FrobeniusCounts GapSieve GapDensity ConditionalGaps FrobeniusBands
open scoped Classical
noncomputable section

theorem first_limit_all (pit : DegreeOnePrimeIdealTheorem) (l : ℕ) :
    Tendsto (fun X => fraction X (fun p => First p l)) atTop (𝓝 (firstDensity l)) := by
  by_cases h : 2≤l
  · exact first_limit pit h
  · simp only [firstDensity,if_neg h]
    apply (tendsto_const_nhds (x:=(0:ℝ))).congr
    intro X
    have no (p : ℕ) (hp : p.Prime) : ¬First p l := by
      rintro ⟨pos,hit,_⟩
      exact no_gap_one hp ((show l=1 by omega) ▸ hit)
    have empty : (Nat.primesLE X).filter (fun p => First p l)=∅ :=
      filter_eq_empty_iff.mpr fun p hp => no p (Nat.mem_primesLE.mp hp).2
    simp [fraction,empty]

theorem survival_step (pit : DegreeOnePrimeIdealTheorem) (n : ℕ) :
    survival (n+1)+firstDensity (n+1)=survival n := by
  apply tendsto_nhds_unique ((survival_limit pit (n+1)).add (first_limit_all pit (n+1)))
  apply (survival_limit pit n).congr
  intro X
  have eq : (fun p => if NoShort p n then (1:ℝ) else 0) =
      (fun p => if NoShort p (n+1) then (1:ℝ) else 0)+(fun p => if First p (n+1) then 1 else 0) := by
    funext p
    have a : NoShort p (n+1) ↔ NoShort p n ∧ ¬HasGap p (n+1) := by
      constructor
      · exact fun h => ⟨fun k hk le => h k hk (by omega),h _ (by omega) le_rfl⟩
      · rintro ⟨h,h'⟩ k hk le
        rcases Nat.lt_or_ge k (n+1) with lt|ge
        · exact h k hk (by omega)
        · exact (le.antisymm ge) ▸ h'
    have c : First p (n+1) ↔ NoShort p n ∧ HasGap p (n+1) := by
      constructor
      · exact fun ⟨_,hit,h⟩ => ⟨fun k hk le => h k hk (by omega),hit⟩
      · exact fun ⟨h,hit⟩ => ⟨by omega,hit,fun k hk lt => h k hk (by omega)⟩
    by_cases old : NoShort p n <;> by_cases hit : HasGap p (n+1) <;> simp [a,c,old,hit]
  simpa only [map_add,ordinary_eq,Pi.add_apply] using congrArg (ordinary X) eq

theorem survival_tail (pit : DegreeOnePrimeIdealTheorem) (K : ℕ) :
    survival K≤(1/2:ℝ)^(family 3 K).card := by
  classical
  let s := family 3 K
  have up := le_of_tendsto_of_tendsto' (survival_limit pit K) (law_of_pit pit s (fun u => u=∅)) (by
    intro X
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Nat.cast_le.mpr
    apply card_le_card
    intro p hp
    simp only [mem_filter] at hp ⊢
    refine ⟨hp.1,?_⟩
    unfold GapSieve.hits
    rw [filter_eq_empty_iff]
    exact fun i hi => hp.2 i.val i.prop.pos (family_mem.mp hi).2.1)
  have good (i) (hi : i∈s) := (family_mem.mp hi)
  have dec := decreasing_upper s (fun i hi => ⟨(good i hi).2.2,(good i hi).1⟩) (fun u => u=∅)
    (fun _ _ h eq => subset_empty.mp (eq ▸ h))
  have ef : @Finset.filter _ (fun u : Finset Nat.Primes => u=∅) (fun _ => Classical.propDecidable _) s.powerset={∅} := by ext u; by_cases h : u=∅ <;> simp [h]
  apply (up.trans dec).trans_eq
  simp [fairShare,ef,one_div]
  rfl

private theorem family_mono {m n : ℕ} (h : m≤n) : family 3 m⊆family 3 n := by
  intro i hi
  obtain ⟨lo,ub,hb⟩ := family_mem.mp hi
  exact family_mem.mpr ⟨lo,ub.trans h,hb⟩

theorem eligible_count_grows : Tendsto (fun K => (family 3 K).card) atTop atTop := by
  have many (n : ℕ) : ∃ K : ℕ, n≤(family 3 K).card := by
    induction n with
    | zero => exact ⟨0,Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨K,hK⟩ := ih
      obtain ⟨p,lo,hp,mod⟩ := Nat.forall_exists_prime_gt_and_modEq (max 3 K)
        (q:=7) (a:=3) (by decide) (by decide)
      let i : Nat.Primes := ⟨p,hp⟩
      have old : i∉family 3 K := fun h => (family_mem.mp h).2.1.not_gt ((le_max_right ..).trans_lt lo)
      have mem : i∈family 3 p := family_mem.mpr ⟨(le_max_left ..).trans_lt lo,le_rfl,Or.inl mod⟩
      have bound := card_le_card (insert_subset mem (family_mono ((le_max_right ..).trans lo.le)))
      rw [card_insert_of_notMem old] at bound
      exact ⟨p,(Nat.succ_le_succ hK).trans bound⟩
  apply tendsto_atTop.2
  intro n
  obtain ⟨K,h⟩ := many n
  filter_upwards [eventually_ge_atTop K] with j hj
  exact h.trans (card_le_card (family_mono hj))

theorem survival_zero (pit : DegreeOnePrimeIdealTheorem) : Tendsto survival atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).comp eligible_count_grows)
    (fun n => (survival_pos n).le) (survival_tail pit)

theorem atom_sum (pit : DegreeOnePrimeIdealTheorem) : HasSum firstDensity 1 := by
  have nonneg (k : ℕ) : 0≤firstDensity k := by
    unfold firstDensity
    split_ifs
    · exact uniform_nonneg fun _ => by split_ifs <;> norm_num
    · exact le_rfl
  rw [hasSum_iff_tendsto_nat_of_nonneg nonneg]
  have base : survival 0=1 := by
    have he : short 0=∅ := by decide
    unfold survival
    rw [he]
    unfold density
    simp only [zeroCounts,IsEmpty.forall_iff,if_true,uniform_one]
  have sum (n : ℕ) : (∑ i∈range (n+1), firstDensity i)=1-survival n := by
    induction n with
    | zero => simp [firstDensity,base]
    | succ n ih =>
      rw [sum_range_succ,ih]
      linarith [survival_step pit n]
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  simpa only [sum,sub_zero] using (tendsto_const_nhds (x:=(1:ℝ))).sub (survival_zero pit)

#print axioms first_limit_all
#print axioms survival_step
#print axioms survival_tail
#print axioms eligible_count_grows
#print axioms survival_zero
#print axioms atom_sum
end
end Erdos478.FirstCollision
