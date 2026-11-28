import Green33SubpowerBudgets
import Green33QuasiSidon

/-! The all-interval quasi-Sidon transfer with a subpower bound on ordered sum counts. -/

open Finset Filter Asymptotics Green33StrictReduction Green33Multiplicity
open Green33MaximalOrders Green33QuasiSidon Green33SubpowerBudgets
open scoped Pointwise Topology

namespace Green33SubpowerIntervals

/-- Number of ordered integer representations, including equal summands. -/
def orderedCount (B : Finset ℕ) (t : ℕ) : ℕ :=
  ((B ×ˢ B).filter (fun p => p.1+p.2=t)).card

/-- Reduction of positive representatives injects an integer sum fiber into
the corresponding cyclic fiber, with the two unit translations removed. -/
theorem interval_count_le {M : ℕ+} (A : Finset (ZMod M)) (t : ℕ) :
    orderedCount (intervalCopy A) t ≤ reps A ((t : ZMod M)-2) := by
  let f (x : ZMod M) := x.val+1
  let g (n : ℕ) : ZMod M := (n:ZMod M)-1
  have left (a : ZMod M) : g (f a)=a := by simp [g,f]
  have inv {x} (hx : x ∈ intervalCopy A) : g x ∈ A ∧ f (g x)=x := by
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    exact ⟨(left a).symm ▸ ha,congrArg f (left a)⟩
  apply card_le_card_of_injOn (fun r : ℕ × ℕ => (g r.1,g r.2))
  · intro r hr
    obtain ⟨mem,sum⟩ := mem_filter.mp hr
    obtain ⟨a,b⟩ := mem_product.mp mem
    refine mem_filter.mpr ⟨mem_product.mpr ⟨(inv a).1,(inv b).1⟩,?_⟩
    change g r.1+g r.2=(t:ZMod M)-2
    rw [←sum]
    simp only [g,Nat.cast_add]
    ring
  · intro x hx y hy eq
    have mx := mem_product.mp (mem_filter.mp hx).1
    have my := mem_product.mp (mem_filter.mp hy).1
    exact Prod.ext (((inv mx.1).2.symm.trans (congrArg (fun r : ZMod M × ZMod M => f r.1) eq)).trans (inv my.1).2)
      (((inv mx.2).2.symm.trans (congrArg (fun r : ZMod M × ZMod M => f r.2) eq)).trans (inv my.2).2)

/-- Under Green 33 the witnesses of the pinned Erdős 840 predicate at √2
can be chosen with a subpower peak across every sufficiently large interval. -/
theorem green_erdos840_subpower (green : OrdinaryLimit) :
    ∃ S : ℕ → Finset ℕ, (∀ n, S n ⊆ Icc 1 n) ∧
      ((fun n => ((S n).card:ℝ)) ~[atTop] (fun n : ℕ => Real.sqrt 2*Real.sqrt n)) ∧
      ((fun n => ((S n+S n).card:ℝ)) ~[atTop] (fun n => ((S n).card.choose 2:ℝ))) ∧
      ∀ h : ℕ, ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, (orderedCount (S n) t)^h ≤ n := by
  classical
  obtain ⟨N,B,valid,lim,caps⟩ := all_budget_family
  let M (n : ℕ) := N (budget n)
  let A (n : ℕ) := B (budget n)
  let ok (n : ℕ) : Prop := StrictCover (A n) ∧ (A n).card ≤ budget n
  let S (n : ℕ) : Finset ℕ := if ok n then intervalCopy (A n) else ∅
  have good : ∀ᶠ n in atTop, ok n := budget_scale.1.eventually valid
  have fits {n} (hn : ok n) : (M n).val ≤ n :=
    (order_le_choose hn.1).trans ((Nat.choose_le_choose 2 hn.2).trans (budget_fits n).2)
  have ord : Tendsto (fun n => (M n:ℝ)/(n:ℝ)) atTop (𝓝 1) := by
    rw [green_iff_orderConstant.mp green] at lim
    have ht := (lim.comp budget_scale.1).mul (budget_scale.2.pow 2)
    norm_num [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at ht
    apply ht.congr'
    filter_upwards [budget_scale.1.eventually_gt_atTop 0] with n hn
    have hk : (budget n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    change (M n:ℝ)/(budget n:ℝ)^2*((budget n:ℝ)/Real.sqrt n)^2 = _
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp
  have size : Tendsto (fun n => ((S n).card:ℝ)/Real.sqrt n) atTop (𝓝 (Real.sqrt 2)) := by
    have lower : Tendsto (fun n => Real.sqrt 2*Real.sqrt ((M n:ℝ)/(n:ℝ))) atTop (𝓝 (Real.sqrt 2)) := by
      simpa using ord.sqrt.const_mul (Real.sqrt 2)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower budget_scale.2
    · filter_upwards [good] with n hn
      rw [show S n=intervalCopy (A n) from if_pos hn,(intervalCopy_spec _ hn.1).2.1,
        Real.sqrt_div (by positivity),← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith only [strict_size_gap hn.1]) (Real.sqrt_nonneg _)
    · filter_upwards [good] with n hn
      rw [show S n=intervalCopy (A n) from if_pos hn,(intervalCopy_spec _ hn.1).2.1]
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hn.2) (Real.sqrt_nonneg _)
  have pairs := pair_scales_of_size size
  have density : Tendsto (fun n => ((S n+S n).card:ℝ)/(n:ℝ)) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ord pairs.2
    · filter_upwards [good] with n hn
      rw [show S n=intervalCopy (A n) from if_pos hn]
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (intervalCopy_spec _ hn.1).2.2) (Nat.cast_nonneg _)
    · exact Eventually.of_forall (fun n => div_le_div_of_nonneg_right
        (Nat.cast_le.mpr (sumset_upper (S n))) (Nat.cast_nonneg _))
  refine ⟨S,?_,?_,?_,?_⟩
  · intro n
    by_cases hn : ok n
    · rw [show S n=intervalCopy (A n) from if_pos hn]
      exact (intervalCopy_spec _ hn.1).1.trans (Icc_subset_Icc le_rfl (fits hn))
    · simpa only [S,if_neg hn] using (empty_subset (Icc 1 n))
  · apply isEquivalent_of_tendsto_one
    have eq := size.div_const (Real.sqrt 2)
    rw [div_self (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ)<2)).ne'] at eq
    exact eq.congr (fun n => by simp [Pi.div_apply,div_div,mul_comm])
  · have sums : (fun n => ((S n+S n).card:ℝ)) ~[atTop] (fun n : ℕ => (n:ℝ)) :=
      isEquivalent_of_tendsto_one density
    have choose : (fun n => ((S n).card.choose 2:ℝ)) ~[atTop] (fun n : ℕ => (n:ℝ)) :=
      isEquivalent_of_tendsto_one pairs.1
    exact sums.trans choose.symm
  · intro h
    filter_upwards [good,budget_scale.1.eventually (caps h)] with n hn cap t
    rw [show S n=intervalCopy (A n) from if_pos hn]
    have bound := (interval_count_le (A n) t).trans (Finset.le_sup (f := reps (A n)) (mem_univ _))
    exact (Nat.pow_le_pow_left bound h).trans (cap.trans (fits hn))

/-- The first three clauses are exactly the formal-conjectures predicate. -/
example (green : OrdinaryLimit) : Erdos840.IsQuasiSidonConstant (Real.sqrt 2) := by
  obtain ⟨S,sub,size,sums,_⟩ := green_erdos840_subpower green
  exact ⟨S,sub,size,sums⟩

#print axioms interval_count_le
#print axioms green_erdos840_subpower

end Green33SubpowerIntervals
