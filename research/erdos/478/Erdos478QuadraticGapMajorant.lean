import Erdos478JointGapMoments

/-! # A quadratic majorant for the lower tail of the factorial gap count -/

namespace Erdos478.GapTail
open Finset Filter Topology GapPatterns GapVariance RootMoments BinaryGap
open scoped Classical
noncomputable section

private def linear (z : ℝ) := -(1-z)-(1-z)^2/2
private def quadratic (z : ℝ) := (1-z)^2/2
def major (z x : ℝ) := 1+linear z*x+quadratic z*x^2
def base (z : ℝ) := (1+z^2)/2

/-- Second-order Bonferroni majorant of the discrete exponential. -/
theorem major_lower {z : ℝ} (hz : 0≤z) (hz' : z≤1) (n : ℕ) : z^n≤major z n := by
  induction n with
  | zero => simp [major]
  | succ n ih =>
    rw [pow_succ]
    apply (mul_le_mul_of_nonneg_right ih hz).trans
    have h : 0≤(n:ℝ)*((n:ℝ)-1) := by
      cases n with
      | zero => norm_num
      | succ n => push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) n,sq_nonneg (n:ℝ)]
    have id : major z (n+1)-major z n*z=(1-z)^3*((n:ℝ)*((n:ℝ)-1))/2 := by
      simp only [major,linear,quadratic]
      ring
    rw [Nat.cast_succ,← sub_nonneg,id]
    exact div_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.mpr hz') _) h) (by norm_num)

def tilt (z : ℝ) (i : Nat.Primes) (p : ℕ) := major z (observation i p)
def count (i : Nat.Primes) (p : ℕ) := Nat.card (RootPairs.solutions (gap i.val) (ZMod p))

def word (z : ℝ) (P S T : Finset Nat.Primes) : ℕ → ℝ :=
  (∏ i∈P, tilt z i)*(∏ i∈S, observation i)*(∏ i∈T, observation i)

private theorem recursion (z : ℝ) {i : Nat.Primes} {P S T : Finset Nat.Primes} (hp : i∉P) (hs : i∉S) (ht : i∉T) :
    word z (insert i P) S T = word z P S T + (linear z) • word z P (insert i S) T +
      (quadratic z) • word z P (insert i S) (insert i T) := by
  funext p
  simp only [word,prod_insert hp,prod_insert hs,prod_insert ht,Pi.add_apply,Pi.smul_apply,
    Pi.mul_apply,smul_eq_mul,tilt,major]
  ring

private theorem word_mean (z : ℝ) (A : PrimeAverage) (P S T : Finset Nat.Primes)
    (gp : ∀ i∈P, broad i.val ∧ 3 < i.val) (gs : ∀ i∈S, broad i.val ∧ 3 < i.val)
    (dis : Disjoint P S) (sub : T⊆S) :
    Tendsto (fun X => A.avg X (word z P S T)) atTop (𝓝 ((base z)^P.card*2^T.card)) := by
  induction P using Finset.induction_on generalizing S T with
  | empty =>
    have eq : word z ∅ S T=fun p => (∏ i∈S, observation i p)*(∏ i∈T, observation i p) := by
      funext p
      simp [word,prod_apply]
    simpa only [eq,card_empty,pow_zero,one_mul] using mixed_pair_mean A sub gs
  | @insert i P hi ih =>
    have hps := (disjoint_insert_left.mp dis)
    have ht : i∉T := fun h => hps.1 (sub h)
    have gp' (j) (hj : j∈P) := gp j (mem_insert_of_mem hj)
    have gs' : ∀ j∈insert i S, broad j.val ∧ 3 < j.val := by
      intro j hj
      rcases mem_insert.mp hj with rfl|hj
      · exact gp _ (mem_insert_self ..)
      · exact gs _ hj
    have dp : Disjoint P (insert i S) := disjoint_insert_right.mpr ⟨hi,hps.2⟩
    have h₀ := ih S T gp' gs hps.2 sub
    have h₁ := ih (insert i S) T gp' gs' dp (sub.trans (subset_insert _ _))
    have h₂ := ih (insert i S) (insert i T) gp' gs' dp (insert_subset_insert _ sub)
    have lim := (h₀.add (h₁.const_mul (linear z))).add (h₂.const_mul (quadratic z))
    rw [card_insert_of_notMem ht] at lim
    rw [card_insert_of_notMem hi]
    convert lim using 1
    · funext X
      rw [recursion z hi hps.1 ht,map_add,map_add,map_smul,map_smul]
      rfl
    · congr 1
      simp only [pow_succ,base,linear,quadratic]
      ring

/-- The mean of the product of the majorants factors exactly. -/
theorem major_product_mean (z : ℝ) (A : PrimeAverage) (s : Finset Nat.Primes)
    (good : ∀ i∈s, broad i.val ∧ 3 < i.val) :
    Tendsto (fun X => A.avg X (fun p => ∏ i∈s, major z (observation i p))) atTop (𝓝 ((base z)^s.card)) := by
  have eq : word z s ∅ ∅=fun p => ∏ i∈s, major z (observation i p) := by
    funext p
    simp [word,prod_apply,tilt]
  simpa only [eq,card_empty,pow_zero,mul_one] using word_mean z A s ∅ ∅ good (by simp) (by simp) (by simp)

theorem pow_sum_le_product {z : ℝ} (hz : 0≤z) (hz' : z≤1) (s : Finset Nat.Primes) (p : ℕ) :
    z^(∑ i∈s, count i p) ≤ ∏ i∈s, major z (observation i p) := by
  rw [← prod_pow_eq_pow_sum]
  exact prod_le_prod (fun _ _ => by positivity) (fun i _ => major_lower hz hz' (count i p))

#print axioms count
#print axioms major
#print axioms base
#print axioms tilt
#print axioms word
#print axioms major_lower
#print axioms major_product_mean
#print axioms pow_sum_le_product
end
end Erdos478.GapTail
