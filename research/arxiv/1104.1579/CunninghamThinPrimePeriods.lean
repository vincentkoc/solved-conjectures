import CunninghamPrimePeriodSupply

/-! Disjoint sets of prime periods with a prescribed total reciprocal mass. -/

namespace CunninghamChain.PrimePeriodSupply
open Finset Filter Topology

private lemma choose_mass (S : Finset ℕ) (f : ℕ → ℝ) {T : ℝ} (ht : 0<T)
    (unit : ∀ p∈S, f p≤1) (low : T≤∑ p∈S, f p) :
    ∃ R⊆S, T≤∑ p∈R, f p ∧ ∑ p∈R, f p ≤ T+1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at low; linarith
  | @insert p S np ih =>
    by_cases enough : T≤∑ q∈S, f q
    · obtain ⟨R,sub,h⟩ := ih (fun q hq => unit q (mem_insert_of_mem hq)) enough
      exact ⟨R,sub.trans (subset_insert ..),h⟩
    · refine ⟨insert p S,Subset.rfl,low,?_⟩
      rw [sum_insert np]
      linarith [unit p (mem_insert_self ..)]

theorem prime_period_set (B : ℕ) (avoid : Finset ℕ) {T : ℝ} (ht : 0<T) :
    ∃ S : Finset ℕ, (∀ p∈S, p.Prime ∧ p ≡ 1 [MOD (B+1).factorial] ∧ p∉avoid) ∧
      T≤∑ p∈S, (p:ℝ)⁻¹ ∧ ∑ p∈S, (p:ℝ)⁻¹ ≤ T+1 := by
  classical
  let M := (B+1).factorial
  let : NeZero M := ⟨Nat.factorial_ne_zero _⟩
  let ok (p : ℕ) := p.Prime ∧ (p:ZMod M)=1 ∧ p∉avoid
  let f (p : ℕ) := if ok p then (p:ℝ)⁻¹ else 0
  have div : ¬Summable f := by
    intro h
    apply progression_reciprocals (1:ZMod M) isUnit_one
    apply (summable_congr_cofinite _).mp h
    filter_upwards [avoid.finite_toSet.compl_mem_cofinite] with p hp
    have np : p∉avoid := hp
    simp [f,ok,np]
  obtain ⟨S,hS⟩ : ∃ S : Finset ℕ, T<∑ p∈S, f p := by
    by_contra! bounded
    exact div (summable_of_sum_le (fun p => by dsimp [f]; split <;> positivity) bounded)
  let V := S.filter ok
  have high : T≤∑ p∈V, (p:ℝ)⁻¹ := by
    simpa only [V,sum_filter,f] using hS.le
  obtain ⟨R,sub,lo,hi⟩ := choose_mass V (fun p => (p:ℝ)⁻¹) ht
    (fun p hp => inv_le_one_of_one_le₀ (by exact_mod_cast (mem_filter.mp hp).2.1.one_le)) high
  refine ⟨R,?_,lo,hi⟩
  intro p hp
  obtain ⟨pr,eq,out⟩ := (mem_filter.mp (sub hp)).2
  exact ⟨pr,(ZMod.natCast_eq_natCast_iff p 1 M).mp (by simpa only [Nat.cast_one] using eq),out⟩

/-- The two period sets will be assigned to the two signs. Their prime
divisors have uniformly bounded total reciprocal cost. -/
structure PeriodSupply (T : ℝ) where
  plus : Finset ℕ
  minus : Finset ℕ
  disjoint : Disjoint plus minus
  q : ℕ → ℕ
  spec : ∀ l∈plus∪minus, l.Prime ∧ (q l).Prime ∧ 2<q l ∧ orderOf (2:ZMod (q l))=l
  cost : ∑ l∈plus∪minus, (q l:ℝ)⁻¹ ≤ 1
  plus_mass : T≤∑ l∈plus, (l:ℝ)⁻¹
  minus_mass : T≤∑ l∈minus, (l:ℝ)⁻¹

theorem period_supply_exists {T : ℝ} (ht : 0<T) : Nonempty (PeriodSupply T) := by
  classical
  obtain ⟨B,hB⟩ := exists_nat_gt (2*(T+1))
  have bp : 0<(B:ℝ) := by linarith
  obtain ⟨P,p_spec,p_lo,p_hi⟩ := prime_period_set B ∅ ht
  obtain ⟨R,r_spec,r_lo,r_hi⟩ := prime_period_set B P ht
  have dis : Disjoint P R := disjoint_left.mpr fun l hp hr => (r_spec l hr).2.2 hp
  have pr {l : ℕ} (hl : l∈P∪R) : l.Prime ∧ l ≡ 1 [MOD (B+1).factorial] := by
    rcases mem_union.mp hl with hp|hr
    · exact ⟨(p_spec _ hp).1,(p_spec _ hp).2.1⟩
    · exact ⟨(r_spec _ hr).1,(r_spec _ hr).2.1⟩
  let q (l : ℕ) := if hl : l∈P∪R then (large_prime_of_order (pr hl).1 (pr hl).2).choose else 0
  have data (l : ℕ) (hl : l∈P∪R) :
      (q l).Prime ∧ 2<q l ∧ B*l<q l ∧ orderOf (2:ZMod (q l))=l := by
    have eq : q l=(large_prime_of_order (pr hl).1 (pr hl).2).choose := dif_pos hl
    exact (congrArg (fun v : ℕ => v.Prime ∧ 2<v ∧ B*l<v ∧ orderOf (2:ZMod v)=l) eq).mpr
      (large_prime_of_order (pr hl).1 (pr hl).2).choose_spec
  refine ⟨⟨P,R,dis,q,fun l hl => ⟨(pr hl).1,(data l hl).1,(data l hl).2.1,(data l hl).2.2.2⟩,
    ?_,p_lo,r_lo⟩⟩
  calc ∑ l∈P∪R, (q l:ℝ)⁻¹ ≤ ∑ l∈P∪R, (l:ℝ)⁻¹/(B:ℝ) := by
         apply sum_le_sum
         intro l hl
         have lp : 0<(l:ℝ) := by exact_mod_cast (pr hl).1.pos
         have big : (B:ℝ)*l≤q l := by exact_mod_cast (data l hl).2.2.1.le
         simpa only [mul_inv_rev,div_eq_mul_inv] using inv_anti₀ (mul_pos bp lp) big
       _ = ((∑ l∈P, (l:ℝ)⁻¹)+(∑ l∈R,(l:ℝ)⁻¹))/B := by rw [←sum_div,sum_union dis]
       _ ≤ 1 := (div_le_one bp).mpr (by linarith)

#print axioms prime_period_set
#print axioms period_supply_exists

end CunninghamChain.PrimePeriodSupply
