import Erdos722RepunitProducts

/-! # Separating the 42-point seed from the full inflation and product closure -/

namespace Erdos722.SmallOrders
open PointedProduct

/-- Punctured orders obtained from zero by any finite sequence of Hanani
inflations and Wilson products. The generated orders include 1, 5 and 21. -/
inductive Generated : ℕ → Prop
  | zero : Generated 0
  | inflate {a : ℕ} : Generated a → Generated (4*a+1)
  | product {a b : ℕ} : Generated a → Generated b → Generated (a*b)

theorem generated_repunit_products (s : Finset ℕ) (e : ℕ → ℕ) :
    Generated (∏ d ∈ s, repunit d ^ e d) := by
  classical
  have one : Generated 1 := Generated.inflate Generated.zero
  have rep (d : ℕ) : Generated (repunit d) := by
    induction d with
    | zero => exact Generated.zero
    | succ d ih => exact Generated.inflate ih
  have power {a : ℕ} (h : Generated a) (n : ℕ) : Generated (a^n) := by
    induction n with
    | zero => simpa using one
    | succ n ih => rw [pow_succ]; exact Generated.product ih h
  induction s using Finset.induction_on with
  | empty => simpa using one
  | @insert d s hd ih => rw [Finset.prod_insert hd]; exact Generated.product (power (rep d) _) ih

theorem design_of_generated (witt : ExistsDesign 5 22) {a : ℕ} (h : Generated a) :
    ExistsDesign 5 (a+1) := by
  induction h with
  | zero =>
    refine ⟨∅,fun _ he => (Finset.notMem_empty _ he).elim,?_⟩
    intro T hT
    have h := T.card_le_univ
    simp [hT] at h
  | inflate _ ih => exact TwoStem.hanani_of_seed witt ih
  | product _ _ ih jh => exact PrimePower.product (by decide : Nat.Prime 5).isPrimePow ih jh

private theorem zero_or_odd {a : ℕ} (ha : Generated a) : a=0 ∨ a%2=1 := by
  induction ha with
  | zero => exact Or.inl rfl
  | inflate => right; omega
  | product _ _ ih jh =>
    rcases ih with h|h <;> rcases jh with j|j
    all_goals simp [h,j,Nat.mul_mod]

/-- No positive power of a prime congruent to one modulo eight is in the
closure. Every nontrivial inflation is five modulo eight. For a product
equal to a prime power, the same prime-power constraint holds for both inputs. -/
theorem prime_power_escape {p : ℕ} (hp : p.Prime) (h₈ : p%8=1) {d : ℕ} (hd : 0<d) :
    ¬Generated (p^d) := by
  have unit (n : ℕ) (h : 1=p^n) : n=0 := by
    apply Nat.pow_right_injective hp.two_le
    simpa only [pow_zero] using h.symm
  have powmod (n : ℕ) : p^n%8=1 := by rw [Nat.pow_mod,h₈,one_pow]; decide
  have only_unit {a : ℕ} (ha : Generated a) : ∀ n, a=p^n → n=0 := by
    induction ha with
    | zero =>
      intro n he
      have := pow_pos hp.pos n
      omega
    | @inflate a ha ih =>
      intro n he
      rcases zero_or_odd ha with rfl|odd
      · exact unit n (by simpa using he)
      · have h := powmod n
        rw [← he] at h
        omega
    | @product a b ha hb ih jh =>
      intro n he
      obtain ⟨i,_,hi⟩ := (Nat.dvd_prime_pow hp).mp (he ▸ Nat.dvd_mul_right a b)
      obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow hp).mp (he ▸ Nat.dvd_mul_left b a)
      have ai := ih i hi
      have bj := jh j hj
      exact unit n (by simpa [hi,hj,ai,bj] using he)
  exact fun h => hd.ne' (only_unit h _ rfl)

/-- Unconditionally, infinitely many nontrivial ordinary six-point-block
designs have punctured order outside the entire two-rule closure. -/
theorem infinite_outside_closure :
    Set.Infinite {n | 6<n ∧ (∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 6) ∧
      ¬Generated (n-1)} := by
  let f (d : ℕ) := 41^(d+1)+1
  have hf : Function.Injective f := fun _ _ h =>
    Nat.succ_inj.mp (Nat.pow_right_injective (by decide : 2≤41) (Nat.succ_inj.mp h))
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨d,rfl⟩
  have lo : 41^1 ≤ 41^(d+1) := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨by dsimp [f]; omega,
    PrimePower.power_order (by decide : Nat.Prime 5).isPrimePow Witness42.order_forty_two (d+1),?_⟩
  exact prime_power_escape (by decide : Nat.Prime 41) (by decide) (Nat.succ_pos d)

#print axioms Generated
#print axioms generated_repunit_products
#print axioms design_of_generated
#print axioms prime_power_escape
#print axioms infinite_outside_closure
end Erdos722.SmallOrders
