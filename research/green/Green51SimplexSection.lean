import Green51Hadamard

/-! # Coordinate functionals at the binary simplex bound -/

open Finset Green51Hadamard
open scoped Classical
namespace Green51SimplexSection
local notation "F" => ZMod 2
variable {U : Type*} [AddCommGroup U] [Module F U] [Fintype U]

/-- At the punctured binary simplex bound, every nonzero linear functional
occurs exactly once among the coordinates. -/
theorem simplex_columns {n : ℕ} (col : Fin n → Module.Dual F U)
    (large : n+1 ≤ Fintype.card U)
    (distance : ∀ x:U, x≠0 → n+1 ≤ 2*(univ.filter (fun i => col i x≠0)).card) :
    Fintype.card U=n+1 ∧ ∀ f : Module.Dual F U,
      (univ.filter (fun i => col i=f)).card = if f=0 then 0 else 1 := by
  classical
  let I (x:U) : ℤ := ∑ i, sign (col i x)
  have atZero : I 0 = n := by simp [I,sign]
  have neg (x:U) (hx:x≠0) : I x ≤ -1 := by
    have term (i:Fin n) : sign (col i x)=1-(if col i x≠0 then (2:ℤ) else 0) := by
      by_cases z:col i x=0 <;> simp [sign,z]
    have w : I x = (n:ℤ)-2*(univ.filter (fun i => col i x≠0)).card := by
      simp_rw [I,term]; simp [sum_sub_distrib,sum_ite,mul_comm]
    rw [w]
    have h : (n:ℤ)+1 ≤ 2*((univ.filter (fun i => col i x≠0)).card:ℤ) := by
      exact_mod_cast distance x hx
    omega
  have nonneg : 0 ≤ ∑ x:U,I x := by
    dsimp only [I]
    rw [sum_comm]
    apply sum_nonneg
    intro i _
    rw [character_sum]
    split <;> positivity
  let R := (univ:Finset U).erase 0
  have rest := sum_erase_add (f:=I) (univ:Finset U) (mem_univ (0:U))
  change (∑ x∈R,I x)+I 0 = _ at rest
  have rc : R.card+1=Fintype.card U := by
    simpa [R] using (card_erase_add_one (s:=univ) (mem_univ (0:U)))
  have total : (∑ x∈R,(-1-I x)) = -(R.card:ℤ) - ∑ x∈R,I x := by
    rw [sum_sub_distrib]; simp
  have terms (x:U) (hx:x∈R) : 0 ≤ -1-I x := by
    have := neg x (mem_erase.mp hx).1
    omega
  have lower := sum_nonneg terms
  have eq : ∑ x∈R,(-1-I x)=0 := by omega
  have equal (x:U) (hx:x≠0) : I x = -1 := by
    have h := (sum_eq_zero_iff_of_nonneg terms).mp eq x (mem_erase.mpr ⟨hx,mem_univ _⟩)
    omega
  have card : Fintype.card U=n+1 := by omega
  refine ⟨card,?_⟩
  intro f
  have flip (i : Fin n) : col i + f = 0 ↔ col i = f := by
    constructor
    · intro h
      apply add_right_cancel (b:=f)
      rw [h, ZModModule.add_self]
    · rintro h; rw [h, ZModModule.add_self]
  have transform : (∑ x:U,I x * sign (f x)) =
      (Fintype.card U:ℤ)*(univ.filter (fun i => col i=f)).card := by
    simp only [I,sum_mul,←sign_add,←LinearMap.add_apply]
    rw [sum_comm]
    simp_rw [character_sum,flip]
    simp [sum_ite,mul_comm]
  have eval (x:U) : I x * sign (f x) =
      (if x=0 then (n:ℤ)+1 else 0) - sign (f x) := by
    by_cases h:x=0
    · subst x;simp [atZero,sign]
    · simp [h,equal x h]
  simp_rw [eval] at transform
  rw [sum_sub_distrib,character_sum] at transform
  simp only [sum_ite_eq', mem_univ, if_true] at transform
  have cardPos : 0 < (Fintype.card U:ℤ) := by exact_mod_cast Fintype.card_pos
  by_cases h:f=0
  · rw [if_pos h]
    rw [if_pos h] at transform
    have hc : ((univ.filter (fun i => col i=f)).card:ℤ)=0 := by
      rw [card, Nat.cast_add, Nat.cast_one] at transform cardPos
      nlinarith
    exact_mod_cast hc
  · rw [if_neg h]
    rw [if_neg h, sub_zero] at transform
    have hc : ((univ.filter (fun i => col i=f)).card:ℤ)=1 := by
      rw [card, Nat.cast_add, Nat.cast_one] at transform cardPos
      nlinarith
    exact_mod_cast hc

end Green51SimplexSection
#print axioms Green51SimplexSection.simplex_columns
