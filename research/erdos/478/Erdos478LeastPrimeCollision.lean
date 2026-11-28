import Erdos478ShortCollisionAvoidance

/-! # The first positive distance between factorials with equal residues -/

namespace Erdos478.FirstCollision
open Polynomial Finset Filter Topology BinaryGap FrobeniusCounts GapSieve GapDensity SplittingDensity
open scoped Classical
noncomputable section

def earlier {s : Finset ℕ} (l : ℕ) (a : ↥(insert l s) → ℕ) (i : s) : ℕ :=
  a ⟨i.val,mem_insert_of_mem i.prop⟩

def withHit {s : Finset ℕ} (l : ℕ) (E : (s → ℕ) → Prop) (a : ↥(insert l s) → ℕ) :=
  E (earlier l a) ∧ 0<a ⟨l,mem_insert_self ..⟩

/-- An old count event may prescribe failures at composite as well as prime lengths. -/
theorem retain_density (pit : DegreeOnePrimeIdealTheorem) (s : Finset ℕ) {l : ℕ} (hl : l.Prime)
    (small : ∀ k∈s, 2≤k ∧ k<l) (E : (s → ℕ) → Prop) :
    density s E≤(if broad l ∧ 3<l then 2 else (l:ℝ))*density (insert l s) (withHit l E) := by
  let T := insert l s
  let K := FieldOf T
  let : Normal ℚ K := SplittingField.instNormal _
  have ht (k) (hk : k∈T) : 2≤k := (mem_insert.mp hk).elim (fun h => h ▸ hl.two_le) (fun h => (small k h).1)
  let W (a : T → ℕ) := E (earlier l a)
  let w (g : Aut K) : ℝ := if W (fun i => fixedGap K i.val g) then 1 else 0
  have eq := density_congr pit (fun k hk => (small k hk).1) ht E W (fun _ _ => Iff.rfl)
  rw [eq]
  have bound := weighted_hit K s hl (fun k hk => ⟨by have := (small k hk).1; omega,(small k hk).2⟩)
    (fun _ hk => gap_splits (fun k h => by have := ht k h; omega) hk) w
    (fun g => by dsimp [w]; split_ifs <;> norm_num) (by
      intro n g
      have he : earlier l (s:=s) (fun i => fixedGap K i.val (n.val*g))=
          earlier l (fun i => fixedGap K i.val g) := funext fun i => stable_count K n g i.prop
      exact congrArg (fun a : s → ℕ => if E a then (1:ℝ) else 0) he)
  apply bound.trans_eq
  congr 1
  apply congrArg (uniform (Aut K))
  funext g
  let a (i : T) := fixedGap K i.val g
  change (if 0<fixedGap K l g then (if E (earlier l a) then (1:ℝ) else 0) else 0)=
    (@ite ℝ (E (earlier l a) ∧ 0<fixedGap K l g) (Classical.propDecidable _) 1 0)
  by_cases hit : 0<fixedGap K l g <;> simp [hit]

def firstDensity (l : ℕ) := if 2≤l then density (insert l (short (l-1))) (withHit l zeroCounts) else 0

theorem first_limit (pit : DegreeOnePrimeIdealTheorem) {l : ℕ} (hl : 2≤l) :
    Tendsto (fun X => fraction X (fun p => First p l)) atTop (𝓝 (firstDensity l)) := by
  let s := short (l-1)
  have hs (k) (hk : k∈insert l s) : 2≤k := (mem_insert.mp hk).elim (fun h => h ▸ hl) (fun h => (mem_Icc.mp h).1)
  rw [firstDensity,if_pos hl]
  apply density_limit pit _ hs _ _ 0
  intro p _ hp
  have eq : First p l ↔ NoShort p (l-1) ∧ HasGap p l := by
    constructor
    · exact fun ⟨_,hit,no⟩ => ⟨fun k hk hs => no k hk (by omega),hit⟩
    · exact fun ⟨no,hit⟩ => ⟨by omega,hit,fun k hk hs => no k hk (by omega)⟩
  rw [eq,noShort_iff hp,ConditionalGaps.hasGap_iff]
  rfl

theorem first_density_bound (pit : DegreeOnePrimeIdealTheorem) {l : ℕ} (hl : l.Prime) :
    survival (l-1) ≤ (if broad l ∧ 3<l then 2 else (l:ℝ))*firstDensity l := by
  rw [firstDensity,if_pos hl.two_le]
  exact retain_density pit _ hl (fun k hk => ⟨(mem_Icc.mp hk).1,by have := (mem_Icc.mp hk).2; have := hl.two_le; omega⟩) _

/-- Every prime length occurs as the exact shortest collision on a prime set
of positive ordinary density. This lower bound uses all smaller integer lengths. -/
theorem prime_atom_lower (pit : DegreeOnePrimeIdealTheorem) {l : ℕ} (hl : l.Prime) :
    ((∏ k∈Icc 2 (l-1), k.factorial : ℕ) : ℝ)⁻¹ /
      (if broad l ∧ 3<l then 2 else (l:ℝ)) ≤ firstDensity l := by
  have lp : (0:ℝ)<l := Nat.cast_pos.mpr hl.pos
  have pos : (0:ℝ)<(if broad l ∧ 3<l then 2 else (l:ℝ)) := by split_ifs <;> positivity
  exact (div_le_iff₀ pos).mpr ((survival_lower _).trans ((first_density_bound pit hl).trans_eq (mul_comm ..)))

theorem prime_atom_pos (pit : DegreeOnePrimeIdealTheorem) {l : ℕ} (hl : l.Prime) : 0<firstDensity l := by
  have lp : (0:ℝ)<l := Nat.cast_pos.mpr hl.pos
  apply lt_of_lt_of_le _ (prime_atom_lower pit hl)
  apply div_pos (inv_pos.mpr (Nat.cast_pos.mpr (prod_pos fun k _ => Nat.factorial_pos k)))
  split_ifs <;> positivity

#print axioms earlier
#print axioms withHit
#print axioms retain_density
#print axioms firstDensity
#print axioms first_limit
#print axioms first_density_bound
#print axioms prime_atom_lower
#print axioms prime_atom_pos
end
end Erdos478.FirstCollision
