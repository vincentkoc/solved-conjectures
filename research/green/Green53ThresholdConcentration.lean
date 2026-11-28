import Mathlib

/-! # Small-ball estimates for sums of independent signs -/

open Finset
open scoped Classical
namespace Green53Threshold
private theorem central_square (n : ℕ) : (n+1)*n.centralBinom^2 ≤ 16^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    have margin : (n+2)*(2*(2*n+1))^2 ≤ 16*(n+1)^3 := by nlinarith
    have calc' : (n+1)^2 * ((n+2)*(n+1).centralBinom^2) ≤ (n+1)^2 * (16^n*16) := by
      calc
        _ = (n+2)*(((n+1)*(n+1).centralBinom)^2) := by ring
        _ = ((n+2)*(2*(2*n+1))^2)*n.centralBinom^2 := by rw [h]; ring
        _ ≤ (16*(n+1)^3)*n.centralBinom^2 := Nat.mul_le_mul_right _ margin
        _ = ((n+1)^2*16)*((n+1)*n.centralBinom^2) := by ring
        _ ≤ ((n+1)^2*16)*(16^n) := Nat.mul_le_mul_left _ ih
        _ = _ := by ring
    rw [pow_succ]
    exact Nat.le_of_mul_le_mul_left calc' (by positivity)

/-- Subsets whose total weight lies in the specified half-open interval. -/
noncomputable def weightWindow {J : Type*} [Fintype J] (a : J → ℝ) (lo hi : ℝ) :=
  (univ : Finset (Finset J)).filter (fun s => lo ≤ ∑ j∈s,a j ∧ (∑ j∈s,a j)<hi)

/-- The Littlewood–Offord interval bound, by partition into Sperner antichains. -/
theorem window_count {J : Type*} [Fintype J] (a : J → ℝ) {δ : ℝ}
    (pos : 0 < δ) (le : ∀ i, δ ≤ a i) (lo : ℝ) (k : ℕ) :
    (weightWindow a lo (lo+k*δ)).card ≤ k*(Fintype.card J).choose (Fintype.card J/2) := by
  classical
  have one (v : ℝ) : (weightWindow a v (v+δ)).card ≤ (Fintype.card J).choose (Fintype.card J/2) := by
    apply IsAntichain.sperner
    intro s hs t ht ne sub
    have sh := (mem_filter.mp hs).2
    have th := (mem_filter.mp ht).2
    have exist : (t\s).Nonempty := sdiff_nonempty.mpr (fun h => ne (Subset.antisymm sub h))
    obtain ⟨j,hj⟩ := exist
    have dif : δ ≤ ∑ i∈t\s, a i := (le j).trans (single_le_sum (fun i _ => (le i).trans' pos.le) hj)
    have eq := sum_sdiff sub (f:=a)
    linarith [sh.1,th.2]
  induction k with
  | zero => simp [weightWindow]
  | succ k ih =>
    have inc : weightWindow a lo (lo+(k+1:ℕ)*δ) ⊆ weightWindow a lo (lo+k*δ) ∪ weightWindow a (lo+k*δ) (lo+k*δ+δ) := by
      intro s hs
      have h := (mem_filter.mp hs).2
      by_cases lt : (∑ i∈s,a i)<lo+k*δ
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h.1,lt⟩)
      · have upper : (∑ i∈s,a i)<lo+k*δ+δ := by
          push_cast at h; linarith [h.2]
        exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,not_lt.mp lt,upper⟩)
    calc
      _ ≤ _ := card_le_card inc
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := Nat.add_le_add ih (one _)
      _ = _ := by ring
def signBit (b : Bool) : ℝ := if b then 1 else -1

/-- The number of signings inside a closed interval of width 2kδ. -/
private theorem signed_window {J : Type*} [Fintype J] (a : J → ℝ) (δ b : ℝ) (k : ℕ)
    (pos : 0<δ) (size : ∀ j, δ≤|a j|) :
    (univ.filter (fun x : J → Bool => |b+∑ j, a j*signBit (x j)|≤k*δ)).card ≤
      (k+1)*(Fintype.card J).choose (Fintype.card J/2) := by
  classical
  let same (x : J → Bool) (j : J) : Prop := x j=decide (0≤a j)
  let up (x : J → Bool) := univ.filter (same x)
  have formula (x : J → Bool) :
      ∑ j, a j*signBit (x j) = 2*∑ j∈up x, |a j| - ∑ j, |a j| := by
    simp only [up,sum_filter,Finset.mul_sum,←sum_sub_distrib]
    refine sum_congr rfl (fun j hj => ?_)
    dsimp only [same]
    by_cases h : 0≤a j <;> cases x j <;>
      simp [signBit,h,abs_of_nonneg,abs_of_neg,lt_of_not_ge] <;> ring
  let lo := ((∑ j,|a j|)-b-k*δ)/2
  refine le_trans (card_le_card_of_injOn (t:=weightWindow (fun j => |a j|) lo (lo+(k+1:ℕ)*δ)) up ?_ ?_)
    (window_count _ pos size _ _)
  · intro x hx
    have h := abs_le.mp (mem_filter.mp hx).2
    rw [formula] at h
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    dsimp only [lo]; push_cast; constructor <;> linarith [h.1,h.2]
  · intro x _ y _ eq
    funext j
    have bi : x j=decide (0≤a j) ↔ y j=decide (0≤a j) := by
      change same x j ↔ same y j
      simpa only [up,mem_filter,mem_univ,true_and] using (Iff.of_eq (congrArg (fun s => j∈s) eq))
    by_cases h : 0≤a j <;> cases e : x j <;> cases f : y j <;> simp_all

/-- Multiplying the size of the central layer in dimension 2u² by u gives less than the whole cube. -/
theorem central_layer_bound (u : ℕ) :
    u*(u^2).centralBinom < 2^(2*u^2) := by
  have sq := central_square (u^2)
  have p := Nat.centralBinom_pos (u^2)
  have eq : (2^(2*u^2))^2=16^(u^2) := by
    calc
      _ = 2^((2*u^2)*2) := (pow_mul _ _ _).symm
      _ = 2^(4*u^2) := by congr 1; ring
      _ = (2^4)^(u^2) := pow_mul _ _ _
      _ = _ := rfl
  by_contra! bad
  have m := Nat.pow_le_pow_left bad 2
  rw [eq,mul_pow] at m
  nlinarith [sq,m,Nat.pow_pos p (n:=2)]

private theorem same_sum {J α : Type*} [AddCommMonoid α] (inst inst' : Fintype J) (f : J → α) :
    ∑ j∈@univ J inst,f j = ∑ j∈@univ J inst',f j := by rw [Subsingleton.elim inst inst']

set_option maxHeartbeats 800000 in
/-- Anti-concentration from a block of large coefficients, with arbitrary weights off the block. -/
theorem block_small_ball {J : Type*} [Fintype J] (s : Finset J) (a : J → ℝ)
    (δ b : ℝ) (k : ℕ) (pos : 0<δ) (large : ∀ j∈s,δ≤|a j|) :
    (univ.filter (fun x : J → Bool => |b+∑ j,a j*signBit (x j)|≤k*δ)).card ≤
      2^(Fintype.card J-s.card)*((k+1)*s.card.choose (s.card/2)) := by
  classical
  let E := (Equiv.piEquivPiSubtypeProd (fun j => j∈s) (fun _ => Bool)).trans (Equiv.prodComm _ _)
  let offset (y : {j // j∉s} → Bool) := b+∑ j, a j.val*signBit (y j)
  let mask (y : {j // j∉s} → Bool) (z : {j // j∈s} → Bool) : ℕ :=
    if |offset y+∑ j, a j.val*signBit (z j)| ≤ k*δ then 1 else 0
  have same (x : J → Bool) :
      (if |b+∑ j,a j*signBit (x j)|≤k*δ then 1 else 0) = mask (E x).1 (E x).2 := by
    have add := Fintype.sum_subtype_add_sum_subtype (fun j => j∈s) (fun j => a j*signBit (x j))
    have total : b+∑ j,a j*signBit (x j) =
        (b+∑ j : {j // j∉s},a j.val*signBit (x j.val)) + ∑ j : {j // j∈s},a j.val*signBit (x j.val) := by
      rw [←add,add_assoc]
      congr 1
      rw [add_comm]
      congr 1; apply same_sum
    unfold mask offset
    change _ = if |(b+∑ j : {j // j∉s}, a j.val*signBit (x j.val)) +
        ∑ j : {j // j∈s},a j.val*signBit (x j.val)|≤k*δ then 1 else 0
    rw [total]
  rw [card_filter]
  calc
    _ = ∑ pair : ({j // j∉s} → Bool) × ({j // j∈s} → Bool), mask pair.1 pair.2 := Fintype.sum_equiv E _ _ same
    _ = ∑ y, ∑ z, mask y z := Fintype.sum_prod_type _
    _ ≤ ∑ _y : {j // j∉s} → Bool, (k+1)*s.card.choose (s.card/2) := by
      refine sum_le_sum (fun y _ => ?_)
      have lim := signed_window (fun j : {j // j∈s} => a j.val) δ (offset y) k pos (fun j => large _ j.property)
      simp only [card_filter,Fintype.card_coe] at lim
      dsimp only [mask]
      convert lim using 1 <;> first | rfl | apply same_sum
    _ = _ := by simp [Fintype.card_subtype_compl]

end Green53Threshold

#print axioms Green53Threshold.window_count
#print axioms Green53Threshold.block_small_ball
#print axioms Green53Threshold.central_layer_bound
