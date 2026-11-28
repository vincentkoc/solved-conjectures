import FormalConjecturesUtil
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Incidence certificates for finite Steiner triple designs

Each entry of `rows` lists, in binary, the blocks through one point. For
three distinct points the bitwise intersection must be a single block.
-/

namespace Erdos722.SmallOrders
open Finset

def column (rows : List ℕ) (j : ℕ) : Finset (Fin rows.length) :=
  univ.filter fun x => (rows.get x).testBit j

def blocks (rows : List ℕ) (b : ℕ) : Finset (Finset (Fin rows.length)) :=
  (range b).image (column rows)

/-- The positive divisors of a power of two are powers of two. The strict bound
selects the b available columns, and the remainder test also excludes zero. -/
def single (b m : ℕ) : Bool :=
  decide (m < 1 <<< b) && ((1 <<< b) % m == 0)

def pairs (b p : ℕ) : List ℕ → Bool
  | [] => true
  | q :: qs => qs.all (fun r => single b (p &&& q &&& r)) && pairs b p qs

def triples (b : ℕ) : List ℕ → Bool
  | [] => true
  | p :: ps => pairs b p ps && triples b ps

private theorem pairs_sound {b p : ℕ} {qs : List ℕ} (h : pairs b p qs = true)
    (i j : Fin qs.length) (hij : i < j) :
    single b (p &&& qs.get i &&& qs.get j) = true := by
  induction qs with
  | nil => exact Fin.elim0 i
  | cons q qs ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    refine Fin.cases ?_ (fun i => ?_) i j hij
    · intro j
      refine Fin.cases (by simp) (fun j _ => ?_) j
      exact List.all_eq_true.mp h₁ _ (List.get_mem _ j)
    · intro j
      refine Fin.cases (by simp) (fun j hij => ?_) j
      exact ih h₂ i j (Fin.succ_lt_succ_iff.mp hij)

private theorem triples_sound {b : ℕ} {ps : List ℕ} (h : triples b ps = true)
    (i j k : Fin ps.length) (hij : i < j) (hjk : j < k) :
    single b (ps.get i &&& ps.get j &&& ps.get k) = true := by
  induction ps with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    refine Fin.cases ?_ (fun i => ?_) i j k hij hjk
    · intro j
      refine Fin.cases (by simp) (fun j k _ => ?_) j
      refine Fin.cases (by simp) (fun k hjk => ?_) k
      exact pairs_sound h₁ j k (Fin.succ_lt_succ_iff.mp hjk)
    · intro j
      refine Fin.cases (by simp) (fun j k hij => ?_) j
      refine Fin.cases (by simp) (fun k hjk => ?_) k
      exact ih h₂ i j k (Fin.succ_lt_succ_iff.mp hij) (Fin.succ_lt_succ_iff.mp hjk)

private theorem column_card (ps : List ℕ) (j : ℕ) :
    (column ps j).card = ps.countP (·.testBit j) := by
  unfold column
  rw [← List.toFinset_finRange, (List.nodup_finRange _).card_eq_countP]
  conv_rhs => rw [← List.map_get_finRange ps, List.countP_map]
  simp [Function.comp_def]

/-- Certify the canonical rank-three predicate from column sizes and triple intersections. -/
theorem design_of_incidence_rows {ps : List ℕ} {b k : ℕ}
    (sizes : ∀ j < b, ps.countP (·.testBit j) = k) (check : triples b ps = true) :
    (blocks ps b).IsBlockDesign 3 k := by
  constructor
  · intro B hB
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hB
    exact (column_card _ _).trans (sizes _ (mem_range.mp hj))
  · intro T hT
    obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := card_eq_three.mp hT
    have checked (a b' c : Fin ps.length) (hab : a < b') (hbc : b' < c) :
        single b (ps.get a &&& ps.get b' &&& ps.get c) = true :=
      triples_sound check a b' c hab hbc
    have perm (a d c : ℕ) : a &&& d &&& c = a &&& c &&& d := by ac_rfl
    have left_comm (a d c : ℕ) : a &&& (d &&& c) = d &&& (a &&& c) := by ac_rfl
    have h : single b (ps.get x &&& ps.get y &&& ps.get z) = true := by
      rcases lt_or_gt_of_ne hxy with h | h
      · rcases lt_or_gt_of_ne hyz with h' | h'
        · exact checked _ _ _ h h'
        · rcases lt_or_gt_of_ne hxz with h'' | h''
          · rw [perm]; exact checked _ _ _ h'' h'
          · simpa only [Nat.land_assoc, Nat.land_comm, left_comm] using checked _ _ _ h'' h
      · rcases lt_or_gt_of_ne hxz with h' | h'
        · simpa only [Nat.land_assoc, Nat.land_comm, left_comm] using checked _ _ _ h h'
        · rcases lt_or_gt_of_ne hyz with h'' | h''
          · simpa only [Nat.land_assoc, Nat.land_comm, left_comm] using checked _ _ _ h'' h'
          · simpa only [Nat.land_assoc, Nat.land_comm, left_comm] using checked _ _ _ h'' h
    let m := ps.get x &&& ps.get y &&& ps.get z
    obtain ⟨hm,he⟩ := Bool.and_eq_true_iff.mp h
    have hlt : m < 2^b := by simpa only [Nat.one_shiftLeft] using of_decide_eq_true hm
    have hdvd : m ∣ 2^b := by
      rw [← Nat.one_shiftLeft]
      exact Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp he)
    obtain ⟨col,_,heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hc : col < b := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (heq ▸ hlt)
    have contained (j : ℕ) : {x,y,z} ⊆ column ps j ↔ col = j := by
      have hbit := congrArg (fun t : ℕ => t.testBit j) heq
      simp only [m,Nat.testBit_and,Nat.testBit_two_pow] at hbit
      simpa [m, column, Finset.insert_subset_iff, and_assoc] using
        (Iff.of_eq (congrArg (fun u : Bool => u = true) hbit))
    refine ⟨column ps col,⟨mem_image_of_mem _ (mem_range.mpr hc),(contained _).2 rfl⟩,?_⟩
    rintro B ⟨hB,hsub⟩
    obtain ⟨j,_,rfl⟩ := mem_image.mp hB
    rw [(contained j).1 hsub]

#print axioms column
#print axioms blocks
#print axioms single
#print axioms pairs
#print axioms triples
#print axioms design_of_incidence_rows
end Erdos722.SmallOrders
