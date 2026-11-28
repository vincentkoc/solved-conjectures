import Erdos722SignedSteinerObstruction
import Mathlib.Combinatorics.Configuration

/-!
# The projective plane in a symmetric pair design

A Steiner pair design with line size q+1 and q²+q+1 points gives a
projective plane of order q in mathlib's incidence convention.
-/

namespace Erdos722.MinimumOrder
open Finset IntegralDesign Configuration

private theorem twice_choose_two (a : ℕ) : 2*(a+1).choose 2=(a+1)*a := by
  change Nat.factorial 2 * _ = _
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  simp [Nat.descFactorial_succ,mul_comm]

private theorem block_total {q : ℕ} (hq : 2≤q)
    {H : Finset (Finset (Fin (q*(q+1)+1)))} (hH : H.IsBlockDesign 2 (q+1)) :
    H.card=q*(q+1)+1 := by
  have h := flag_count hH ∅ (by simp)
  simp only [card_empty,Nat.sub_zero,empty_subset,filter_true] at h
  have ht := congrArg (2*·) h
  rw [← Nat.mul_assoc,twice_choose_two,twice_choose_two] at ht
  apply Nat.eq_of_mul_eq_mul_left (show 0<q*(q+1) by positivity)
  calc
    q*(q+1)*H.card = (q+1)*q*H.card := by ring
    _ = _ := ht.trans (by ring)

private theorem pencil_total {q : ℕ} (hq : 2≤q)
    {H : Finset (Finset (Fin (q*(q+1)+1)))} (hH : H.IsBlockDesign 2 (q+1))
    (x : Fin (q*(q+1)+1)) : (H.filter (x∈·)).card=q+1 := by
  have h := flag_count hH {x} (by simp)
  simpa only [card_singleton,singleton_subset_iff,Nat.add_sub_cancel,Nat.reduceSub,
    Nat.choose_one_right,mul_right_inj' (by omega : q≠0)] using h

private theorem pair_unique {P : Type*} [DecidableEq P] {k : ℕ} {H : Finset (Finset P)}
    (hH : H.IsBlockDesign 2 k) {x y : P} (hxy : x ≠ y) :
    ∃! B : Finset P, B∈H ∧ x∈B ∧ y∈B := by
  simpa [insert_subset_iff,singleton_subset_iff] using
    hH.2 {x,y} (by simp [hxy])

/-- The point and line types, incidence, and order in the same form as
the projective-plane predicate used by Erdős 723. -/
theorem projective_plane_of_symmetric_pairs {q : ℕ} (hq : 2≤q)
    {H : Finset (Finset (Fin (q*(q+1)+1)))} (hH : H.IsBlockDesign 2 (q+1)) :
    ∃ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L)
      (pp : ProjectivePlane P L), pp.order=q := by
  classical
  let P := Fin (q*(q+1)+1)
  let L := (H : Type)
  let : Membership P L := ⟨fun l x => x∈l.val⟩
  let pencil (x : P) := H.filter (x∈·)
  have hb := block_total hq hH
  have hp (x : P) : (pencil x).card=q+1 := pencil_total hq hH x
  have hbig : 2*(q+1)<q*(q+1)+1 := by nlinarith [Nat.mul_le_mul_right (q+1) hq]
  have hpts : (univ : Finset P).card=q*(q+1)+1 := by simp [P]
  have outside (A : Finset P) (hA : A.card<(univ : Finset P).card) : ∃ x : P, x∉A := by
    obtain ⟨x,_,hx⟩ := exists_mem_notMem_of_card_lt_card hA
    exact ⟨x,hx⟩
  have eqline {x y : P} {l m : L} (hxy : x≠y)
      (hx : x∈l) (hy : y∈l) (hx' : x∈m) (hy' : y∈m) : l=m :=
    Subtype.ext ((pair_unique hH hxy).unique ⟨l.property,hx,hy⟩ ⟨m.property,hx',hy'⟩)
  let : Nondegenerate P L := {
    exists_point := fun l => outside l.val (by rw [hpts,hH.1 _ l.property]; omega)
    exists_line := fun x => by
      obtain ⟨B,hB,hx⟩ := exists_mem_notMem_of_card_lt_card (show (pencil x).card<H.card by rw [hp,hb]; omega)
      exact ⟨⟨B,hB⟩,fun hxB => hx (mem_filter.mpr ⟨hB,hxB⟩)⟩
    eq_or_eq := fun hx hy hx' hy' => or_iff_not_imp_left.mpr fun hxy => eqline hxy hx hy hx' hy' }
  let join {x y : P} (h : x≠y) : L := ⟨(pair_unique hH h).choose,(pair_unique hH h).choose_spec.1.1⟩
  let : HasLines P L := {
    mkLine := fun h => join h
    mkLine_ax := fun h => (pair_unique hH h).choose_spec.1.2 }
  have heq : Fintype.card P = Fintype.card L := by simp [P,L,hb]
  let : HasPoints P L := HasLines.hasPoints heq
  obtain ⟨B,hB⟩ := card_pos.mp (show 0<H.card by rw [hb]; positivity)
  obtain ⟨x,y,hx,hy,hxy⟩ := one_lt_card_iff.mp (show 1<B.card by rw [hH.1 B hB]; omega)
  obtain ⟨C,hC,hCB⟩ := exists_mem_notMem_of_card_lt_card
    (s:={B}) (t:=pencil x) (by rw [card_singleton,hp]; omega)
  have hxC := (mem_filter.mp hC).2
  have hc := (mem_filter.mp hC).1
  have hyC : y∉C := by
    intro hy'
    exact hCB (mem_singleton.mpr ((pair_unique hH hxy).unique ⟨hc,hxC,hy'⟩ ⟨hB,hx,hy⟩))
  obtain ⟨z,hz⟩ := outside (B∪C) (by
    rw [hpts]
    exact (card_union_le _ _).trans_lt (by rw [hH.1 _ hB,hH.1 _ hc]; omega))
  obtain ⟨A,hA,hA'⟩ := exists_mem_notMem_of_card_lt_card
    (s:=pencil x∪pencil y) (t:=H) (by rw [hb]; exact (card_union_le _ _).trans_lt (by rw [hp,hp]; omega))
  have hxA : x∉A := fun h => hA' (mem_union_left _ (mem_filter.mpr ⟨hA,h⟩))
  have hyA : y∉A := fun h => hA' (mem_union_right _ (mem_filter.mpr ⟨hA,h⟩))
  let pp : ProjectivePlane P L := { (inferInstance : HasLines P L), (inferInstance : HasPoints P L) with
    exists_config := ⟨z,x,y,⟨A,hA⟩,⟨B,hB⟩,⟨C,hc⟩,fun h => hz (mem_union_left _ h),
      fun h => hz (mem_union_right _ h),hxA,hx,hxC,hyA,hy,hyC⟩ }
  refine ⟨P,L,inferInstance,inferInstance,inferInstance,pp,?_⟩
  have ht := ProjectivePlane.pointCount_eq P (⟨B,hB⟩ : L)
  change Nat.card {x : P // x∈B} = pp.order+1 at ht
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,hH.1 _ hB] at ht
  omega

#print axioms projective_plane_of_symmetric_pairs
end Erdos722.MinimumOrder
