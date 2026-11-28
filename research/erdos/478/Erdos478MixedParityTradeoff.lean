import Erdos478AntipodalProducts
import Erdos478ReflectedParityValues

/-! # Two losses in the count of products of opposite-parity factorials -/

namespace Erdos478.ParityProducts
open Finset
open scoped Classical
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def commonValues (p : ℕ) := parityValues p 0 ∩ parityValues p 1

private theorem half_core (hp : p%2=1) : ∃ H : Finset (ZMod p),
    Disjoint H (H.image Neg.neg) ∧ H ∪ H.image Neg.neg ⊆ allValues p ∧
    (commonValues p).card≤2*H.card := by
  let A := allValues p
  let K := A.filter (fun x => -x∈A)
  let H := K.filter (fun x => x.val<(-x).val)
  have kn {x : ZMod p} (hx : x∈K) : -x∈K :=
    mem_filter.mpr ⟨(mem_filter.mp hx).2,by simpa using (mem_filter.mp hx).1⟩
  have nx {x : ZMod p} (hx : x∈K) : x≠0 := by
    rcases mem_union.mp (mem_filter.mp hx).1 with ev|od
    · exact no_zero ev
    · exact no_zero od
  have un : H ∪ H.image Neg.neg=K := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with left|right
      · exact (mem_filter.mp left).1
      · obtain ⟨y,hy,rfl⟩ := mem_image.mp right
        exact kn (mem_filter.mp hy).1
    · intro hx
      have vl := x.val_lt
      have : NeZero x := ⟨nx hx⟩
      have inv := ZMod.val_neg_of_ne_zero x
      by_cases lt : x.val<(-x).val
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,lt⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨-x,mem_filter.mpr ⟨kn hx,by simp only [neg_neg]; omega⟩,neg_neg x⟩)
  have dis : Disjoint H (H.image Neg.neg) := by
    apply disjoint_left.mpr
    intro x hx hi
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hi
    have a := (mem_filter.mp hx).2
    have b := (mem_filter.mp hy).2
    change (-y).val<(- -y).val at a
    exact (not_lt_of_ge (by simpa only [neg_neg] using a.le)) b
  have core : (commonValues p).image (fun x => x⁻¹) ⊆ K := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
    obtain ⟨he,ho⟩ := mem_inter.mp hx
    have odd : x⁻¹∈parityValues p 1 := by simpa only [if_neg (by decide : 1≠0)] using reflected_value hp ho
    have even : -x⁻¹∈parityValues p 0 := by simpa using reflected_value hp he
    exact mem_filter.mpr ⟨mem_union_right _ odd,mem_union_left _ even⟩
  refine ⟨H,dis,(by rw [un]; exact filter_subset ..),?_⟩
  have bound := card_le_card core
  rw [card_image_of_injective _ inv_injective,← un,card_union_of_disjoint dis,card_image_of_injective _ neg_injective] at bound
  omega

/-- The two independent overcounts in the mixed product image arise
from reversing an overlapping pair and negating an antipodal pair. -/
theorem mixed_count_bounds (hp : p%2=1) :
    let a := (allValues p).card
    let t := (commonValues p).card
    let m := (mixedProducts p).card
    m+t.choose 2≤(parityValues p 0).card*(parityValues p 1).card ∧
    4*m+t^2≤2*a*(a+1) := by
  dsimp only
  constructor
  · let L := LinearOrder.lift' ZMod.val (ZMod.val_injective p)
    exact @mixed_image_bound (ZMod p) (ZMod p) L (ZMod.decidableEq p) (·*·) mul_comm (parityValues p 0) (parityValues p 1)
  · obtain ⟨H,dis,sub,bound⟩ := half_core hp
    have ss : mixedProducts p ⊆ (allValues p).sym2.image pairProduct := by
      intro x hx
      obtain ⟨e,he,o,ho,rfl⟩ := mem_mixed.mp hx
      exact mem_image.mpr ⟨s(e,o),mk_mem_sym2_iff.mpr ⟨mem_union_left _ he,mem_union_right _ ho⟩,rfl⟩
    have c := card_le_card ss
    have b := antipodal_products (allValues p) H dis sub
    nlinarith only [c,b,two_choose (allValues p).card,Nat.pow_le_pow_left bound 2]

/-- The finite parity-resolved inequality. Both squared terms measure
information lost by keeping only the cardinality of the factorial image. -/
theorem parity_tradeoff (hp : p%2=1) :
    let a : ℤ := ((Ico 1 p).image (fun i => i.factorial%p)).card
    let t : ℤ := (commonValues p).card
    let e : ℤ := (parityValues p 0).card
    let o : ℤ := (parityValues p 1).card
    16*((mixedProducts p).card:ℤ)+(a-2*t)^2+2*(e-o)^2 ≤ 7*a^2+4*(a+t) := by
  dsimp only
  obtain ⟨m,k⟩ := mixed_count_bounds hp
  have part : (allValues p).card+(commonValues p).card=(parityValues p 0).card+(parityValues p 1).card :=
    card_union_add_card_inter _ _
  have c (n : ℕ) : 2*(n.choose 2)+n=n*n := by
    cases n with
    | zero => decide
    | succ n => nlinarith only [two_choose n]
  rw [← host_card]
  zify at m k part
  have cc := c (commonValues p).card
  zify at cc
  nlinarith only [m,k,cc,congrArg (fun z : ℤ => z^2) part]

theorem mixed_capacity (hp : p%2=1) :
    let a := ((Ico 1 p).image (fun i => i.factorial%p)).card
    16*(mixedProducts p).card ≤ 7*a^2+8*a := by
  dsimp only
  have t : commonValues p ⊆ allValues p := fun _ h => mem_union_left _ (mem_inter.mp h).1
  have ht := card_le_card t
  rw [host_card] at ht
  have h := parity_tradeoff hp
  dsimp only at h
  zify at ht ⊢
  nlinarith only [h,ht,sq_nonneg ((((Ico 1 p).image (fun i => i.factorial%p)).card:ℤ)-2*(commonValues p).card),
    sq_nonneg (((parityValues p 0).card:ℤ)-(parityValues p 1).card)]

#print axioms commonValues
#print axioms mixed_count_bounds
#print axioms parity_tradeoff
#print axioms mixed_capacity
end
end Erdos478.ParityProducts
