import Erdos478SexticEndpoints

/-!
# The shared upper endpoint of the third and sixth gaps

If the two windows ending at x have product one, the two adjacent
three-factor products are both one. Eliminating their common root gives
the prime 347. The unique shared upper endpoint there is 328.
-/

namespace Erdos478.GapReality
open Finset Polynomial SplittingDensity SexticGap
open scoped Classical

private theorem product_one {p k j : ℕ} (hp : p.Prime) (hj : j∈endpoints k p) :
    (descPochhammer (ZMod p) k).eval (j:ZMod p)=1 := by
  rw [endpoints_eq_short_product hp] at hj
  rw [descPochhammer_eval_eq_descFactorial]
  simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff' (j.descFactorial k) 1 p).mpr
    ((mem_filter.mp hj).2.trans (Nat.mod_eq_of_lt hp.one_lt).symm)

/-- Two consecutive gaps never share a positive upper endpoint. Their
window products differ by the factor j−k, which would have to be one. -/
theorem consecutive_endpoint_disjoint {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Disjoint (endpoints k p) (endpoints (k+1) p) := by
  apply disjoint_left.mpr
  intro j hj hj'
  obtain ⟨hl,hu⟩ := mem_Ico.mp (mem_filter.mp hj').1
  have h := product_one hp hj'
  rw [descPochhammer_succ_eval,product_one hp hj,one_mul] at h
  have eq : (j:ZMod p)=((k+1:ℕ):ZMod p) := by push_cast; linear_combination h
  have hh := (ZMod.natCast_eq_natCast_iff' j (k+1) p).mp eq
  rw [Nat.mod_eq_of_lt hu,Nat.mod_eq_of_lt (by omega : k+1<p)] at hh
  omega

private theorem common_prime {p j : ℕ} (hp : p.Prime) (h₃ : j∈endpoints 3 p)
    (h₆ : j∈endpoints 6 p) : p=347 := by
  let : Fact p.Prime := ⟨hp⟩
  let x : ZMod p := j
  have a : x*(x-1)*(x-2)=1 := by
    simpa only [descPochhammer_succ_eval,descPochhammer_zero,eval_one,Nat.cast_zero,Nat.cast_one,
      Nat.cast_ofNat,sub_zero,one_mul,x] using product_one hp h₃
  have b : (x-3)*(x-4)*(x-5)=1 := by
    have h : x*(x-1)*(x-2)*(x-3)*(x-4)*(x-5)=1 := by
      simpa only [descPochhammer_succ_eval,descPochhammer_zero,eval_one,Nat.cast_zero,Nat.cast_one,
        Nat.cast_ofNat,sub_zero,one_mul,x] using product_one hp h₆
    rwa [a,one_mul] at h
  have hp' : 6<p := by have := (mem_Ico.mp (mem_filter.mp h₆).1); omega
  have hn : (3:ZMod p)≠0 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0<3) ((CharP.cast_eq_zero_iff (ZMod p) p 3).mp h)
    omega
  have c : 3*x^2-15*x+20=0 := by
    apply (mul_eq_zero.mp (show 3*(3*x^2-15*x+20)=0 by linear_combination a-b)).resolve_left hn
  have d : 16*x-43=0 := by linear_combination 3*a-(x+2)*c
  have z : (347:ZMod p)=0 := by linear_combination 256*c-(48*x-111)*d
  exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 347)).mp
    ((CharP.cast_eq_zero_iff (ZMod p) p 347).mp z)

set_option maxRecDepth 12000 in
theorem cubic_sextic_intersection {p : ℕ} (hp : p.Prime) :
    endpoints 3 p ∩ endpoints 6 p=if p=347 then {328} else ∅ := by
  by_cases he : p=347
  · subst p
    rw [if_pos rfl,endpoints_eq_short_product hp,endpoints_eq_short_product hp]
    decide
  · rw [if_neg he]
    exact eq_empty_iff_forall_notMem.mpr (fun j hj => he (common_prime hp (mem_inter.mp hj).1 (mem_inter.mp hj).2))

/-- Distinct upper endpoints of two positive gaps can all be discarded
from the image, regardless of coincidences of their factorial values. -/
theorem union_endpoint_deficit (p a b : ℕ) (ha : 0<a) (hb : 0<b) :
    ((Ico 1 p).image (fun i => i.factorial%p)).card+(endpoints a p∪endpoints b p).card≤p-1 := by
  classical
  let V := Ico 1 p
  let U := endpoints a p∪endpoints b p
  let f := fun i : ℕ => i.factorial%p
  have spec {i k : ℕ} (hk : 0<k) (hi : i∈endpoints k p) :
      i∈V ∧ ∃ j∈V, j < i ∧ f j=f i := by
    obtain ⟨hI,hf⟩ := mem_filter.mp hi
    obtain ⟨hl,hu⟩ := mem_Ico.mp hI
    exact ⟨mem_Ico.mpr ⟨by omega,hu⟩,i-k,mem_Ico.mpr ⟨by omega,by omega⟩,by omega,hf⟩
  have repeats {i} (hi : i∈U) := (mem_union.mp hi).elim (spec ha) (spec hb)
  have cover : V.image f⊆(V\U).image f := by
    intro y hy
    have hit : ∃ j, j∈V ∧ f j=y := mem_image.mp hy
    obtain ⟨hm,he⟩ := Nat.find_spec hit
    refine mem_image.mpr ⟨_,mem_sdiff.mpr ⟨hm,?_⟩,he⟩
    intro h
    obtain ⟨j,hj,hl,hf⟩ := (repeats h).2
    exact Nat.find_min hit hl ⟨hj,hf.trans he⟩
  have hle := (card_le_card cover).trans card_image_le
  rw [card_sdiff_of_subset (fun i hi => (repeats hi).1)] at hle
  have hus : U.card≤V.card := card_le_card fun i hi => (repeats hi).1
  change (V.image f).card+U.card≤p-1
  have hv : V.card=p-1 := Nat.card_Ico _ _
  omega

set_option maxRecDepth 12000 in
/-- At every prime the two positive counts give their full combined
deficit. The one exceptional overlap is covered by direct computation. -/
theorem three_six_deficit {p : ℕ} (hp : p.Prime) :
    ((Ico 1 p).image (fun i => i.factorial%p)).card+(endpoints 3 p).card+(endpoints 6 p).card≤p-1 := by
  by_cases he : p=347
  · subst p
    rw [endpoints_eq_short_product hp,endpoints_eq_short_product hp]
    decide
  · have hi := cubic_sextic_intersection hp
    rw [if_neg he] at hi
    have hd := disjoint_iff_inter_eq_empty.mpr hi
    have H := union_endpoint_deficit p 3 6 (by decide) (by decide)
    rwa [card_union_of_disjoint hd,← add_assoc] at H

theorem consecutive_gap_deficit {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0<k) :
    ((Ico 1 p).image (fun i => i.factorial%p)).card+
      (endpoints k p).card+(endpoints (k+1) p).card≤p-1 := by
  have h := union_endpoint_deficit p k (k+1) hk (by omega)
  rwa [card_union_of_disjoint (consecutive_endpoint_disjoint hp k),← add_assoc] at h

#print axioms consecutive_endpoint_disjoint
#print axioms consecutive_gap_deficit
#print axioms cubic_sextic_intersection
#print axioms union_endpoint_deficit
#print axioms three_six_deficit
end Erdos478.GapReality
