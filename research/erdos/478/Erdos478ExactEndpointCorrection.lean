import Erdos478FactorialEndpointCounts
import Erdos478GaloisObservables

/-! # The exact correction between modular roots and positive factorial endpoints -/

namespace Erdos478.LocalWitness
open Polynomial Finset FrobeniusCounts SplittingDensity
open scoped Classical
noncomputable section

def inclusiveEndpoints (k p : ℕ) := (Ico k p).filter fun j => (j-k).factorial%p=j.factorial%p

theorem inclusive_iff_root {k p : ℕ} [hpr : Fact p.Prime] (x : ZMod p) :
    x.val∈inclusiveEndpoints k p ↔ ((gapPoly k).map (Int.castRingHom (ZMod p))).IsRoot x := by
  constructor
  · intro h
    obtain ⟨mem,he⟩ := mem_filter.mp h
    obtain ⟨lo,hi⟩ := mem_Ico.mp mem
    have same := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr he
    have nz : ((x.val-k).factorial : ZMod p)≠0 := by
      rw [Ne,ZMod.natCast_eq_zero_iff,hpr.out.dvd_factorial]
      omega
    have product := congrArg (fun j : ℕ => (j:ZMod p)) (Nat.factorial_mul_descFactorial lo)
    simp only [Nat.cast_mul] at product
    have one : (x.val.descFactorial k : ZMod p)=1 := mul_left_cancel₀ nz (by simpa only [mul_one] using product.trans same.symm)
    rw [← descPochhammer_eval_eq_descFactorial,ZMod.natCast_zmod_val] at one
    simpa [gapPoly,IsRoot,sub_eq_zero] using one
  · intro root
    have ⟨lo,he⟩ := FallingGap.endpoints_of_root (show (FallingGap.gap (ZMod p) k).IsRoot x from
      by simpa [FallingGap.gap,gapPoly] using root)
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨lo,x.val_lt⟩,he⟩

theorem inclusive_count (k p : ℕ) [hpr : Fact p.Prime] :
    (inclusiveEndpoints k p).card=primeRoots (gapPoly k) p := by
  let F (j : inclusiveEndpoints k p) : RootPairs.solutions (gapPoly k) (ZMod p) := by
    have hj : j.val<p := (mem_Ico.mp (mem_filter.mp j.prop).1).2
    refine ⟨(j.val:ZMod p),?_⟩
    have h := (inclusive_iff_root (k:=k) (j.val:ZMod p)).mp (by rw [ZMod.val_natCast_of_lt hj]; exact j.prop)
    simpa only [IsRoot.def,eval_map] using h
  have bij : Function.Bijective F := by
    constructor
    · intro a b eq
      have ha : a.val<p := (mem_Ico.mp (mem_filter.mp a.prop).1).2
      have hb : b.val<p := (mem_Ico.mp (mem_filter.mp b.prop).1).2
      have h := congrArg (fun u : RootPairs.solutions (gapPoly k) (ZMod p) => u.val.val) eq
      exact Subtype.ext (by simpa [F,ZMod.val_natCast_of_lt ha,ZMod.val_natCast_of_lt hb] using h)
    · rintro ⟨x,hx⟩
      have root : ((gapPoly k).map (Int.castRingHom (ZMod p))).IsRoot x := by simpa only [IsRoot.def,eval_map] using hx
      exact ⟨⟨x.val,(inclusive_iff_root x).mpr root⟩,Subtype.ext (ZMod.natCast_zmod_val x)⟩
  exact (Nat.card_eq_finsetCard _).symm.trans (Nat.card_congr (Equiv.ofBijective F bij))

/-- Over every prime, the only possible root to discard is k itself: it would
give the lower index zero. The root count here counts distinct roots. -/
theorem endpoint_correction (k p : ℕ) [hpr : Fact p.Prime] :
    primeRoots (gapPoly k) p=(endpoints k p).card + if k<p ∧ k.factorial%p=1 then 1 else 0 := by
  rw [← inclusive_count]
  have eq : (inclusiveEndpoints k p).erase k=endpoints k p := by
    ext j
    simp only [inclusiveEndpoints,endpoints,mem_erase,mem_filter,mem_Ico]
    omega
  have key : k∈inclusiveEndpoints k p ↔ k<p ∧ k.factorial%p=1 := by
    simp [inclusiveEndpoints,Nat.mod_eq_of_lt hpr.out.one_lt,eq_comm]
  by_cases h : k∈inclusiveEndpoints k p
  · rw [if_pos (key.mp h),← eq,card_erase_of_mem h]
    have nz := card_pos.mpr ⟨k,h⟩
    omega
  · rw [if_neg (fun yes => h (key.mpr yes)),← eq,erase_eq_of_notMem h,add_zero]

#print axioms inclusiveEndpoints
#print axioms inclusive_iff_root
#print axioms inclusive_count
#print axioms endpoint_correction
end
end Erdos478.LocalWitness
