import Erdos478WitnessDensityDichotomy
import Erdos478LeastPrimeCollision

/-! # Finite modular tests certifying the first factorial collision law -/

namespace Erdos478.LocalWitness
open Finset Polynomial FrobeniusCounts FirstCollision SplittingDensity
noncomputable section

def rawRoots (p k : ℕ) := (range p).filter fun x => x.descFactorial k%p=1

theorem rawRoots_card (p k : ℕ) [hpr : Fact p.Prime] : (rawRoots p k).card=primeRoots (gapPoly k) p := by
  have test (j : ℕ) : (gapPoly k).eval₂ (Int.castRingHom (ZMod p)) (j:ZMod p)=0 ↔ j.descFactorial k%p=1 := by
    rw [← eval_map]
    simp only [gapPoly,Polynomial.map_sub,descPochhammer_map,Polynomial.map_one,eval_sub,eval_one,
      descPochhammer_eval_eq_descFactorial,sub_eq_zero]
    simpa only [Nat.cast_one,Nat.mod_eq_of_lt hpr.out.one_lt] using ZMod.natCast_eq_natCast_iff' (j.descFactorial k) 1 p
  let F (j : rawRoots p k) : RootPairs.solutions (gapPoly k) (ZMod p) :=
    ⟨(j.val:ZMod p),(test _).mpr (mem_filter.mp j.prop).2⟩
  have bij : Function.Bijective F := by
    constructor
    · intro a b he
      have ha := mem_range.mp (mem_filter.mp a.prop).1
      have hb := mem_range.mp (mem_filter.mp b.prop).1
      have eq := congrArg (fun z : RootPairs.solutions (gapPoly k) (ZMod p) => z.val.val) he
      exact Subtype.ext (by simpa [F,ZMod.val_natCast_of_lt ha,ZMod.val_natCast_of_lt hb] using eq)
    · rintro ⟨x,hx⟩
      have testx := (test x.val).mp (by rwa [ZMod.natCast_zmod_val])
      exact ⟨⟨x.val,mem_filter.mpr ⟨mem_range.mpr x.val_lt,testx⟩⟩,Subtype.ext (ZMod.natCast_zmod_val x)⟩
  exact (Nat.card_eq_finsetCard _).symm.trans (Nat.card_congr (Equiv.ofBijective F bij))

/-- A single regular modular first hit gives an explicit lower bound for the ordinary
first-distance atom, including every intervening composite length in its exclusions. -/
theorem first_mass_of_sample (p l : ℕ) [Fact p.Prime] (hl : 2≤l)
    (reg : ∀ k, 2≤k → k≤l → ((gapPoly k).map (Int.castRingHom (ZMod p))).Separable)
    (earliest : ∀ k, 2≤k → k<l → rawRoots p k=∅) (hit : (rawRoots p l).Nonempty) :
    ((∏ k∈Icc 2 l,k.factorial : ℕ) : ℝ)⁻¹≤firstDensity l := by
  let S := insert l (short (l-1))
  have eq : S=Icc 2 l := by ext k; simp only [S,short,mem_insert,mem_Icc]; omega
  have bounds (k : ℕ) (hk : k∈S) := mem_Icc.mp (eq ▸ hk)
  have h := modular_witness_mass (fun k hk => (bounds k hk).1) (withHit l zeroCounts) p
    (fun k hk => reg k (bounds k hk).1 (bounds k hk).2) (by
      constructor
      · intro i
        change primeRoots (gapPoly i.val) p=0
        rw [← rawRoots_card,earliest i.val (mem_Icc.mp i.prop).1 (by have := (mem_Icc.mp i.prop).2; omega),card_empty]
      · change 0<primeRoots (gapPoly l) p
        rw [← rawRoots_card]; exact card_pos.mpr hit)
  rw [firstDensity,if_pos hl,← eq]
  exact h

#print axioms rawRoots
#print axioms rawRoots_card
#print axioms first_mass_of_sample
end
end Erdos478.LocalWitness
