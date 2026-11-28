import Mathlib

/-! Prime residues whose prescribed power has order four. -/

namespace CunninghamChain.JonesSplitParity

/-- The prime used on the opposite side of a split can detect a factor with
any positive multiplicity e when its multiplicative group has order divisible by 4e. -/
theorem exists_weighted_fourth_root {p e : ℕ} (hp : p.Prime) (hp₂ : 2 < p)
    (he : 0 < e) (hd : 4*e ∣ p-1) :
    ∃ a : ℕ, a.Coprime p ∧ ((a : ZMod p)^e)^2 = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,gen⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have ord : orderOf (g : ZMod p) = p-1 := by
    rw [orderOf_units,gen,Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,Nat.totient_prime hp]
  let z := (g : ZMod p) ^ (orderOf (g : ZMod p)/(4*e))
  have hz : orderOf z = 4*e := orderOf_pow_orderOf_div (by omega) (ord ▸ hd)
  have unit : IsUnit z := isUnit_iff_ne_zero.mpr (pow_ne_zero _ g.ne_zero)
  refine ⟨z.val,(ZMod.isUnit_iff_coprime ..).mp (by simpa using unit),?_⟩
  rw [ZMod.natCast_zmod_val,←pow_mul]
  apply (CharP.orderOf_eq_two_iff p (by omega)).mp
  have div : e*2 ∣ orderOf z := by rw [hz]; exact ⟨2,by ring⟩
  rw [orderOf_pow_of_dvd (by omega) div,hz]
  exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)

#print axioms exists_weighted_fourth_root

end CunninghamChain.JonesSplitParity
