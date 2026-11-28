import Erdos478SexticSplittingDegree
import Erdos478EvenGapSaturation

/-! # The sextic contribution to a joint factorial collision bound -/

namespace Erdos478.SplittingDensity
open Polynomial Finset SexticGap

/-- Each additional half-gap is charged its paired degree bound.
The sixth gap itself costs exactly 24 in the degree estimate. -/
theorem sextic_joint_cost {m : ℕ} (hm : 0<m) (R : Finset ℕ)
    (hpos : ∀ r∈R, 0<r) (h3 : 3∉R) :
    ((m.totient*(24*pairingProduct R) : ℕ):ℝ)⁻¹ ≤ splitDensity m (insert 6 (evenLengths R)) := by
  let S := insert 6 (evenLengths R)
  let weight (k : ℕ) := if k=6 then 24 else 2^(k/2)*(k/2).factorial
  have hnot : 6∉evenLengths R := by
    rintro h
    obtain ⟨r,hr,he⟩ := mem_image.mp h
    exact h3 ((show r=3 by omega) ▸ hr)
  have hk : ∀ k∈S, 0<k := by
    intro k hk
    rcases mem_insert.mp hk with rfl|hk
    · decide
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hk
    exact Nat.mul_pos (by decide) (hpos r hr)
  have hw : ∀ k∈S, Module.finrank ℚ (SplitField (gapPoly k)) ≤ weight k := by
    intro k hk
    rcases mem_insert.mp hk with rfl|hk
    · simp [weight,sextic_splitting_degree]
    have hn : k≠6 := fun h => hnot (h ▸ hk)
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hk
    simpa [weight,hn] using even_gap_field_degree (hpos r hr)
  have he : ∏ k∈S, weight k=24*pairingProduct R := by
    rw [prod_insert hnot,evenLengths,prod_image (by intro i _ j _ e; exact Nat.eq_of_mul_eq_mul_left (by decide : 0<2) e)]
    congr 1
    apply prod_congr rfl
    intro r hr
    have hn : 2*r≠6 := fun e => h3 ((show r=3 by omega) ▸ hr)
    simp [weight,hn]
  apply inv_anti₀ (by exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=SplitField (test m S))))
  exact_mod_cast (field_degree_bound_of hm S hk weight hw).trans_eq (congrArg (m.totient*·) he)

#print axioms sextic_joint_cost
end Erdos478.SplittingDensity
