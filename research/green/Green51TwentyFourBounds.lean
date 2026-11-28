import Green51TwentyFourLabels
import Green51TwelveThreshold

/-! # The twenty-four and twenty-five label density interval for Green 51 -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51TwelveSections
local notation "F" => ZMod 2
local notation "V" => Cube 12

private theorem density (A : Finset V) : (A.dens : ℝ)=(A.card:ℝ)/4096 := by
  rw [nnratCast_dens]; norm_num [Cube]

theorem three_above {α : ℝ} (lo : 23/4096<α) (one : α≤1) :
    3≤Green51.guaranteedMaxCosetDim 12 α := by
  rw [Green51LocalFlats.guaranteed_iff (by decide) one]
  intro A hA
  have lt := lo.trans_le hA
  rw [density,div_lt_div_iff_of_pos_right (by norm_num)] at lt
  have enough : 24≤A.card := by exact_mod_cast (show (23:ℝ)<A.card from lt)
  obtain ⟨B,sub,size⟩ := exists_subset_card_eq enough
  obtain ⟨p,h⟩ := twenty_four B size
  obtain ⟨W,d,inside⟩ := Green51FlatSections.flat_mono sub h
  obtain ⟨S,L,a,sA,restricted,ambient,_,_,count,rank⟩ :=
    Green51LocalFlats.local_labels A W p inside
  exact ⟨S,sA,L,W,a,p,d ▸ count,d ▸ rank,ambient,d,restricted⟩

/-- Green's guaranteed dimension is exactly three if the minimum required
cardinality is twenty-four or twenty-five. A single admissible set excludes
every three-space through the origin throughout the interval. -/
theorem plateau {α : ℝ} (lo : 23/4096<α) (hi : α≤25/4096) :
    Green51.guaranteedMaxCosetDim 12 α=3 ∧
      ∃A : Finset V,A.card=25 ∧ α≤(A.dens:ℝ) ∧ ¬FlatAt A 0 := by
  have missing : ¬∀A : Finset V,25≤A.card → FlatAt A 0 := by
    intro h
    have := (Green51TwelveThreshold.linear_iff 25).mp h
    omega
  push Not at missing
  obtain ⟨B,large,avoids⟩ := missing
  obtain ⟨A,sub,size⟩ := exists_subset_card_eq large
  have avoid : ¬FlatAt A 0 := fun h => avoids (Green51FlatSections.flat_mono sub h)
  have adm : α≤(A.dens:ℝ) := by simpa only [density,size,Nat.cast_ofNat] using hi
  have top : Green51.guaranteedMaxCosetDim 12 α ≤ maxCosetDim F V ↑(A+A) :=
    csInf_le (OrderBot.bddBelow _) ⟨A,adm,rfl⟩
  have bound := Green51SmallWitnesses.max_dim_of_avoiding A (by decide : 2≤3)
    (fun h => avoid ((flat_zero A).mpr h)) (by rw [size];decide)
  exact ⟨le_antisymm (top.trans bound) (three_above lo (by linarith)),A,size,adm,avoid⟩

end Green51TwelveSections
#print axioms Green51TwelveSections.three_above
#print axioms Green51TwelveSections.plateau
