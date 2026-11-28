import Green51TwelveAffine
import Green51TwelveAffineWitness
import Green51TwelveThreshold

/-! # The original Green guarantee at sparse densities in dimension twelve -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51TwelveAffine
local notation "F" => ZMod 2
local notation "V" => Cube 12

private theorem density (A : Finset V) : (A.dens : ℝ) = (A.card : ℝ)/4096 := by
  rw [nnratCast_dens]; norm_num [Cube]

/-- From the third required label through the twentieth, the guaranteed affine dimension is two. -/
theorem two_plateau {α : ℝ} (lo : 2/4096 < α) (hi : α ≤ 20/4096) :
    Green51.guaranteedMaxCosetDim 12 α = 2 := by
  have one : α ≤ 1 := by linarith
  have upper : ¬3 ≤ Green51.guaranteedMaxCosetDim 12 α := by
    rw [Green51LocalFlats.guaranteed_iff (by decide) one]
    intro h
    have admissible : α ≤ (Green51TwelveAffineWitness.labels.dens : ℝ) := by
      simpa only [density, Green51TwelveAffineWitness.labels_card, Nat.cast_ofNat] using hi
    obtain ⟨B, sub, _, W, _, p, _, _, _, d, inside⟩ := h _ admissible
    exact Green51TwelveAffineWitness.no_affine
      ⟨p, Green51FlatSections.flat_mono sub ⟨W,d,inside⟩⟩
  have lower : 2 ≤ Green51.guaranteedMaxCosetDim 12 α := by
    apply Green51SparseBounds.two_above_two_points one
    convert lo using 1; norm_num
  omega

/-- Densities strictly above 24/4096 already guarantee an affine three-space. -/
theorem three_above {α : ℝ} (lo : 24/4096 < α) (one : α ≤ 1) :
    3 ≤ Green51.guaranteedMaxCosetDim 12 α := by
  rw [Green51LocalFlats.guaranteed_iff (by decide) one]
  intro A hA
  have lt := lo.trans_le hA
  rw [density, div_lt_div_iff_of_pos_right (by norm_num)] at lt
  have enough : 25≤A.card := by exact_mod_cast (show (24:ℝ)<A.card from lt)
  obtain ⟨B,sub,size⟩ := exists_subset_card_eq enough
  obtain ⟨p,h⟩ := twenty_five B size
  obtain ⟨W,d,inside⟩ := Green51FlatSections.flat_mono sub h
  obtain ⟨S,L,a,sA,restricted,ambient,_,_,count,rank⟩ :=
    Green51LocalFlats.local_labels A W p inside
  exact ⟨S,sA,L,W,a,p,d ▸ count,d ▸ rank,ambient,d,restricted⟩

/-- At twenty-five required labels the guarantee is exactly three, and the
guaranteed flat can be forced to miss the origin. -/
theorem twenty_five_plateau {α : ℝ} (lo : 24/4096 < α) (hi : α ≤ 25/4096) :
    Green51.guaranteedMaxCosetDim 12 α = 3 ∧
      ∃ A : Finset V, A.card=25 ∧ α≤(A.dens:ℝ) ∧ ¬FlatAt A 0 := by
  have missing : ¬∀ A : Finset V, 25≤A.card → FlatAt A 0 := by
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
  exact ⟨le_antisymm (top.trans bound) (three_above lo (by linarith)), A, size, adm, avoid⟩

end Green51TwelveAffine
#print axioms Green51TwelveAffine.two_plateau
#print axioms Green51TwelveAffine.three_above
#print axioms Green51TwelveAffine.twenty_five_plateau
