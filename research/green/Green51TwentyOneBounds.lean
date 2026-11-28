import Green51TwentyOne
import Green51TwentyFourBounds
import Green51TwelveAffineBounds

/-! # Sharp affine and linear three-space thresholds in twelve dimensions -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51TwentyOne
local notation "F" => ZMod 2
local notation "V" => Cube 12

/-- The least cardinality forcing an affine three-flat is 21. -/
theorem affine_iff (k:ℕ) : (∀A:Finset V,k≤A.card → ∃p,FlatAt A p) ↔ 21≤k := by
  constructor
  · intro all
    by_contra! low
    exact Green51TwelveAffineWitness.no_affine (all _ (by
      rw [Green51TwelveAffineWitness.labels_card];omega))
  · intro hk A hA
    obtain ⟨B,sub,size⟩ := exists_subset_card_eq (hk.trans hA)
    obtain ⟨p,hp⟩ := twenty_one B size
    exact ⟨p,Green51FlatSections.flat_mono sub hp⟩

private theorem density (A:Finset V) : (A.dens:ℝ)=(A.card:ℝ)/4096 := by
  rw [nnratCast_dens];norm_num [Cube]

/-- A translated three-space is guaranteed precisely above density 20/4096. -/
theorem dimension_iff {α:ℝ} (one:α≤1) :
    3≤Green51.guaranteedMaxCosetDim 12 α ↔ 20/4096<α := by
  constructor
  · intro dim
    by_contra! small
    let A := Green51TwelveAffineWitness.labels
    have pts:A.card=20 := Green51TwelveAffineWitness.labels_card
    have adm:α≤(A.dens:ℝ) := by simpa only [density,pts,Nat.cast_ofNat] using small
    rw [Green51LocalFlats.guaranteed_iff (by decide) one] at dim
    obtain ⟨B,sub,_,W,_,p,_,_,_,d,inside⟩ := dim A adm
    exact Green51TwelveAffineWitness.no_affine ⟨p,Green51FlatSections.flat_mono sub ⟨W,d,inside⟩⟩
  · intro lo
    rw [Green51LocalFlats.guaranteed_iff (by decide) one]
    intro A adm
    have lt:=lo.trans_le adm
    rw [density,div_lt_div_iff_of_pos_right (by norm_num)] at lt
    have large:21≤A.card := by exact_mod_cast (show (20:ℝ)<A.card from lt)
    obtain ⟨p,W,d,inside⟩ := (affine_iff 21).mpr le_rfl A large
    obtain ⟨S,L,a,sA,restricted,ambient,_,_,count,rank⟩ := Green51LocalFlats.local_labels A W p inside
    exact ⟨S,sA,L,W,a,p,d ▸ count,d ▸ rank,ambient,d,restricted⟩

/-- From minimum cardinality 21 through 25 the exact guaranteed dimension is
three. One admissible twenty-five-point set still excludes all linear three-spaces. -/
theorem plateau {α:ℝ} (lo:20/4096<α) (hi:α≤25/4096) :
    Green51.guaranteedMaxCosetDim 12 α=3 ∧
      ∃A:Finset V,A.card=25 ∧ α≤(A.dens:ℝ) ∧ ¬FlatAt A 0 := by
  obtain ⟨_,A,size,hA,no⟩ := Green51TwelveSections.plateau (α:=25/4096) (by norm_num) le_rfl
  have adm:=hi.trans hA
  have top:Green51.guaranteedMaxCosetDim 12 α ≤ maxCosetDim F V ↑(A+A) :=
    csInf_le (OrderBot.bddBelow _) ⟨A,adm,rfl⟩
  have bound := Green51SmallWitnesses.max_dim_of_avoiding A (by decide : 2≤3)
    (fun h=>no ((flat_zero A).mpr h)) (by rw [size];decide)
  exact ⟨le_antisymm (top.trans bound) ((dimension_iff (by linarith)).mpr lo),A,size,adm,no⟩

end Green51TwentyOne
#print axioms Green51TwentyOne.affine_iff
#print axioms Green51TwentyOne.dimension_iff
#print axioms Green51TwentyOne.plateau
