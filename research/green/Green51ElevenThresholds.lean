import Green51GolayWitnesses
import Green51NineteenLabels

/-! # The exact affine and linear three-space thresholds in dimension eleven -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51GolayWitnesses
open scoped Classical Pointwise
namespace Green51ElevenThresholds
local notation "F" => ZMod 2
local notation "V" => Cube 11

private theorem density (A : Finset V) : (A.dens:ℝ)=(A.card:ℝ)/2048 := by
  rw [nnratCast_dens]; norm_num [Cube]

/-- The smallest number of labels forcing an affine three-space is nineteen. -/
theorem affine_iff (k : ℕ) :
    (∀ A : Finset V,k≤A.card → ∃p,FlatAt A p) ↔ 19≤k := by
  constructor
  · intro h
    by_contra! small
    exact no_affine (h shortened (by rw [sizes.2];omega))
  · intro enough A large
    obtain ⟨B,sub,size⟩ := exists_subset_card_eq (enough.trans large)
    obtain ⟨p,h⟩ := Green51NineteenLabels.nineteen_affine B size
    exact ⟨p,Green51ElevenColumns.flat_mono sub h⟩

/-- Requiring the three-space to contain the origin raises the threshold to
twenty-five. The lower witness has the 24 extended Golay labels. -/
theorem linear_iff (k : ℕ) : (∀ A : Finset V,k≤A.card → FlatAt A 0) ↔ 25≤k := by
  constructor
  · intro h
    by_contra! small
    exact no_linear (h full (by rw [sizes.1];omega))
  · intro enough A large
    obtain ⟨B,sub,sz⟩ := exists_subset_card_eq (enough.trans large)
    apply Green51ElevenColumns.flat_mono sub
    by_contra avoid
    have pack := Green51SparseDimensions.triple_packing B (by omega) (fun h => avoid ((flat_zero B).mpr h))
    rw [sz] at pack
    exact (show ¬ (25 + Nat.choose 25 3≤Fintype.card V) from by decide +kernel) pack

/-- Green’s guarantee first reaches dimension three strictly above density
18/2048. The endpoint is witnessed by the shortened Golay columns. -/
theorem three_iff {α : ℝ} (one : α≤1) :
    3≤Green51.guaranteedMaxCosetDim 11 α ↔ 18/2048<α := by
  rw [Green51LocalFlats.guaranteed_iff (by decide) one]
  constructor
  · intro h
    by_contra! bound
    obtain ⟨B,sub,_,W,_,p,_,_,_,rank,inside⟩ := h shortened (by simpa only [density,sizes.2,Nat.cast_ofNat] using bound)
    exact no_affine ⟨p,Green51ElevenColumns.flat_mono sub ⟨W,rank,inside⟩⟩
  · intro large A hA
    have lt := large.trans_le hA
    rw [density,div_lt_div_iff_of_pos_right (by norm_num)] at lt
    have enough : 19≤A.card := by exact_mod_cast (show (18:ℝ)<A.card from lt)
    obtain ⟨p,W,d,inside⟩ := (affine_iff 19).mpr le_rfl A enough
    obtain ⟨B,L,a,sub,restricted,ambient,_,_,count,rank⟩ := Green51LocalFlats.local_labels A W p inside
    exact ⟨B,sub,L,W,a,p,d ▸ count,d ▸ rank,ambient,d,restricted⟩

/-- From the third required label through the eighteenth, the guaranteed
dimension is two. -/
theorem two_plateau {α : ℝ} (lo : 2/2048<α) (hi : α≤18/2048) :
    Green51.guaranteedMaxCosetDim 11 α=2 := by
  have upper : ¬3≤Green51.guaranteedMaxCosetDim 11 α := by
    rw [three_iff (by linarith)]
    exact not_lt.mpr hi
  have lower : 2≤Green51.guaranteedMaxCosetDim 11 α := by
    apply Green51SparseBounds.two_above_two_points (by linarith)
    convert lo using 1;norm_num
  omega

/-- From the nineteenth required label through the twenty-fourth the guaranteed
dimension is exactly three, and one admissible double avoids every linear
three-space. -/
theorem three_plateau {α : ℝ} (lo : 18/2048<α) (hi : α≤24/2048) :
    Green51.guaranteedMaxCosetDim 11 α=3 ∧
      ∃ A : Finset V, α≤(A.dens:ℝ) ∧ ¬FlatAt A 0 := by
  have adm : α≤(full.dens:ℝ) := by simpa only [density,sizes.1,Nat.cast_ofNat] using hi
  have top : Green51.guaranteedMaxCosetDim 11 α ≤ maxCosetDim F V ↑(full+full) :=
    csInf_le (OrderBot.bddBelow _) ⟨full,adm,rfl⟩
  have bound := Green51SmallWitnesses.max_dim_of_avoiding full (by decide : 2≤3)
    (fun h => no_linear ((flat_zero full).mpr h)) (by rw [sizes.1];decide)
  exact ⟨le_antisymm (top.trans bound) ((three_iff (by linarith)).mpr lo),full,adm,no_linear⟩

end Green51ElevenThresholds
#print axioms Green51ElevenThresholds.affine_iff
#print axioms Green51ElevenThresholds.linear_iff
#print axioms Green51ElevenThresholds.three_iff
#print axioms Green51ElevenThresholds.two_plateau
#print axioms Green51ElevenThresholds.three_plateau
