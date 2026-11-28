import Green51PermutedModels
import Green51PermutedInversion
import Green51WitnessIncidence
import Green51SmallWitnesses
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order
/-! # Different numbers of largest affine flats at the same ambient dimension -/

open Finset Green50Downsets Green51QuadraticFlats Green51PairedTypes Green51WitnessIncidence
open scoped Classical Pointwise
namespace Green51PermutedPairs
local notation "F" => ZMod 2
theorem packed_dimension (n:ℕ) : Module.finrank F (Packed n)=(n+1).choose 2 := by
  rw [show Module.finrank F (Packed n) = Fintype.card (PairCoordinate n) from Module.finrank_pi F]
  rw [←Fintype.card_congr (Sym2.sortEquiv (α:=Fin n)),Sym2.card,Fintype.card_fin]
theorem paired_dimension (n:ℕ) : Module.finrank F (PackedSpace n)=(n+2).choose 2 := by
  rw [show Module.finrank F (PackedSpace n)=Module.finrank F (Packed n)+Module.finrank F (V n) from Module.finrank_prod ..,
    packed_dimension]
  change _+Module.finrank F (F × Cube n)=_
  rw [Module.finrank_prod,show Module.finrank F F=1 from by simp,show Module.finrank F (Cube n)=n from by simp [Cube]]
  rw [Nat.choose_succ_succ (n+1) 1,Nat.choose_one_right]
  change (n+1).choose 2+(1+n)=(n+1)+(n+1).choose 2
  omega
variable {U T:Type*} [AddCommGroup U] [Module F U] [DecidableEq U] [AddCommGroup T] [Module F T] [DecidableEq T]
theorem copy_in_equiv (e:U ≃ₗ[F] T) (A:Finset T) : AffineCopy (A.image e.symm) A := by
  refine ⟨e.toLinearMap,0,e.injective,?_⟩
  simp [image_image,Function.comp_def]

/-- The size and the number of affine n-flats in a double avoiding linear three-spaces. -/
def WitnessWithCount {G:Type*} [AddCommGroup G] [Module F G] [DecidableEq G]
    (n cnt:ℕ) (A:Finset G) : Prop :=
  A.card=2^(n+1) ∧
    (¬∃ W:Submodule F G,Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A) ∧ (familyAt n A).ncard=cnt

private theorem witness_of_copy {A:Finset U} {B:Finset T} {n cnt:ℕ} (copy:AffineCopy A B)
    (profile:WitnessWithCount n cnt B) : WitnessWithCount n cnt A := by
  exact ⟨(copy_card copy).trans profile.1,avoids_of_copy copy profile.2.1,
    (count_copy_at n copy).symm.trans profile.2.2⟩

theorem single_flat_witness {n:ℕ} (large:4≤n) :
    ∃ f:Cube n ≃ Cube n,WitnessWithCount n 1 (labels f 0) := by
  obtain ⟨f,absent⟩:=exists_no_constant_derivative n (by omega)
  refine ⟨f,labels_card _ _,avoids_linear f f.injective _,?_⟩
  have uniq:=(unique_top_iff large f).mpr absent
  have exactSet:familyAt n (labels f 0)={distinguished n} := by
    ext D
    constructor
    · rintro ⟨P,W,rank,rfl,h⟩
      exact Set.mem_singleton_iff.mpr (uniq P W rank h)
    · intro h
      obtain rfl:=Set.mem_singleton_iff.mp h
      obtain ⟨W,P,rank,inside⟩:=vertical_flat f 0
      exact ⟨P,W,rank,(uniq P W rank inside).symm,uniq P W rank inside ▸ inside⟩
  rw [exactSet,Set.ncard_singleton]

theorem quadratic_witness {n:ℕ} (large:3≤n) : WitnessWithCount n (2^(n+1)-1) (graph (n+1)) := by
  refine ⟨?_,Green51QuadraticFlats.avoids_linear _,?_⟩
  · rw [graph,card_image_of_injective _ quad_inj]
    simp [Cube]
  · simpa only [familyAt,show ∀ r:ℕ,r+1=n+1 ↔ r=n from fun _=>by omega] using
      number_of_largest_flats (n:=n+1) (by omega)

theorem two_flat_counts (n:ℕ) (large:4≤n) :
    (∃ A:Finset (Cube ((n+2).choose 2)),WitnessWithCount n 1 A) ∧
    (∃ B:Finset (Cube ((n+2).choose 2)),WitnessWithCount n (2^(n+1)-1) B) := by
  classical
  obtain ⟨f,one⟩:=single_flat_witness large
  let e : Cube ((n+2).choose 2) ≃ₗ[F] PackedSpace n := LinearEquiv.ofFinrankEq _ _ (by
    rw [paired_dimension];simp [Cube])
  let j : Cube ((n+2).choose 2) ≃ₗ[F] Packed (n+1) := LinearEquiv.ofFinrankEq _ _ (by
    rw [packed_dimension];simp [Cube,Nat.add_assoc])
  exact ⟨⟨_,witness_of_copy (copy_in_equiv e _) (witness_of_copy (paired_copy f 0) one)⟩,
    ⟨_,witness_of_copy (copy_in_equiv j _) (witness_of_copy (quadratic_copy (n+1)) (quadratic_witness (by omega)))⟩⟩

theorem fifteen_dimensional_witnesses :
    (∃ A:Finset (Cube 15),WitnessWithCount 4 1 A) ∧ (∃ B:Finset (Cube 15),WitnessWithCount 4 31 B) :=
  two_flat_counts 4 (by decide)

theorem max_coset_dimension {N d cnt:ℕ} (A:Finset (Cube N)) (large:2≤d) (pos:0<cnt)
    (h:WitnessWithCount d cnt A) : maxCosetDim F (Cube N) ↑(A+A)=d := by
  apply le_antisymm
  · apply Green51SmallWitnesses.max_dim_of_avoiding A large h.2.1
    rw [h.1]
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr (by omega)
  · have non : (familyAt d A).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (h.2.2.symm ▸ pos)
    obtain ⟨_,p,W,rank,rfl,inside⟩:=non
    apply le_csSup
    · refine ⟨Module.finrank F (Cube N),?_⟩
      rintro _ ⟨S,_,rfl⟩;exact Submodule.finrank_le _
    · refine ⟨AffineSubspace.mk' p W,?_,by rwa [AffineSubspace.direction_mk']⟩
      intro z hz
      refine inside ⟨z-p,AffineSubspace.mem_mk'.mp hz,?_⟩
      change p+(z-p)=z
      abel

end Green51PermutedPairs

#print axioms Green51PermutedPairs.max_coset_dimension
#print axioms Green51PermutedPairs.two_flat_counts
#print axioms Green51PermutedPairs.fifteen_dimensional_witnesses
