import Erdos722QuadSwitchClassification

/-!
# Recovering and counting the base systems

The four-point projections of a doubling recover its original system. Counting
all projection-compatible systems therefore multiplies the number of labelled
bases by the exact size of a parity cube, without counting any lift twice.
-/

namespace Erdos722.QuadSwitch
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Each triple occurs in one base block, and each block has four triples. -/
theorem triple_incidence_count {H : Finset (Finset V)} (hH : H.IsBlockDesign 3 4) :
    H.card * 4 = (Fintype.card V).choose 3 := by
  classical
  have union : H.biUnion (fun B => B.powersetCard 3) = (univ : Finset V).powersetCard 3 := by
    ext T
    constructor
    · intro ht
      obtain ⟨B,_,h⟩ := mem_biUnion.mp ht
      exact mem_powersetCard.mpr ⟨subset_univ _,(mem_powersetCard.mp h).2⟩
    · intro ht
      obtain ⟨B,⟨hb,hsub⟩,_⟩ := hH.2 T (mem_powersetCard.mp ht).2
      exact mem_biUnion.mpr ⟨B,hb,mem_powersetCard.mpr ⟨hsub,(mem_powersetCard.mp ht).2⟩⟩
  have dj : (H : Set (Finset V)).PairwiseDisjoint (fun B => B.powersetCard 3) := by
    intro B hb C hc ne
    apply disjoint_left.mpr
    intro T h₁ h₂
    have u := hH.2 T (mem_powersetCard.mp h₁).2
    exact ne (u.unique ⟨hb,(mem_powersetCard.mp h₁).1⟩ ⟨hc,(mem_powersetCard.mp h₂).1⟩)
  have eq := congrArg Finset.card union
  rw [card_biUnion dj,card_powersetCard,card_univ] at eq
  have terms (B) (hB : B ∈ H) : (B.powersetCard 3).card = 4 := by
    rw [card_powersetCard,hH.1 B hB]
    decide
  rw [sum_congr rfl terms,sum_const,nsmul_eq_mul] at eq
  simpa using eq

theorem base_block_count {H : Finset (Finset V)} (hH : H.IsBlockDesign 3 4) :
    H.card = (Fintype.card V).choose 3 / 4 := by
  rw [← triple_incidence_count hH]
  simp

def recoveredBase (D : Finset (Finset (V × Bool))) := (D.image footprint).filter (fun B => B.card = 4)

theorem recover_doubling {H : Finset (Finset V)} (hH : H.IsBlockDesign 3 4) (bits : H → Bool) :
    recoveredBase (doubling hH bits) = H := by
  ext B
  constructor
  · intro h
    obtain ⟨hm,hc⟩ := mem_filter.mp h
    obtain ⟨S,hs,rfl⟩ := mem_image.mp hm
    rcases (mem_doubling hH bits S).mp hs with ⟨P,hp,rfl⟩ | ⟨i,hi⟩
    · rw [footprint_twins,hp] at hc
      contradiction
    · rw [(component_shape hH i hi).2]
      exact i.property
  · intro hB
    let i : H := ⟨B,hB⟩
    obtain ⟨S,hs⟩ := card_pos.mp (show 0 < (component hH i (bits i)).card by
      rw [component,tile_card]; decide)
    exact mem_filter.mpr ⟨mem_image.mpr ⟨S,(mem_doubling hH bits S).mpr (.inr ⟨i,hs⟩),
      (component_shape hH i hs).2⟩,hH.1 B hB⟩

abbrev Systems (V : Type*) := {H : Finset (Finset V) // H.IsBlockDesign 3 4}

abbrev LiftData (V : Type*) := (H : Systems V) × (H.val → Bool)

abbrev CompatibleSystems (V : Type*) [DecidableEq V] := {D : Systems (V × Bool) //
  ∃ H : Systems V, Compatible H.val D.val}

/-- Bijection simultaneously recovers the base and every local parity bit. -/
noncomputable def allLifts : LiftData V ≃ CompatibleSystems V := by
  let F : LiftData V → CompatibleSystems V := fun ⟨H,f⟩ =>
    ⟨⟨doubling H.property f,doubling_design H.property f⟩,H,doubling_compatible H.property f⟩
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨H,f⟩ ⟨G,g⟩ h
    have eq : doubling H.property f = doubling G.property g := congrArg (fun x : CompatibleSystems V => x.val.val) h
    have base : H = G := Subtype.ext (((recover_doubling H.property f).symm.trans (congrArg recoveredBase eq)).trans
      (recover_doubling G.property g))
    subst G
    rw [doubling_injective H.property eq]
  · rintro ⟨D,⟨H,compat⟩⟩
    obtain ⟨f,hf,_⟩ := (classification H.property D.val).mp ⟨D.property,compat⟩
    exact ⟨⟨H,f⟩,Subtype.ext (Subtype.ext hf.symm)⟩

/-- Count all compatible labelled doubles over a fixed projection onto V. -/
theorem all_lifts_count : Nat.card (CompatibleSystems V) =
    Nat.card (Systems V) * 2^((Fintype.card V).choose 3 / 4) := by
  classical
  rw [← Nat.card_congr (allLifts (V:=V))]
  simp only [Nat.card_eq_fintype_card,LiftData,Fintype.card_sigma,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_coe]
  rw [sum_congr rfl (g:=fun _ => 2^((Fintype.card V).choose 3 / 4))
    (fun H _ => congrArg (2^·) (base_block_count H.property)),sum_const]
  simp

#print axioms base_block_count
#print axioms recover_doubling
#print axioms allLifts
#print axioms all_lifts_count
end Erdos722.QuadSwitch
