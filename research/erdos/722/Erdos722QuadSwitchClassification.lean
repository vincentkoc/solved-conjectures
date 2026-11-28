import Erdos722QuadSwitchRigidity

/-!
# All compatible labelled lifts of a fixed quadruple system

The complete fibre pairs are forced by triples with two projected points.
Over each original block, minimum trade distance leaves exactly two choices.
-/

namespace Erdos722.QuadSwitch
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V] {H : Finset (Finset V)}

theorem doubling_compatible (hH : H.IsBlockDesign 3 4) (bits : H → Bool) :
    Compatible H (doubling hH bits) := by
  intro D hD
  rcases (mem_doubling hH bits D).mp hD with h | ⟨i,hi⟩
  · exact .inl h
  · exact .inr ((component_shape hH i hi).2.symm ▸ i.property)

omit [Fintype V] in
theorem forced_twins (hH : H.IsBlockDesign 3 4) {D : Finset (Finset (V × Bool))}
    (hD : D.IsBlockDesign 3 4) (compat : Compatible H D) (P : Finset V) (hp : P.card = 2) :
    twins P ∈ D := by
  have hc : (twins P).card = 4 := by rw [twins_card,hp]
  obtain ⟨T,htp,ht⟩ := exists_subset_card_eq (show 3 ≤ (twins P).card by omega)
  have small := card_le_card ((subset_twins T P).mp htp)
  have hself := card_le_card ((subset_twins T (footprint T)).mpr Subset.rfl)
  rw [twins_card,ht] at hself
  have hpT : footprint T = P := eq_of_subset_of_card_le ((subset_twins T P).mp htp) (by omega)
  obtain ⟨B,⟨hb,hs⟩,_⟩ := hD.2 T ht
  rcases compat B hb with ⟨Q,hq,rfl⟩ | hbH
  · have hsub := (subset_twins T Q).mp hs
    rw [hpT] at hsub
    exact (eq_of_subset_of_card_le hsub (by omega)).symm ▸ hb
  · have inj : Set.InjOn Prod.fst (B : Set (V × Bool)) :=
      injOn_of_card_image_eq ((hH.1 _ hbH).trans (hD.1 B hb).symm)
    have eq := card_image_of_injOn (inj.mono (show (T : Set (V × Bool)) ⊆ B from hs))
    change (footprint T).card = T.card at eq
    rw [hpT,hp,ht] at eq
    contradiction

/-- The unique parity vector classifies every projection-compatible ordinary lift. -/
theorem classification (hH : H.IsBlockDesign 3 4) (D : Finset (Finset (V × Bool))) :
    D.IsBlockDesign 3 4 ∧ Compatible H D ↔ ∃! bits : H → Bool, D = doubling hH bits := by
  classical
  constructor
  · rintro ⟨hD,compat⟩
    choose bits shapes using fun i : H => component_rigidity hH i hD compat
    have eq : D = doubling hH bits := by
      ext B
      constructor
      · intro hB
        apply (mem_doubling hH bits B).mpr
        rcases compat B hB with hp | hb
        · exact .inl hp
        · let i : H := ⟨footprint B,hb⟩
          exact .inr ⟨i,shapes i ▸ mem_filter.mpr ⟨hB,rfl⟩⟩
      · intro hB
        rcases (mem_doubling hH bits B).mp hB with ⟨P,hp,rfl⟩ | ⟨i,hi⟩
        · exact forced_twins hH hD compat P hp
        · exact (mem_filter.mp (show B ∈ overBlock D i.val from (shapes i).symm ▸ hi)).1
    exact ⟨bits,eq,fun f hf => doubling_injective hH (hf.symm.trans eq)⟩
  · rintro ⟨bits,rfl,_⟩
    exact ⟨doubling_design hH bits,doubling_compatible hH bits⟩

/-- Exact labelled count for a given base and a specified projection onto it. -/
theorem compatible_count (hH : H.IsBlockDesign 3 4) :
    Nat.card {D : Finset (Finset (V × Bool)) // D.IsBlockDesign 3 4 ∧ Compatible H D} = 2^H.card := by
  classical
  let target := {D : Finset (Finset (V × Bool)) // D.IsBlockDesign 3 4 ∧ Compatible H D}
  let F : (H → Bool) → target := fun f => ⟨doubling hH f,doubling_design hH f,doubling_compatible hH f⟩
  have bij : Function.Bijective F := by
    refine ⟨fun a b e => doubling_injective hH (congrArg Subtype.val e),?_⟩
    intro D
    obtain ⟨f,hf,_⟩ := (classification hH D.val).mp D.property
    exact ⟨f,Subtype.ext hf.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective F bij)]
  simp [Nat.card_eq_fintype_card]

#print axioms forced_twins
#print axioms classification
#print axioms compatible_count
end Erdos722.QuadSwitch
