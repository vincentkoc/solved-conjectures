import Erdos722ProjectiveSublines
import Mathlib.Tactic

/-!
# Deriving an affine pair design from a projective subline design

Keep the blocks through a fixed point and delete that point. The subline
designs then give block size a prime power and order any positive power
of that block size.
-/

namespace Erdos722.Cyclotomy
open Finset

/-- Deriving at the final vertex removes one point from each incident block. -/
theorem derive_design {n r k : ℕ} {H : Finset (Finset (Fin (n+1)))}
    (hH : H.IsBlockDesign (r+1) (k+1)) :
    ∃ G : Finset (Finset (Fin n)), G.IsBlockDesign r k := by
  classical
  let e : Fin n ↪ Fin (n+1) := Fin.castSuccEmb
  let lift (B : Finset (Fin n)) := insert (Fin.last n) (B.map e)
  have fresh (B : Finset (Fin n)) : Fin.last n ∉ B.map e := by
    rintro h
    obtain ⟨i,_,hi⟩ := mem_map.mp h
    exact Fin.castSucc_ne_last i hi
  have size (B : Finset (Fin n)) : (lift B).card=B.card+1 := by
    dsimp only [lift]
    rw [card_insert_of_notMem (fresh _),card_map]
  have subset (A B : Finset (Fin n)) : lift A ⊆ lift B ↔ A ⊆ B := by
    constructor
    · intro h x hx
      have he := h (mem_insert_of_mem (mem_map_of_mem e hx))
      rcases mem_insert.mp he with he|he
      · exact (Fin.castSucc_ne_last x he).elim
      · exact (mem_map' e).mp he
    · intro h; exact Finset.insert_subset_insert _ (map_subset_map.mpr h)
  let G := univ.filter fun B => lift B ∈ H
  refine ⟨G,?_,?_⟩
  · intro B hB
    have hh := hH.1 _ (mem_filter.mp hB).2
    rw [size] at hh
    omega
  · intro A hA
    obtain ⟨W,⟨hW,hAW⟩,huniq⟩ := hH.2 (lift A) (by rw [size,hA])
    let B := univ.filter fun i : Fin n => e i ∈ W
    have eq : lift B=W := by
      ext x
      refine Fin.lastCases ?_ (fun i => ?_) x
      · have hlast := hAW (mem_insert_self ..)
        simp [lift,hlast]
      · change e i ∈ insert (Fin.last n) (B.map e) ↔ e i ∈ W
        simp only [mem_insert,show e i ≠ Fin.last n from Fin.castSucc_ne_last _,false_or,mem_map',B,mem_filter,mem_univ,true_and]
    refine ⟨B,⟨mem_filter.mpr ⟨mem_univ _,eq ▸ hW⟩,(subset A B).mp (eq ▸ hAW)⟩,?_⟩
    intro C hC
    have hc := huniq (lift C) ⟨(mem_filter.mp hC.1).2,(subset _ _).mpr hC.2⟩
    have he := hc.trans eq.symm
    exact (subset _ _).mp he.le |>.antisymm ((subset _ _).mp he.ge)

theorem affine_power_design (p a d : ℕ) [Fact p.Prime] (ha : 0<a) (hd : 0<d) :
    ∃ H : Finset (Finset (Fin ((p^a)^d))), H.IsBlockDesign 2 (p^a) :=
  (Sublines.exists_prime_power_subline_design p a d ha hd).elim (fun _ h => derive_design h)

#print axioms derive_design
#print axioms affine_power_design

end Erdos722.Cyclotomy
