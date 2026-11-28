import Erdos722AffineCompletion
import Erdos722ExtremalParameters

/-!
# Deleting a projective line

Deleting an arbitrary line and all its incident points gives the converse
to completion at square order. Taking links gives a necessary plane at
every rank on the same square boundary.
-/

namespace Erdos722.InversiveOrder
open Finset Configuration Quartet MinimumOrder
open scoped Classical
noncomputable section

/-- The complement of any line of a finite plane of order q carries
a canonical Steiner pair design of order q² and block size q. -/
theorem delete_projective_line {P L : Type} [Membership P L] [Fintype P] [Fintype L]
    [pp : ProjectivePlane P L] (l₀ : L) {q : ℕ} (h : pp.order=q) :
    ∃ H : Finset (Finset (Fin (q^2))), H.IsBlockDesign 2 q := by
  classical
  let X := {p : P // p∉l₀}
  let I := {l : L // l≠l₀}
  let line (i : I) := (univ : Finset X).filter fun x => x.val∈i.val
  have count (l : L) : Fintype.card {p : P // p∈l}=q+1 := by
    simpa [pointCount,Nat.card_eq_fintype_card,h] using ProjectivePlane.pointCount_eq P l
  have hs : Fintype.card X=q^2 := by
    change Fintype.card {p : P // ¬p∈l₀}=_
    rw [Fintype.card_subtype_compl,ProjectivePlane.card_points P L,count,h]
    omega
  have block (i : I) : (line i).card=q := by
    obtain ⟨z,hz,hu⟩ := HasPoints.existsUnique_point P L i.val l₀ i.property
    let U := (univ : Finset P).filter (·∈i.val)
    have hzU : z∈U := by simpa [U] using hz.1
    have hc : U.card=q+1 := by
      rw [← Fintype.card_of_subtype U (p:=fun p => p∈i.val) (by simp [U]),count]
    calc
      _ = (U.erase z).card := by
        apply card_bij (fun x _ => x.val)
        · intro x hx
          exact mem_erase.mpr ⟨fun e => x.property (e ▸ hz.2),
            by simpa [line,U] using hx⟩
        · exact fun _ _ _ _ e => Subtype.ext e
        · intro y hy
          obtain ⟨hyz,hyU⟩ := mem_erase.mp hy
          have hyi : y∈i.val := by simpa [U] using hyU
          let x : X := ⟨y,fun hy₀ => hyz (hu y ⟨hyi,hy₀⟩)⟩
          exact ⟨x,by simpa [line,x] using hyi,rfl⟩
      _ = q := by rw [card_erase_of_mem hzU,hc]; omega
  let C : Cover X (AllPairs _) (·=q) := Cover.ofLines line block
    (fun _ _ _ _ _ _ => trivial) (by
      intro x y hxy _
      obtain ⟨l,hl,hu⟩ := HasLines.existsUnique_line P L x.val y.val (fun e => hxy (Subtype.ext e))
      let i : I := ⟨l,fun e => x.property (e ▸ hl.1)⟩
      exact ⟨i,by simpa [line,i] using hl,fun j hj => Subtype.ext (hu j.val (by simpa [line] using hj))⟩)
  exact (C.has hs).some.design

theorem affine_design_iff_plane {q : ℕ} (hq : 2≤q) :
    (∃ H : Finset (Finset (Fin (q^2))), H.IsBlockDesign 2 q) ↔ PlaneOfOrder q := by
  constructor
  · rintro ⟨H,hH⟩
    exact projective_plane_of_affine_design hq hH
  · rintro ⟨P,L,m,f,g,pp,h⟩
    obtain ⟨_,_,_,l,_⟩ := @ProjectivePlane.exists_config P L m pp
    exact delete_projective_line l h

/-- Deriving s times from S(2+s,q+s,q²+s) gives an affine pair
design. Completion gives a projective plane of order q. -/
theorem plane_of_square_design {q : ℕ} (hq : 2≤q) (s : ℕ)
    {H : Finset (Finset (Fin (q^2+s)))} (hH : H.IsBlockDesign (2+s) (q+s)) :
    PlaneOfOrder q := by
  induction s with
  | zero => exact projective_plane_of_affine_design hq hH
  | succ s ih =>
    obtain ⟨G,hG⟩ := Cyclotomy.derive_design (n:=q^2+s) (r:=2+s) (k:=q+s) hH
    exact ih hG

#print axioms delete_projective_line
#print axioms affine_design_iff_plane
#print axioms plane_of_square_design
end
end Erdos722.InversiveOrder
