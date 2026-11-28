import Erdos722SharpFourFibreAutomorphisms

/-! # Rooted affine bases and simultaneous colour centralizers -/

namespace Erdos722.FourPoint
open Finset Equiv
open scoped Classical
noncomputable section
local instance : Fintype Colour := fintypePerm
local instance (d : ℕ) : Fintype (Perm (Cube d)) := fintypePerm

def rootedBases (d : ℕ) := (univ : Finset (Perm (Cube d))).filter fun b =>
  b 0=0 ∧ ∀ x y z,b (x+y+z)=b x+b y+b z

theorem mem_rootedBases (d : ℕ) (b : Perm (Cube d)) : b∈rootedBases d ↔
    b 0=0 ∧ ∀ x y z,b (x+y+z)=b x+b y+b z := by simp [rootedBases]

theorem rooted_bases_card (d : ℕ) : (rootedBases d).card≤(2^d)^d := by
  let B := Pi.basisFun (ZMod 2) (Fin d)
  let L (b : rootedBases d) : Cube d →ₗ[ZMod 2] Cube d :=
    let h := (mem_filter.mp b.prop).2
    let f : Cube d →+ Cube d :=
      { toFun := b.val
        map_zero' := h.1
        map_add' := fun x y => by simpa only [add_zero,h.1] using h.2 x y 0 }
    f.toZModLinearMap 2
  let eval (b : rootedBases d) (i : Fin d) := b.val (B i)
  have inj : Function.Injective eval := by
    intro b c eq
    have same : L b=L c := B.ext fun i => congrFun eq i
    exact Subtype.ext (Equiv.ext fun x => DFunLike.congr_fun same x)
  have h := Fintype.card_le_of_injective eval inj
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin,Cube,ZMod.card] using h

def commutingColours (s : Colour) := univ.filter fun z : Colour => s*z=z*s

private theorem centralizers_small : ∀ s : Colour, s≠1 → (commutingColours s).card≤3 := by decide +kernel

/-- Each nonidentity global fibre colour allows at most three of the six
letters on every edge. -/
theorem colour_frame_bound {I : Type*} [LinearOrder I] [Fintype I] (o : I)
    (s : Colour) (hne : s≠1) :
    ((univ : Finset (edges o → Colour)).filter fun w => Frame (edgeMatching o w) (edgeMatching o w) 1 s).card ≤
      3^((Fintype.card I-1).choose 2) := by
  let T := (univ : Finset (edges o → Colour)).filter fun w => Frame (edgeMatching o w) (edgeMatching o w) 1 s
  let f (w : T) (e : edges o) : commutingColours s :=
    ⟨w.val e,mem_filter.mpr ⟨mem_univ _,by
      have h := (mem_filter.mp w.prop).2 e.val.1 e.val.2
      simpa only [Perm.one_apply,edge_forward] using h⟩⟩
  have inj : Function.Injective f := fun _ _ h => Subtype.ext (funext fun e => congrArg Subtype.val (congrFun h e))
  have h := Fintype.card_le_of_injective f inj
  rw [Fintype.card_coe,Fintype.card_fun,Fintype.card_coe,Fintype.card_coe,edges_card] at h
  exact h.trans (Nat.pow_le_pow_left (centralizers_small s hne) _)

/-- Fixing a direction in the three-letter action forces a nonidentity
common centralizer. -/
theorem fixed_direction_frame {I : Type*} [LinearOrder I] [Fintype I] (o : I) (w : edges o → Colour)
    (d : Direction) (h : ∀ e,w e d=d) :
    ∃ s : Colour,s≠1 ∧ Frame (edgeMatching o w) (edgeMatching o w) 1 s := by
  have finite : ∀ i : Direction,∃ s : Colour,s≠1 ∧ ∀ z : Colour,z i=i → s*z=z*s := by decide +kernel
  obtain ⟨s,hs,comm⟩ := finite d
  refine ⟨s,hs,fun i j => ?_⟩
  apply comm
  have fv := (invariant_iff_edges o w (some d)).mpr (fun e => congrArg some (h e))
  exact Option.some.inj (fv i j)

#print axioms rootedBases
#print axioms mem_rootedBases
#print axioms rooted_bases_card
#print axioms commutingColours
#print axioms colour_frame_bound
#print axioms fixed_direction_frame
end
end Erdos722.FourPoint
