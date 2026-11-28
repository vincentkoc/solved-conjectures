import Erdos722RootedWordAction
import Erdos722RankClassQuotient

/-! # Unrestricted point isomorphisms between typical four-fibre systems -/

namespace Erdos722.FourPoint
open Finset Equiv QuadCompletion QuadSwitch
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

theorem rooted_action_frame {d : ℕ} (g : RootFrames d) (w : EdgeWord d) :
    Frame (edgeMatching 0 w) (edgeMatching 0 (g • w)) g.1.toEquiv g.2 :=
  (frame_iff_recode g w _).mpr rfl

theorem typical_iff_free {d : ℕ} (w : EdgeWord d) : Typical d w ↔
    (∀ x,Normalized (edgeMatching 0 w) x → x=0) ∧ (∀ g : RootFrames d,g • w=w → g=1) := by
  refine ⟨fun h => ⟨h.1,?_⟩,fun h => ⟨h.1,?_⟩⟩
  · intro g hg
    obtain ⟨b,s⟩ := h.2 _ (linear_rooted g.1) g.2 ((frame_iff_recode g w w).mpr hg)
    exact Prod.ext (LinearEquiv.ext fun x => DFunLike.congr_fun b x) s
  · intro b hb s hf
    obtain ⟨L,rfl⟩ := rooted_linear hb
    have fix := (frame_iff_recode (L,s) w w).mp hf
    have eq := h.2 (L,s) fix
    exact ⟨congrArg (fun g : RootFrames d => g.1.toEquiv) eq,congrArg Prod.snd eq⟩

theorem typical_smul {d : ℕ} {w : EdgeWord d} (hw : Typical d w) (g : RootFrames d) :
    Typical d (g • w) := by
  apply (typical_iff_free _).mpr
  constructor
  · intro x hx
    have fr := rooted_action_frame g⁻¹ (g • w)
    rw [inv_smul_smul] at fr
    have zero := hw.1 _ (carries_star fr hx)
    change g.1.symm x=0 at zero
    simpa using congrArg g.1 zero
  · intro k hk
    have f : (g⁻¹*k*g) • w=w := by rw [mul_smul,mul_smul,hk,inv_smul_smul]
    have eq := ((typical_iff_free w).mp hw).2 _ f
    calc
      k=g*(g⁻¹*k*g)*g⁻¹ := by group
      _=1 := by rw [eq]; group

def splitClass (d : ℕ) (w : EdgeWord d) := classOf (splitFamily d w)

theorem action_class {d : ℕ} (g : RootFrames d) (w : EdgeWord d) :
    splitClass d w=splitClass d (g • w) := by
  apply class_eq_iff.mpr
  apply (relabel_iso_iff (fourLabels d)).mpr
  refine ⟨pointForm g.1.toEquiv g.2 (fun _ => 0),form_preserves (Q:=cubeRule d) (R:=cubeRule d)
    (fun i j k => ?_) (rooted_action_frame g w) (fun _ _ _ => by simp)⟩
  exact ((mem_rootedBases d _).mp (linear_rooted g.1)).2 i j k

/-- Equality in the quotient by all permutations of the actual point set
is equivalent, on typical systems, to the rooted action on matching words. -/
theorem typical_class_iff {d : ℕ} (hd : 2≤d) {w v : EdgeWord d} (hw : Typical d w) (hv : Typical d v) :
    splitClass d w=splitClass d v ↔ ∃ g : RootFrames d,g • w=v := by
  refine ⟨?_,?_⟩
  · intro he
    obtain ⟨e,h⟩ := (relabel_iso_iff (fourLabels d)).mp (class_eq_iff.mp he)
    have hyp (u : EdgeWord d) (hu : Typical d u) : FibreHypotheses (cubeRule d) (edgeMatching 0 u) :=
      ⟨cube_separates d,⟨0,edge_normalized 0 u⟩,(noFix_edge_iff ..).mpr (typical_top hu)⟩
    have hn : 2^2≤2^d := Nat.pow_le_pow_right (by decide) hd
    have hc : 3≤Fintype.card (Cube d) := by simpa [Cube] using (show 3≤2^d by omega)
    obtain ⟨b,s,_,base,frame,_,_⟩ := (four_fibre_iso_iff (hyp _ hw) (hyp _ hv) hc e).mp h
    have zero := hv.1 _ (carries_star frame (edge_normalized 0 w))
    obtain ⟨L,rfl⟩ := rooted_linear ((mem_rootedBases d b).mpr ⟨zero,base⟩)
    exact ⟨(L,s),(frame_iff_recode (L,s) w v).mp frame⟩
  · rintro ⟨g,rfl⟩; exact action_class g w

#print axioms rooted_action_frame
#print axioms typical_iff_free
#print axioms typical_smul
#print axioms splitClass
#print axioms action_class
#print axioms typical_class_iff
end
end Erdos722.FourPoint
