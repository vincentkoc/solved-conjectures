import ThetaSmoothFiltration
import ThetaFiniteExposure

/-! The finite exposure projections are the arithmetic conditional row means. -/
namespace Arxiv.«2501.03234».ThetaUnitExposure
open Finset Real ThetaConditionalRows ThetaIdentityFiber ThetaSmoothConditionalModel ThetaFiniteExposure
open ThetaSmoothFiltration ThetaPrimeTailTransfer
noncomputable section

def key {P : ℕ} [NeZero P] (m : ℕ) (x : (ZMod P)ˣ) := (x:ZMod P).val%m

theorem key_unit {P m : ℕ} [NeZero P] (h : m∣P) (x : (ZMod P)ˣ) : (key m x).Coprime m := by
  have hc := (ZMod.val_coe_unit_coprime x).coprime_dvd_right h
  change Nat.gcd ((x:ZMod P).val % m) m=1
  rw [← Nat.gcd_rec]
  exact hc.symm

theorem refine {P m n : ℕ} [NeZero P] (h : m∣n) (x y : (ZMod P)ˣ)
    (he : key n x=key n y) : key m x=key m y := by
  simpa only [key,Nat.mod_mod_of_dvd _ h] using congrArg (·%m) he

theorem class_sum {P : ℕ} [NeZero P] (r m : ℕ) (f : ℕ → ℝ) :
    ∑ x∈fiber (key (P:=P) m) r,f (x:ZMod P).val =
      ∑ x : (ZMod P)ˣ,selectClass r m (x:ZMod P).val*f (x:ZMod P).val := by
  classical
  unfold fiber
  rw [Finset.sum_filter]
  apply sum_congr rfl
  intro u _
  by_cases hu : (u:ZMod P).val%m=r <;> simp [key,selectClass,hu]

theorem unit_class {m r : ℕ} [NeZero m] (hr : r < m) (hc : r.Coprime m) :
    unitMean m (selectClass r m)=1/(m.totient:ℝ) := by
  unfold unitMean
  congr 1
  rw [ThetaReciprocalFibers.unit_sum_nat]
  rw [sum_eq_single r]
  · simp [selectClass,Nat.mod_eq_of_lt hr]
  · intro j hj hn
    simp [selectClass,Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hj).1),hn]
  · simp [hr,hc]

theorem card_ratio {P m : ℕ} [NeZero P] [NeZero m] (h : m∣P) (x : (ZMod P)ˣ) :
    ((fiber (key (P:=P) m) (key m x)).card:ℝ)/(P.totient:ℝ)=1/m.totient := by
  have H := (unitMean_lift h (selectClass_mod (key m x) m)).trans
    (unit_class (Nat.mod_lt _ (NeZero.pos m)) (key_unit h x))
  have hs := class_sum (P:=P) (key m x) m (fun _ => 1)
  simpa only [unitMean,show (∑ u : (ZMod P)ˣ,selectClass (key m x) m (u:ZMod P).val)=
      ((fiber (key (P:=P) m) (key m x)).card:ℝ) by simpa using hs.symm] using H

theorem project {Y m : ℕ} [NeZero Y.factorial] [NeZero m] (h : m∣Y.factorial) (V : ℕ)
    (x : (ZMod Y.factorial)ˣ) :
    proj (key m) (fun u : (ZMod Y.factorial)ˣ => model Y V (u:ZMod Y.factorial).val) x =
      ThetaSmoothConditionalModel.cond m (key m x) Y V := by
  unfold proj avg ThetaSmoothConditionalModel.cond unitMean
  rw [class_sum]
  have H := card_ratio h x
  have hm : 0<(m.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos _))
  have hP : 0<(Y.factorial.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.factorial_pos _))
  have hc : 0<((fiber (key (P:=Y.factorial) m) (key m x)).card:ℝ) := by
    exact Nat.cast_pos.mpr (card_pos.mpr ⟨x,by simp [fiber]⟩)
  field_simp at H ⊢
  linear_combination -(∑ u : (ZMod Y.factorial)ˣ,selectClass (key m x) m (u:ZMod Y.factorial).val*
    model Y V (u:ZMod Y.factorial).val)*H

theorem final_project {P : ℕ} [NeZero P] (f : (ZMod P)ˣ → ℝ) (x : (ZMod P)ˣ) :
    proj (key P) f x=f x := by
  classical
  have hi : Function.Injective (key (P:=P) P) := by
    intro u v he
    apply Units.ext
    apply ZMod.val_injective
    simpa [key,Nat.mod_eq_of_lt (ZMod.val_lt _)] using he
  have hh : fiber (key (P:=P) P) (key P x)={x} := by ext u; simp [fiber,hi.eq_iff]
  simp [proj,hh,avg]

#print axioms project
#print axioms final_project
end
end Arxiv.«2501.03234».ThetaUnitExposure
