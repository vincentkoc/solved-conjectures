import ThetaUnitExposure

/-! Refining a reduced class can preserve or increase any prescribed signed mean. -/
namespace Arxiv.«2501.03234».ThetaRefinedSignedMean
open Finset ThetaFiniteExposure ThetaUnitExposure ThetaConditionalRows ThetaIdentityFiber
noncomputable section

theorem project {P m : ℕ} [NeZero P] [NeZero m] (h : m∣P) (f : ℕ → ℝ) (x : (ZMod P)ˣ) :
    proj (key m) (fun u : (ZMod P)ˣ => f (u:ZMod P).val) x =
    m.totient*unitMean P (fun n => selectClass (key m x) m n*f n) := by
  unfold proj avg unitMean
  rw [class_sum]
  have H := card_ratio h x
  have hm : 0<(m.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos _))
  have hP : 0<(P.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos _))
  have hc : 0<((fiber (key (P:=P) m) (key m x)).card:ℝ) :=
    Nat.cast_pos.mpr (card_pos.mpr (fiber_nonempty _ x))
  field_simp at H ⊢
  linear_combination -(∑ u : (ZMod P)ˣ,selectClass (key m x) m (u:ZMod P).val*f (u:ZMod P).val)*H

theorem best {P m l r : ℕ} [NeZero P] [NeZero m] [NeZero l] (hml : m∣l) (hl : l∣P)
    (hr : r < m) (hc : r.Coprime m) (f : ℕ → ℝ) :
    ∃ b < l,b.Coprime l ∧ b%m=r ∧
      m.totient*unitMean P (fun n => selectClass r m n*f n) ≤
      l.totient*unitMean P (fun n => selectClass b l n*f n) := by
  classical
  have hm := hml.trans hl
  obtain ⟨x,hx⟩ := ZMod.unitsMap_surjective hm (ZMod.unitOfCoprime r hc)
  have hx' : key m x=r := by
    have h := congrArg (fun u : (ZMod m)ˣ => (u:ZMod m).val) hx
    rw [ZMod.unitsMap_val,← ZMod.natCast_zmod_val (x:ZMod P),ZMod.cast_natCast hm,
      ZMod.val_natCast,ZMod.coe_unitOfCoprime,ZMod.val_natCast,
      Nat.mod_eq_of_lt hr] at h
    exact h
  let k := key (P:=P) m
  let j := key (P:=P) l
  let g (y : (ZMod P)ˣ) := f (y:ZMod P).val
  let A := fiber k (k x)
  have hA : A.Nonempty := fiber_nonempty _ _
  have hpos := Nat.cast_pos (α:=ℝ).mpr (card_pos.mpr hA)
  have he := tower k j g (refine hml) x
  change (∑ y∈A,proj j g y)/(A.card:ℝ)=proj k g x at he
  have hsum : ∑ _y∈A,proj k g x ≤ ∑ y∈A,proj j g y := by
    rw [div_eq_iff hpos.ne'] at he
    rw [sum_const,nsmul_eq_mul];linarith only [he]
  obtain ⟨y,hy,hle⟩ := exists_le_of_sum_le hA hsum
  have hky : key m y=key m x := (mem_filter.mp hy).2
  refine ⟨key l y,Nat.mod_lt _ (NeZero.pos _),key_unit hl y,?_,?_⟩
  · change (y:ZMod P).val%l%m=r;rw [Nat.mod_mod_of_dvd _ hml];exact hky.trans hx'
  · change proj (key m) (fun u : (ZMod P)ˣ => f (u:ZMod P).val) x ≤
      proj (key l) (fun u : (ZMod P)ˣ => f (u:ZMod P).val) y at hle
    simpa only [project hm,project hl,hx'] using hle

#print axioms best
end
end Arxiv.«2501.03234».ThetaRefinedSignedMean
