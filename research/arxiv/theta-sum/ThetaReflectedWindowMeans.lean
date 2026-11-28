import ThetaCompactModels
import ThetaRowReflection

/-! Exact reflection of signed finite-window means on opposite unit classes. -/
namespace Arxiv.«2501.03234».ThetaReflectedWindowMeans
open Finset Filter ThetaPrimeTailTransfer ThetaConditionalRows ThetaIdentityFiber ThetaReciprocalFibers
open ThetaRowCorrelations ThetaCotangentTriangle ThetaCompactModulus
noncomputable section

private theorem cast_neg {m P : ℕ} [NeZero P] (h : m∣P) (u : (ZMod P)ˣ) :
    ((((-u:(ZMod P)ˣ):ZMod P).val:ℕ):ZMod m)= -(((u:ZMod P).val:ℕ):ZMod m) := by
  have H : ((((-u:(ZMod P)ˣ):ZMod P).val:ℕ):ZMod P)= -(((u:ZMod P).val:ℕ):ZMod P) := by simp
  simpa only [map_natCast,map_neg] using congrArg (ZMod.castHom h (ZMod m)) H

/-- All numerator cutoffs and weights of the prime model commute with the
negation involution on the selected classes. -/
theorem reflection {m Y b b' : ℕ} [NeZero Y.factorial] (hb : b < m) (hb' : b' < m)
    (he : (b':ZMod m)=-(b:ZMod m)) (hm : m∣Y.factorial) (V : ℕ) :
    unitMean Y.factorial (fun n => selectClass b' m n*model Y V n)=
      -unitMean Y.factorial (fun n => selectClass b m n*model Y V n) := by
  let f (b : ℕ) (u : (ZMod Y.factorial)ˣ) := selectClass b m (u:ZMod Y.factorial).val*model Y V (u:ZMod Y.factorial).val
  have hsel (u : (ZMod Y.factorial)ˣ) : selectClass b' m ((-u:(ZMod Y.factorial)ˣ):ZMod Y.factorial).val =
      selectClass b m (u:ZMod Y.factorial).val := by
    have H : ((((-u:(ZMod Y.factorial)ˣ):ZMod Y.factorial).val:ℕ):ZMod m)=(b':ZMod m) ↔
        (((u:ZMod Y.factorial).val:ℕ):ZMod m)=(b:ZMod m) := by rw [cast_neg hm,he,neg_inj]
    simp only [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hb'] at H
    simp only [selectClass,H]
  have hneg (u : (ZMod Y.factorial)ˣ) : f b' (-u)= -f b u := by
    simp only [f,hsel,ThetaRowReflection.model_neg_unit,mul_neg]
  have h := Fintype.sum_equiv (Equiv.neg (ZMod Y.factorial)ˣ) (fun u => f b' (-u)) (f b') (by intros; rfl)
  simp only [hneg,sum_neg_distrib] at h
  change (∑ u,f b' u)/Y.factorial.totient= -((∑ u,f b u)/Y.factorial.totient)
  rw [←h,neg_div]

#print axioms reflection

/-- For either sign the same growing family of moduli refines the requested
reduced class and attains the logarithmic-square lower bound. -/
theorem uniform : ∃ η : ℝ, 0<η ∧ ∀ᶠ T : ℕ in atTop,
    ∀ q r : ℕ, 0 < q → r < q → r.Coprime q → Real.log q≤η*Real.log T → ∀ z : ℝ, |z|=1 →
    let m := modulus T
    1< m ∧ q∣m ∧ ∃ n < m, n.Coprime m ∧ n%q=r ∧
        ∀ Y ≥ m, ∀ V ≥ max m 3,
          letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
          (Real.log T)^2/64≤z*(m.totient*unitMean Y.factorial (fun j => selectClass n m j*model Y V j)) := by
  obtain ⟨η,hη,U⟩ := ThetaCompactModels.uniform
  refine ⟨η,hη,?_⟩
  filter_upwards [U] with T he
  intro q r hq hr hc hqt z hz
  have hchoice : z=1 ∨ z= -1 := (abs_eq (by norm_num : (0:ℝ)≤1)).mp hz
  rcases hchoice with rfl|rfl
  · have H := he q r hq hr hc hqt
    obtain ⟨hm,hqm,n,hn,hnc,hnq,h⟩ := H
    exact ⟨hm,hqm,n,hn,hnc,hnq,fun Y hY V hV => by simpa only [one_mul] using (h Y hY V hV).2⟩
  let : NeZero q := ⟨hq.ne'⟩
  let v : (ZMod q)ˣ := -ZMod.unitOfCoprime r hc
  let b := (v:ZMod q).val
  have hb : b < q := ZMod.val_lt _
  have hbc : b.Coprime q := ZMod.val_coe_unit_coprime _
  have H := he q b hq hb hbc hqt
  let m := modulus T
  let : NeZero m := ⟨(positive T).ne'⟩
  obtain ⟨hm,hqm,t,ht,htc,htq,h⟩ := H
  let u : (ZMod m)ˣ := -ZMod.unitOfCoprime t htc
  let s := (u:ZMod m).val
  have hs : s < m := ZMod.val_lt _
  have hsc : s.Coprime m := ZMod.val_coe_unit_coprime _
  have he : (s:ZMod m)=-(t:ZMod m) := by simp [s,u]
  have hqb : (t:ZMod q)=(b:ZMod q) := (ZMod.natCast_eq_natCast_iff' ..).mpr (htq.trans (Nat.mod_eq_of_lt hb).symm)
  have hsr := congrArg (ZMod.castHom hqm (ZMod q)) he
  have hcast : (s:ZMod q)=(r:ZMod q) := by
    simpa only [map_neg,map_natCast,hqb,b,ZMod.natCast_zmod_val,v,Units.val_neg,ZMod.coe_unitOfCoprime,neg_neg] using hsr
  refine ⟨hm,hqm,s,hs,hsc,((ZMod.natCast_eq_natCast_iff' ..).mp hcast).trans (Nat.mod_eq_of_lt hr),?_⟩
  intro Y hY V hV
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  obtain ⟨hdiv,hh⟩ := h Y hY V hV
  rw [reflection ht hs he hdiv,mul_neg,neg_mul,one_mul,neg_neg]
  exact hh

#print axioms uniform
end
end Arxiv.«2501.03234».ThetaReflectedWindowMeans
