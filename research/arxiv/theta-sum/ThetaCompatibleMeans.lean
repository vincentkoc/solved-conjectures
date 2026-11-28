import ThetaCompatibleModels
import ThetaOppositeMeans
import ThetaIdentityPrimeMeans

/-! Two-sided extreme conditional means within any fixed reduced prime class. -/
namespace Arxiv.«2501.03234».ThetaCompatibleMeans
open Filter Finset Real ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaIdentityFiber
open ThetaFactorialSequence ThetaProgressionProjection ThetaDiagonalConstant
open scoped Topology
noncomputable section

private lemma positive (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0 < q)
    (hr : r < q) (hc : r.Coprime q) :
    ∀ᶠ T : ℕ in atTop, let m := modulus T
      letI : NeZero m := ⟨pow_ne_zero _ (Nat.factorial_ne_zero _)⟩
      1 < m ∧ q∣m ∧ ∃ n < m, n.Coprime m ∧ n%q=r ∧
        (log T)^2/(8*Real.pi^2) ≤ predictor m n := by
  filter_upwards [ThetaCompatibleModels.growing hq hr hc] with T h
  obtain ⟨hm,hqm,n,hn,hnc,hnq,H⟩ := h
  let m := modulus T
  let : NeZero m := ⟨pow_ne_zero _ (Nat.factorial_ne_zero _)⟩
  obtain ⟨L,hL,ht⟩ := ThetaIdentityPrimeMeans.residue_transfer hAP hm hn hnc H
  have he : L=diagonalConstant+predictor m n := tendsto_nhds_unique ht (original_mean m n hnc hn hAP)
  refine ⟨hm,hqm,n,hn,hnc,hnq,?_⟩
  rw [he] at hL
  have hh : 8/Real.pi^2*((log T)^2/64)=(log T)^2/(8*Real.pi^2) := by ring
  linarith only [hL,hh]

/-- Each sufficiently large factorial modulus has two unit classes above the
prescribed residue. Their conditional centered means have opposite excursions
of size at least (log T)²/(8π²). -/
theorem both (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0 < q)
    (hr : r < q) (hc : r.Coprime q) :
    ∀ᶠ T : ℕ in atTop, let m := modulus T
      letI : NeZero m := ⟨pow_ne_zero _ (Nat.factorial_ne_zero _)⟩
      1 < m ∧ q∣m ∧ ∃ n < m, ∃ s < m, n.Coprime m ∧ s.Coprime m ∧ n%q=r ∧ s%q=r ∧
        (log T)^2/(8*Real.pi^2) ≤ predictor m n ∧ predictor m s ≤ -(log T)^2/(8*Real.pi^2) := by
  let : NeZero q := ⟨hq.ne'⟩
  let v : (ZMod q)ˣ := -ZMod.unitOfCoprime r hc
  let b := (v:ZMod q).val
  have hb : b < q := ZMod.val_lt _
  have hbc : b.Coprime q := ZMod.val_coe_unit_coprime _
  filter_upwards [positive hAP hq hr hc,positive hAP hq hb hbc] with T H G
  let m := modulus T
  let : NeZero m := ⟨pow_ne_zero _ (Nat.factorial_ne_zero _)⟩
  obtain ⟨hm,hqm,n,hn,hnc,hnq,hp⟩ := H
  obtain ⟨_,_,t,ht,htc,htq,htp⟩ := G
  let u : (ZMod m)ˣ := -ZMod.unitOfCoprime t htc
  let s := (u:ZMod m).val
  have hs : s < m := ZMod.val_lt _
  have hsc : s.Coprime m := ZMod.val_coe_unit_coprime _
  have he : (s:ZMod m)=-(t:ZMod m) := by simp [s,u]
  have hqb : (t:ZMod q)=(b:ZMod q) := (ZMod.natCast_eq_natCast_iff' ..).mpr (htq.trans (Nat.mod_eq_of_lt hb).symm)
  have hsr := congrArg (ZMod.castHom hqm (ZMod q)) he
  have hcast : (s:ZMod q)=(r:ZMod q) := by
    simpa only [map_neg,map_natCast,hqb,b,ZMod.natCast_zmod_val,v,Units.val_neg,ZMod.coe_unitOfCoprime,neg_neg] using hsr
  have hmod := ((ZMod.natCast_eq_natCast_iff' ..).mp hcast).trans (Nat.mod_eq_of_lt hr)
  refine ⟨hm,hqm,n,hn,s,hs,hnc,hsc,hnq,hmod,hp,?_⟩
  rw [ThetaOppositeMeans.reflection he hAP,neg_div]
  exact neg_le_neg htp

#print axioms both
end
end Arxiv.«2501.03234».ThetaCompatibleMeans
