import ThetaPowerResidueMeans

/-! The original prime average for unions of power-residue classes. -/
namespace Arxiv.«2501.03234».ThetaPowerResiduePrimeMeans
open Finset Filter Real ThetaNaturalPrimeMeans ThetaPrimeDensity ThetaDiagonalConstant
open ThetaConditionalRows ThetaDyadicLaw ThetaPeriodMeans ThetaProgressionProjection ThetaLevelCoefficients
open ThetaPowerResidueMeans ThetaBoundedOrderSpectrum ThetaSpectralVariance
open scoped Topology
noncomputable section

def allows {m : ℕ} (A : Finset (ZMod m)ˣ) (n : ℕ) : Prop := ∃ u∈A,(n:ZMod m)=(u:ZMod m)

private lemma sum_select {m : ℕ} (A : Finset (ZMod m)ˣ) (n : ℕ) [Decidable (allows A n)] :
    ∑ u∈A,select u n = if allows A n then 1 else 0 := by
  classical
  by_cases h : allows A n
  · obtain ⟨u,hu,he⟩ := h
    simp only [if_pos (show allows A n from ⟨u,hu,he⟩),select,he,Units.val_inj,sum_ite_eq,hu,if_true]
  · rw [if_neg h]; apply sum_eq_zero; intro u hu
    exact if_neg fun he => h ⟨u,hu,he⟩

/-- The original prime mean over a nonempty union of reduced residue classes
converges to the average of their individual means. -/
theorem limit {m : ℕ} [NeZero m] (A : Finset (ZMod m)ˣ) (ha : A.Nonempty) (hAP : ProgressionMangoldt) :
    Tendsto (predicateMean (allows A) (fun p => (S p:ℝ)/p-log p/2)) atTop (𝓝 (diagonalConstant+bias m A)) := by
  classical
  let w (n : ℕ) : ℝ := if allows A n then 1 else 0
  have hw (n) : w n = ∑ u∈A,select u n := (sum_select A n).symm
  have hp : OnMod m w := by
    intro n; rw [hw,hw]; apply sum_congr rfl; intro u _; simp [select,ZMod.natCast_mod]
  have hv (u : (ZMod m)ˣ) : allows A (u:ZMod m).val ↔ u∈A := by
    simp [allows,Units.val_inj]
  have hmean : unitMean m w=A.card/m.totient := by
    unfold unitMean
    simp only [w,hv,sum_boole,filter_mem_eq_inter,univ_inter]
  have hD := periodic_prime_mean hAP hp
  rw [hmean] at hD
  have hn : Tendsto (primeMean (fun p => centered p*w p)) atTop
      (𝓝 ((∑ u∈A,predictor m (u:ZMod m).val)/m.totient)) := by
    have h := tendsto_finsetSum A (fun u _ => select_mean u hAP)
    rw [sum_div]
    apply h.congr'; filter_upwards with X
    simp only [primeMean,hw,mul_sum,←sum_div]; rw [sum_comm]
  have hφ : 0<(m.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos m))
  have hcard : 0<(A.card:ℝ) := Nat.cast_pos.mpr ha.card_pos
  have hd := hn.div hD (div_pos hcard hφ).ne'
  rw [div_div_div_cancel_right₀ hφ.ne'] at hd
  apply (hd.const_add diagonalConstant).congr'
  filter_upwards [hD.eventually_const_lt (div_pos hcard hφ),
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting).eventually_gt_atTop 0] with X hD' hπ
  let D := primeSet (allows A) X
  have hden : primeMean w X=(D.card:ℝ)/X.primeCounting := by simp [primeMean,w,D,primeSet,sum_boole]
  have hnum : ∑ p∈Nat.primesLE X,centered p*w p=∑ p∈D,centered p := by
    rw [show D=(Nat.primesLE X).filter (allows A) from rfl,sum_filter]
    apply sum_congr rfl; intro p _; dsimp [w]; split_ifs <;> simp
  rw [hden] at hD'
  have hx : (D.card:ℝ)≠0 := by intro h; simp [h] at hD'
  change diagonalConstant+(primeMean (fun p => centered p*w p) X)/(primeMean w X)=_
  rw [hden,primeMean,hnum,div_div_div_cancel_right₀ (by exact (show 0<(X.primeCounting:ℝ) from hπ).ne')]
  change diagonalConstant+(∑ p∈D,centered p)/D.card=(∑ p∈D,_)/D.card
  simp only [centered,ThetaCharacterPrimeMeans.residual,sum_sub_distrib,sum_const,nsmul_eq_mul]
  field_simp
  ring

theorem original (hAP : ProgressionMangoldt) {k : ℕ} (hk : 0< k) :
    ∃ C : ℝ, 0≤ C ∧ ∀ m : ℕ, [NeZero m] → ∀ A : Finset (ZMod m)ˣ, A.Nonempty → Stable k A →
      ∃ L : ℝ, |L-diagonalConstant|≤ C ∧
        Tendsto (predicateMean (allows A) (fun p => (S p:ℝ)/p-log p/2)) atTop (𝓝 L) := by
  refine ⟨∑' u : Mode,weight k 0 u,tsum_nonneg fun u => ThetaBoundedOrderSpectrum.nonneg k 0 u,?_⟩
  intro m _ A ha hstable
  exact ⟨_,by simpa only [add_sub_cancel_left] using bounded hk hstable hAP,limit A ha hAP⟩

theorem original_odd (hAP : ProgressionMangoldt) {k m : ℕ} [NeZero m] (hk : _root_.Odd k)
    (A : Finset (ZMod m)ˣ) (ha : A.Nonempty) (hA : Stable k A) :
    Tendsto (predicateMean (allows A) (fun p => (S p:ℝ)/p-log p/2)) atTop (𝓝 diagonalConstant) := by
  simpa only [odd_bias hk hA hAP,add_zero] using limit A ha hAP

#print axioms original_odd
#print axioms original
end
end Arxiv.«2501.03234».ThetaPowerResiduePrimeMeans
