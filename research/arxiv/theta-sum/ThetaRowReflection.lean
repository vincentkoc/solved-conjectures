import ThetaCharacterCoefficient
/-! Oddness of the primitive reciprocal row on reduced residues. -/
namespace Arxiv.«2501.03234».ThetaRowReflection
open Finset ThetaRowCorrelations ThetaCharacterThree ThetaConditionalRows

private lemma parity_opp {d : ℕ} [NeZero d] (hd : 1<d) (ho : Odd d) (u : (ZMod d)ˣ) :
    parity ((-u:(ZMod d)ˣ):ZMod d).val= -parity (u:ZMod d).val := by
  let : Fact (1<d) := ⟨hd⟩
  let : NeZero (u:ZMod d) := ⟨u.ne_zero⟩
  rw [Units.val_neg,ZMod.val_neg_of_ne_zero]
  have hsum := Nat.sub_add_cancel (Nat.le_of_lt (ZMod.val_lt (u:ZMod d)))
  have hpow : (-1:ℤ)^(d-(u:ZMod d).val)*(-1)^(u:ZMod d).val= -1 := by
    rw [← pow_add,hsum,ho.neg_one_pow]
  have hsq : ((-1:ℤ)^(u:ZMod d).val)^2=1 := by rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  unfold parity
  linear_combination -((-1:ℤ)^(u:ZMod d).val)*hpow + ((-1:ℤ)^(d-(u:ZMod d).val))*hsq

theorem wave_neg_unit {d : ℕ} [NeZero d] (hd : 1<d) (u : (ZMod d)ˣ) (w : ℕ) :
    wave ((-u:(ZMod d)ˣ):ZMod d).val d w = -wave (u:ZMod d).val d w := by
  by_cases h : d%2=1 ∧ w%2=1 ∧ w.Coprime d
  · have h₁ := Nat.odd_iff.mpr h.1
    have h₂ := Nat.odd_iff.mpr h.2.1
    rw [wave_unit h₁ h₂ h.2.2,wave_unit h₁ h₂ h.2.2]
    have he : ZMod.unitOfCoprime w h.2.2 / -u = -(ZMod.unitOfCoprime w h.2.2 / u) := by
      apply Units.ext
      simp [div_eq_mul_inv]
    rw [he,parity_opp hd h₁]
  · have hz (v : (ZMod d)ˣ) : wave (v:ZMod d).val d w=0 := if_neg (fun H => h H.2)
    simp only [hz,neg_zero]

theorem row_neg_unit {d : ℕ} [NeZero d] (hd : 1<d) (u : (ZMod d)ˣ) (K : ℕ) :
    row d K ((-u:(ZMod d)ˣ):ZMod d).val = -row d K (u:ZMod d).val := by
  unfold row
  simp only [wave_neg_unit hd,Int.cast_neg,mul_neg,sum_neg_distrib]

private lemma row_restrict {P d : ℕ} [NeZero d] [NeZero P] (h : d ∣ P)
    (u : (ZMod P)ˣ) (K : ℕ) :
    row d K ((ZMod.unitsMap h u : ZMod d).val) = row d K (u:ZMod P).val := by
  have hv : (ZMod.unitsMap h u : ZMod d).val = (u:ZMod P).val%d := by
    rw [ZMod.unitsMap_val,← ZMod.natCast_zmod_val (u:ZMod P),ZMod.cast_natCast h,
      ZMod.val_natCast,ZMod.natCast_zmod_val]
  rw [hv,row_onMod d K]

private lemma restrict_neg {P d : ℕ} (h : d ∣ P) (u : (ZMod P)ˣ) :
    ZMod.unitsMap h (-u) = -ZMod.unitsMap h u := by
  apply Units.ext
  simp [ZMod.unitsMap_def]

open ThetaPrimeTailTransfer
local instance (T : ℕ) : NeZero T.factorial := ⟨(Nat.factorial_pos _).ne'⟩

theorem model_neg_unit (T V : ℕ) (u : (ZMod T.factorial)ˣ) :
    model T V ((-u:(ZMod T.factorial)ˣ):ZMod T.factorial).val = -model T V (u:ZMod T.factorial).val := by
  unfold model low
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro d hd
  have h2 := (mem_Icc.mp hd).1
  have h : d ∣ T.factorial := Nat.dvd_factorial (by omega) (mem_Icc.mp hd).2
  let : NeZero d := ⟨by omega⟩
  rw [← row_restrict h (-u),← row_restrict h u,restrict_neg,row_neg_unit (by omega : 1<d),mul_neg]

theorem finite_test_reflection (B c : ℝ) (T V : ℕ) (φ : ℝ → ℝ) :
    unitMean T.factorial (fun n => φ (B+c*model T V n)) =
      unitMean T.factorial (fun n => φ (B-c*model T V n)) := by
  unfold unitMean
  congr 1
  apply Fintype.sum_equiv (Equiv.neg (ZMod T.factorial)ˣ)
  intro u
  simp only [Equiv.neg_apply,model_neg_unit,mul_neg,sub_neg_eq_add]

#print axioms finite_test_reflection
#print axioms row_neg_unit
end Arxiv.«2501.03234».ThetaRowReflection
