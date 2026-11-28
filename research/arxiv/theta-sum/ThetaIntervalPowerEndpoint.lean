import ThetaWindowPowerEndpoint

/-! Complete means and interval moments of translated periodic rows. -/
namespace Arxiv.«2501.03234».ThetaIntervalPowerEndpoint
open Finset ThetaPeriodMeans
noncomputable section

theorem translate_period {d : ℕ} {f : ℕ → ℝ} (hf : OnMod d f) (M : ℕ) :
    OnMod d (fun n => f (M+n)) := by
  intro n
  change f (M+n%d)=f (M+n)
  rw [← hf (M+n%d),Nat.add_mod_mod,hf]

theorem translate_mean {P : ℕ} (hP : 0<P) {f : ℕ → ℝ} (hf : OnMod P f) (M : ℕ) :
    mean P (fun n => f (M+n))=mean P f := by
  let : NeZero P := ⟨hP.ne'⟩
  unfold mean
  rw [ThetaAllWindowMoments.sum_period,ThetaAllWindowMoments.sum_period]
  congr 1
  have h (x : ZMod P) : f (M+x.val)=f ((M:ZMod P)+x).val := by
    have he : (M:ZMod P)+x=((M+x.val:ℕ):ZMod P) := by rw [Nat.cast_add,ZMod.natCast_zmod_val]
    rw [he,ZMod.val_natCast,hf]
  simp_rw [h]
  exact Fintype.sum_bijective _ (Equiv.addLeft (M:ZMod P)).bijective _ _ (fun _ => rfl)

theorem translated_power {Y : ℕ} (f : ℕ → ℕ → ℝ) (M X k : ℕ) {B : ℝ} (hB : 0≤B)
    (hf : ∀ d∈Icc 2 Y, OnMod d (f d)) (hb : ∀ d∈Icc 2 Y, ∀ n, |f d n|≤B) :
    (∑ n∈range X,(∑ d∈Icc 2 Y,f d (M+n))^k) ≤
      (X:ℝ)*mean Y.factorial (fun n => (∑ d∈Icc 2 Y,f d n)^k)+2*(B*(Y:ℝ)^2)^k := by
  have h := ThetaWindowPowerEndpoint.power_endpoint (Y:=Y) (fun d n => f d (M+n)) X k hB
    (fun d hd => translate_period (hf d hd) M) (fun d hd n => hb d hd (M+n))
  have hp : OnMod Y.factorial (fun n => (∑ d∈Icc 2 Y,f d n)^k) := by
    intro n
    dsimp
    congr 1
    exact sum_congr rfl (fun d hd => onMod_lift (Nat.dvd_factorial (by have := (mem_Icc.mp hd).1;omega) (mem_Icc.mp hd).2) (hf d hd) n)
  have ht := translate_mean (Nat.factorial_pos Y) hp M
  exact h.trans_eq (by rw [← ht])

#print axioms translated_power
end
end Arxiv.«2501.03234».ThetaIntervalPowerEndpoint
