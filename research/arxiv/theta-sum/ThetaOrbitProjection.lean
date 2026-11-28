import ThetaCenteredExposure

/-! A small-prime projection acting on every residue, including the nonunits. -/
namespace Arxiv.«2501.03234».ThetaOrbitProjection
open Finset Real ThetaFiniteExposure ThetaUnitExposure ThetaSmoothFiltration ThetaExposureLayers
open ThetaSmoothConditionalModel ThetaConditionalRows ThetaAllWindowMoments ThetaPeriodMeans
noncomputable section
local instance (Y : ℕ) : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩

private theorem key_map {P m : ℕ} [NeZero P] [NeZero m] (h : m∣P) (u : (ZMod P)ˣ) :
    ((ZMod.unitsMap h u : (ZMod m)ˣ):ZMod m).val=key m u := by
  rw [ZMod.unitsMap_val,← ZMod.natCast_zmod_val (u:ZMod P),ZMod.cast_natCast h,ZMod.val_natCast]
  rfl

private theorem same {P m : ℕ} [NeZero P] [NeZero m] (h : m∣P) (u v : (ZMod P)ˣ) :
    key m u=key m v ↔ ZMod.unitsMap h u=ZMod.unitsMap h v := by
  rw [←key_map h,←key_map h]
  constructor
  · exact fun he => Units.ext (ZMod.val_injective m he)
  · exact fun he => congrArg (fun x : (ZMod m)ˣ => (x:ZMod m).val) he

theorem translate {P m : ℕ} [NeZero P] [NeZero m] (h : m∣P) (f : (ZMod P)ˣ → ℝ)
    (x : (ZMod P)ˣ) : proj (key m) f x=avg (fiber (key m) (key m (1:(ZMod P)ˣ))) (fun u => f (x*u)) := by
  classical
  let A := fiber (key (P:=P) m) (key m (1:(ZMod P)ˣ))
  have he : fiber (key m) (key m x)=A.map (Equiv.mulLeft x).toEmbedding := by
    ext u
    rw [mem_map_equiv]
    simp only [A,fiber,mem_filter,mem_univ,true_and,same h]
    change ZMod.unitsMap h u=ZMod.unitsMap h x ↔ ZMod.unitsMap h (x⁻¹*u)=ZMod.unitsMap h 1
    rw [map_mul,map_inv,map_one,inv_mul_eq_one]
    exact eq_comm
  change (∑ u∈fiber (key m) (key m x),f u)/_=(∑ u∈A,f (x*u))/A.card
  rw [he,sum_map,card_map]
  rfl

def smooth (Y T : ℕ) (f : ℕ → ℝ) (n : ℕ) :=
  avg (fiber (key (modulus Y.factorial T)) (key (modulus Y.factorial T) (1:(ZMod Y.factorial)ˣ)))
    (fun u : (ZMod Y.factorial)ˣ => f (n*(u:ZMod Y.factorial).val))

theorem unit_value (Y T : ℕ) (W : Window) (x : (ZMod Y.factorial)ˣ) :
    smooth Y T (rowModel Y W) (x:ZMod Y.factorial).val=value Y W T x := by
  let : NeZero (modulus Y.factorial T) := ⟨(pos (Nat.factorial_pos _) T).ne'⟩
  rw [value,translate (divides (Nat.factorial_pos _) T)]
  simp only [smooth,Units.val_mul,ZMod.val_mul,periodic Y W _]

theorem orbit (Y T n : ℕ) (W : Window) : ∃ v : (ZMod Y.factorial)ˣ, ∀ t : ℕ,
    rowModel Y W (n*t)=rowModel Y (masked W n) ((v:ZMod Y.factorial).val*t) ∧
    smooth Y T (rowModel Y W) (n*t)=smooth Y T (rowModel Y (masked W n)) ((v:ZMod Y.factorial).val*t) := by
  obtain ⟨v,hv⟩ := orbit_model Y n W
  refine ⟨v,fun t => ⟨hv t,?_⟩⟩
  unfold smooth avg
  congr 1
  apply sum_congr rfl
  intro u _
  simpa only [Nat.mul_assoc] using hv (t*(u:ZMod Y.factorial).val)

theorem smooth_baseline {Y T : ℕ} (hY : 2≤Y) (hT : 2≤T) (hl : 1≤log T) (W : Window) (n : ℕ) :
    |smooth Y T (rowModel Y W) n|≤ThetaModelExponentialMoment.height T := by
  obtain ⟨v,hv⟩ := orbit Y T n W
  have h := (hv 1).2
  simp only [Nat.mul_one,unit_value] at h
  rw [h]
  exact baseline hY hT hl _ _

#print axioms smooth_baseline
end
end Arxiv.«2501.03234».ThetaOrbitProjection
