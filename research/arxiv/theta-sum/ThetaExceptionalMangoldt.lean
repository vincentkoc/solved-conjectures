import ThetaExceptionalPrimeInput
import ThetaNaturalPrimeMeans

/-! Specializing the exceptional-character von Mangoldt estimate to ordinary log-weighted primes. -/
namespace Arxiv.«2501.03234».ThetaExceptionalMangoldt
open Filter Real Finset ThetaNaturalPrimeMeans ThetaExceptionalPrimeInput ThetaFiberDiscrepancy
noncomputable section

def corrected (x β u : ℝ) := x-u*x^β/β

/-- The usual pointwise exceptional-character term for the von Mangoldt sum.
A zero-free endpoint is represented by the zero coefficient function. The
primitive real character enters only by its residue values and zero gap. -/
def Estimate : Prop := ∃ c δ : ℝ,0<c ∧ 0<δ ∧ ∀ᶠ X : ℕ in atTop,
    ∃ f : ℕ,∃ β : ℝ,∃ χ : ℕ → ℝ,0<f ∧ 1/2≤β ∧ β<1 ∧ c/(f:ℝ)^2≤1-β ∧ (∀ b,χ b≤1) ∧
    ∀ q b : ℕ,0<q → (q:ℝ)≤radius X → b<q → b.Coprime q →
      |selectedPsi (fun n => n%q=b) (X+1) -
        (if f∣q then corrected X β (χ (b%f)) else (X:ℝ))/(q.totient:ℝ)| ≤
          X*exp (-δ*sqrt (log X))

theorem corrected_lower {x β u : ℝ} (hx : 0<x) (hL : 4≤log x)
    (hβ : 1/2≤β) (hβ' : β<1) (hu : u≤1) :
    (1-β)*x ≤ corrected x β u := by
  have hb : 0<β := by linarith
  have hg := one_sub_inv_le_log_of_pos hb
  have hlog : -2*(1-β) ≤ log β := by
    have haux : β⁻¹ ≤ 1+2*(1-β) := by
      rw [inv_le_iff_one_le_mul₀ hb]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hβ'.le) (show 0≤2*β-1 by linarith)]
    linarith only [hg,haux]
  have hbound : x^β ≤ x*β^2 := by
    rw [rpow_def_of_pos hx,←exp_log hx,←exp_log hb,←exp_nat_mul,←exp_add,exp_le_exp,log_exp,exp_log hb]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hlog,mul_le_mul_of_nonneg_right hL (sub_nonneg.mpr hβ'.le)]
  unfold corrected
  rw [le_sub_iff_add_le]
  have hdiv : u*x^β/β ≤ x*β := by
    rw [div_le_iff₀ hb]
    calc _ ≤ x^β := mul_le_of_le_one_left (rpow_nonneg hx.le _) hu
         _ ≤ x*β^2 := hbound
         _ = _ := by ring
  linarith only [hdiv]

private theorem allowances {δ : ℝ} (hδ : 0<δ) (C : ℝ) :
    ∀ᶠ X : ℕ in atTop, 4≤log (X:ℝ) ∧
      C*sqrt X + X*exp (-δ*sqrt (log X)) ≤ X/(radius X)^2 := by
  let hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  let hl := tendsto_log_atTop.comp hn
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/6)).comp hl
  have hbig := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/3)).comp hl
  have hc := ((tendsto_exp_atTop.comp tendsto_id).comp (hl.atTop_div_const (by norm_num : (0:ℝ)<4))).eventually_ge_atTop (2*C)
  filter_upwards [hl.eventually_ge_atTop 4,hpow.eventually_ge_atTop (3/δ),
    hbig.eventually_ge_atTop 16,hc,hn.eventually_gt_atTop 0] with X hL hg hG hC hx
  let L := log (X:ℝ)
  let R := L^(1/3:ℝ)
  change 4≤L at hL
  change 3/δ ≤ L^(1/6:ℝ) at hg
  change 16≤L^(2/3:ℝ) at hG
  change 2*C ≤ exp (L/4) at hC
  have hLp : 0<L := by linarith
  have hR : 1≤R := one_le_rpow (by linarith) (by norm_num)
  have hgap : 3*R ≤ δ*sqrt L := by
    have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hδ).mp hg) (rpow_nonneg hLp.le (1/3))
    rw [sqrt_eq_rpow];calc
      _ ≤ (L^(1/6:ℝ)*δ)*R := h
      _ = _ := by dsimp [R];rw [mul_right_comm,←rpow_add hLp];norm_num;ring
  have hmain : 16*R ≤ L := by
    have h := mul_le_mul_of_nonneg_right hG (rpow_nonneg hLp.le (1/3))
    rw [←rpow_add hLp,show (2/3+1/3:ℝ)=1 by norm_num,rpow_one] at h;exact h
  have h₂ : (2:ℝ)≤exp R := by linarith only [add_one_le_exp R,hR]
  have hs : sqrt (X:ℝ)=exp (L/2) := by rw [sqrt_eq_rpow,rpow_def_of_pos hx];congr 1;dsimp [L];ring
  have hx' : (X:ℝ)=exp L := (exp_log hx).symm
  have he : 2*(C*sqrt X) ≤ exp (L-2*R) := by
    rw [←mul_assoc,hs];apply (mul_le_mul_of_nonneg_right hC (exp_pos _).le).trans
    rw [←exp_add,exp_le_exp];linarith only [hmain,hR]
  have he' : 2*((X:ℝ)*exp (-δ*sqrt L)) ≤ exp (L-2*R) := by
    rw [hx',mul_left_comm,←mul_assoc]
    calc _ ≤ exp L*(exp R*exp (-δ*sqrt L)) := by rw [mul_assoc];gcongr
         _ ≤ _ := by rw [←exp_add,←exp_add,exp_le_exp];linarith only [hgap]
  refine ⟨hL,?_⟩
  change _ ≤ (X:ℝ)/(exp R)^2
  rw [hx',←exp_nat_mul,←exp_sub]
  rw [←hx'];norm_num only [Nat.cast_ofNat];linarith only [he,he']

theorem ordinary (H : Estimate) : ThetaExceptionalPrimeInput.Ordinary := by
  obtain ⟨c,δ,hc,hδ,he⟩ := H
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨c,hc,?_⟩
  filter_upwards [he,allowances hδ C,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop 0] with X h ha hx
  obtain ⟨f,β,χ,hf,hβ,hβ',hgap,hχ,hq⟩ := h
  refine ⟨f,(fun b => corrected X β (χ b)),hf,fun b => ?_,?_⟩
  · rw [mul_div_right_comm]
    exact (mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg _)).trans (corrected_lower hx ha.1 hβ hβ' (hχ _))
  · intro q b hp hsize hb hcop
    have hs := selected_prime_weight_bounds (fun n => n%q=b) X
    let T := mass (Nat.primesLE X) (fun p => log p) q b
    let P := selectedPsi (fun n => n%q=b) (X+1)
    have hset : ThetaPrimeDensity.primeSet (fun n => n%q=b) X = (Nat.primesLE X).filter (fun n => n%q=b) := by
      ext n;simp [ThetaPrimeDensity.primeSet]
    dsimp only at hs
    rw [hset] at hs
    change T ≤ P ∧ P-T ≤ _ at hs
    have hdiff : |T-P| ≤ C*sqrt X := by rw [abs_of_nonpos (sub_nonpos.mpr hs.1)];linarith only [hs.2,hC X]
    let v := center f q b X (fun j => corrected X β (χ j))/(q.totient:ℝ)
    change |T-v|≤_
    exact ((abs_sub_le T P v).trans (add_le_add hdiff (hq q b hp hsize hb hcop))).trans ha.2

#print axioms corrected_lower
#print axioms ordinary
end
end Arxiv.«2501.03234».ThetaExceptionalMangoldt
