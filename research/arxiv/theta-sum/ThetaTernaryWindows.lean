import ThetaTernaryErrorBudget

/-! Contain a three-prime window centered at n/3 in a translated theta interval. -/
namespace Arxiv.«2501.03234».ThetaTernaryWindows
open Real Filter Finset ThetaTernaryErrorBudget ThetaShortPrimeInterval
noncomputable section

def window (n : ℕ) (θ : ℝ) := (Nat.primesLE n).filter (fun p : ℕ =>
  |(p:ℝ)-(n:ℝ)/3| ≤ (n:ℝ)^θ)

theorem scales {α θ : ℝ} (hα : 0≤α) (hθ : α<θ) (ht : θ<1) (m : ℕ) {K : ℝ} (hK : 0<K) (X₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ X H : ℕ, X₀≤X ∧ H≤X ∧
      K*(X:ℝ)^(α)*(width X)^(8+m) ≤ H ∧ (H:ℝ)≤8*(n:ℝ)^θ ∧
      width n≤2*width X ∧ 0<width X ∧
      ∀ p : ℕ,p∈window n θ → p∈Ioc X (X+H) := by
  let hpow := 8+m
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hδ : 0<θ-α := sub_pos.mpr hθ
  have hpoly := hn.eventually ((isLittleO_log_rpow_rpow_atTop hpow hδ).bound
    (show 0<(1:ℝ)/(K*2^hpow) by positivity))
  have hratio := ((tendsto_rpow_atTop (sub_pos.mpr ht)).comp hn).eventually_ge_atTop 128
  filter_upwards [hpoly,hratio,hn.eventually_ge_atTop 256,eventually_ge_atTop (8*X₀+256),
    (tendsto_log_atTop.comp hn).eventually_ge_atTop 1] with n hpoly hr hn hn₀ hL
  have hp : 0<(n:ℝ) := by linarith
  change 1≤log (n:ℝ) at hL
  change 128≤(n:ℝ)^(1-θ) at hr
  let R := (n:ℝ)^θ
  let T := ⌈R⌉₊
  let X := n/3-2*T
  let H := 4*T
  have hR : 1≤R := one_le_rpow (by linarith) (by linarith)
  have hTlo : R≤T := Nat.le_ceil _
  have hThi : (T:ℝ)≤2*R := by linarith only [Nat.ceil_lt_add_one (by linarith : 0≤R),hR]
  have hRsmall : 128*R ≤ n := by
    calc _ ≤ (n:ℝ)^(1-θ)*R := mul_le_mul_of_nonneg_right hr (by linarith)
         _ = _ := by dsimp [R];rw [←rpow_add hp,show 1-θ+θ=1 by ring,rpow_one]
  have hTsmall : 64*T≤n := by exact_mod_cast (show 64*(T:ℝ) ≤ n by linarith only [hThi,hRsmall])
  have hXn : n≤8*X := by dsimp [X];omega
  have hX : X≤n := by dsimp [X];omega
  have hX₀ : X₀≤X := by omega
  have hHX : H≤X := by dsimp [X,H];omega
  have hx : 1≤(X:ℝ) := by exact_mod_cast (show 1≤X by omega)
  have hxp : 0<(X:ℝ) := by linarith
  have hVX : 0<width X := by unfold width;linarith only [log_nonneg hx]
  have hV : width X≤width n := by unfold width;gcongr
  have hxn : (n:ℝ)≤8*X := by exact_mod_cast hXn
  have hxsq : (n:ℝ)≤(X:ℝ)^2 := by
    have hh : 8≤(X:ℝ) := by linarith only [hxn,hn]
    nlinarith only [hxn,mul_nonneg (sub_nonneg.mpr hh) hxp.le]
  have hLx := log_le_log hp hxsq
  rw [log_pow,Nat.cast_ofNat] at hLx
  have hwidth : width n≤2*width X := by unfold width;linarith only [hLx]
  have hLpos : 0<log (n:ℝ) := by linarith
  change ‖(log (n:ℝ))^(hpow:ℝ)‖ ≤ 1/(K*2^hpow)*‖(n:ℝ)^(θ-α)‖ at hpoly
  rw [rpow_natCast,Real.norm_of_nonneg (pow_nonneg hLpos.le _),Real.norm_of_nonneg (rpow_nonneg hp.le _),
    one_div_mul_eq_div,le_div_iff₀ (by positivity)] at hpoly
  have hdn : (width n)^hpow ≤ (2:ℝ)^hpow*(log n)^hpow := by
    rw [←mul_pow];apply pow_le_pow_left₀ (by unfold width;linarith) (by unfold width;linarith)
  have hprod : K*(width n)^hpow≤(n:ℝ)^(θ-α) := by
    linarith only [hpoly,mul_le_mul_of_nonneg_left hdn hK.le]
  have hbudget : K*(X:ℝ)^(α)*(width X)^(8+m)≤H := by
    have h₁ := rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) X) (Nat.cast_le.mpr hX) hα
    have h₂ := pow_le_pow_left₀ hVX.le hV hpow
    calc _ ≤ (n:ℝ)^(α)*(K*(width n)^hpow) := by
              rw [mul_comm ((n:ℝ)^(α)),mul_right_comm K];gcongr
              positivity [hVX.trans_le hV]
         _ ≤ (n:ℝ)^(α)*(n:ℝ)^(θ-α) := mul_le_mul_of_nonneg_left hprod (rpow_nonneg hp.le _)
         _ = R := by dsimp [R];rw [←rpow_add hp,show α+(θ-α)=θ by ring]
         _ ≤ T := hTlo
         _ ≤ H := by exact_mod_cast (show T≤H by dsimp [H];omega)
  refine ⟨X,H,hX₀,hHX,hbudget,by dsimp [H];push_cast;linarith only [hThi],hwidth,hVX,?_⟩
  intro p hp'
  have h : -R ≤ (p:ℝ)-(n:ℝ)/3 ∧ (p:ℝ)-(n:ℝ)/3≤R := abs_le.mp (mem_filter.mp hp').2
  have hg : 3*(n/3)≤n := by omega
  have hg' : n≤3*(n/3)+2 := by omega
  have hg₁ : 3*((n/3:ℕ):ℝ)≤n := by exact_mod_cast hg
  have hg₂ : (n:ℝ)≤3*((n/3:ℕ):ℝ)+2 := by exact_mod_cast hg'
  have htpos : 0<T := by exact_mod_cast (show 0<(T:ℝ) by linarith only [hTlo,hR])
  have hTX : X+2*T=n/3 := by dsimp [X];omega
  have hTX' : (X:ℝ)+2*T=((n/3:ℕ):ℝ) := by exact_mod_cast hTX
  have hp₁ : (X:ℝ)<p := by linarith only [h.1,hTX',hg₁,hTlo,hR]
  have hp₂ : (p:ℝ)≤X+4*T := by linarith only [h.2,hTX',hg₂,hTlo,hR]
  exact mem_Ioc.mpr ⟨Nat.cast_lt.mp hp₁,by change p≤X+4*T;exact_mod_cast hp₂⟩

#print axioms scales
end
end Arxiv.«2501.03234».ThetaTernaryWindows
