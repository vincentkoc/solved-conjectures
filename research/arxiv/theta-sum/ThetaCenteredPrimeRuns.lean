import ThetaCenteredBackward
import ThetaShortPrimeRuns
import ThetaCenteredOriginalTail

/-! Stretched-exponentially long runs in the ordered prime lists. -/
namespace Arxiv.«2501.03234».ThetaCenteredPrimeRuns
open Finset Filter Real ThetaPrimeDensity ThetaPrimeRuns ThetaShortPrimeRuns ThetaShortProgressions
open ThetaCenteredDeviation ThetaBackwardInterval ThetaShortPrimeInterval
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable _

def depth (a : ℝ) (x : ℕ) := exp (a*rate x)

theorem depth_tendsto {a : ℝ} (ha : 0<a) : Tendsto (depth a) atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [ThetaShortCenteredInterval.absorb (by positivity : 0 < |n|+1) ha 0] with x hx
  simp only [pow_zero,mul_one] at hx
  exact (by linarith only [le_abs_self n] : n≤|n|+1).trans hx

/-- Uniformly in all reduced classes with polylogarithmic modulus, almost
every class prime starts an uninterrupted run within this same short window.
Weil and the ordinary prime count in progressions are the two inputs. -/
theorem progressions (weil : ThetaWeilShortIntervals.Weil) {ε : ℝ} (he : 0<ε) :
    ∃ a : ℝ, 0<a ∧ ∀ K : ℕ, Ordinary K → ∀ᶠ x : ℕ in atTop,
    ∀ q r : ℕ, 0<q → (q:ℝ)≤(log x)^K → r.Coprime q →
    let A := window x (fun p => p ≡ r [MOD q])
    let F := depth a (left x)
    (1-3/F)*A.card ≤ ((starts A ⌊F⌋₊ (deviates ε)).card:ℝ) := by
  obtain ⟨b,hb,hb1,h⟩ := ThetaCenteredBackward.count weil he
  let a := b/4
  have ha : 0<a := by dsimp [a];positivity
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  refine ⟨a,ha,?_⟩
  intro K li
  have hD : (0:ℝ)<250*2^(K+1) := by positivity
  filter_upwards [h,li,admissible,hl.eventually_ge_atTop 1,
    tendsto_left.eventually (ThetaShortCenteredInterval.absorb hD ha (K+1))] with x hx hc hw hLx hpoly
  let Y := left x
  let R := rate (Y:ℝ)
  let F := depth a Y
  have hR : 0<R := rate_pos _
  have hF : 1≤F := one_le_exp (mul_nonneg ha.le hR.le)
  obtain ⟨_,_,_,hL2,hL⟩ := hw
  change 1≤log (x:ℝ) at hLx
  have hlog : 0<log (x:ℝ) := by linarith
  have hle : left x≤x := Nat.floor_le_of_le (by linarith only [show 0≤width x by unfold width;positivity])
  have hYpos : 0<(Y:ℝ) := by
    by_contra! h
    have hz := le_antisymm h (Nat.cast_nonneg Y)
    change 1≤log (Y:ℝ) at hL
    rw [hz,log_zero] at hL
    norm_num at hL
  have hXpos : 0<(x:ℝ) := hYpos.trans_le (by exact_mod_cast hle)
  have hlogs := log_le_log hYpos (show (Y:ℝ)≤(x:ℝ) by exact_mod_cast hle)
  have hW : F^3≤width x := by
    dsimp [F,depth,width]
    rw [←exp_nat_mul,rpow_def_of_pos hXpos,exp_le_exp]
    have hr := rate_le hL
    change R≤log (Y:ℝ) at hr
    dsimp [a]
    change ((3:ℕ):ℝ)*(b/4*R)≤_
    nlinarith only [mul_le_mul_of_nonneg_right hb1 hR.le,hr,hlogs,hLx]
  have hfac : 250*(log (x:ℝ))^(K+1)≤F := by
    have hh : (log (x:ℝ))^(K+1)≤2^(K+1)*(1+log (Y:ℝ))^(K+1) := by
      rw [←mul_pow];exact pow_le_pow_left₀ hlog.le (by change log (x:ℝ)≤2*log (Y:ℝ) at hL2;linarith) _
    change 250*2^(K+1)*(1+log (Y:ℝ))^(K+1)≤F at hpoly
    linarith only [mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤250),hpoly]
  apply of_count hc hlog hF hW hfac
  have hid : exp (-b*R)=(F^4)⁻¹ := by
    dsimp [F,depth,a];rw [←exp_nat_mul,←exp_neg];congr 1;ring
  change ((window x (deviates ε)).card:ℝ)≤width x*exp (-b*R) at hx
  rw [hid] at hx
  rw [div_eq_mul_inv]
  exact hx.trans (mul_le_mul_of_nonneg_right (by linarith only [show 0≤width x by unfold width;positivity]) (by positivity))

/-- Almost every ordinary prime through X begins a run of this length among
the ordinary primes through X. No short-interval prime input is needed. -/
theorem ordinary {ε : ℝ} (he : 0<ε) : ∃ a : ℝ, 0<a ∧ ∀ᶠ X : ℕ in atTop,
    let A := Nat.primesLE X
    let F := depth a X
    (1-3/F)*A.card ≤ ((starts A ⌊F⌋₊ (deviates ε)).card:ℝ) := by
  obtain ⟨b,hb,h⟩ := ThetaCenteredOriginalTail.original he
  let a := min (b/4) (1/100:ℝ)
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  have ha1 : a≤1/100 := min_le_right ..
  have hab : a≤b/4 := min_le_left ..
  let c := log 2/2
  have hc : 0<c := div_pos (log_pos (by norm_num)) (by norm_num)
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).bound hc)
  refine ⟨a,ha,?_⟩
  filter_upwards [h,prime_count_lower,hsmall,hl.eventually_ge_atTop 1,eventually_ge_atTop 1] with X hx hπ hlog hL hX
  change 1≤log (X:ℝ) at hL
  have hxp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hs := sqrt_pos_of_pos hxp
  change ‖log (X:ℝ)‖≤c*‖(X:ℝ)^(1/2:ℝ)‖ at hlog
  rw [Real.norm_eq_abs,abs_of_pos (by linarith),←sqrt_eq_rpow,Real.norm_eq_abs,abs_of_pos hs] at hlog
  have hP : sqrt X≤Nat.primeCounting X := by
    apply (mul_le_mul_iff_left₀ (mul_pos hc hs)).mp
    have heq : sqrt X*(c*sqrt X)=c*(X:ℝ) := by rw [show sqrt X*(c*sqrt X)=c*(sqrt X)^2 by ring,sq_sqrt hxp.le]
    exact heq.le.trans (hπ.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)))
  let F := depth a X
  let A := Nat.primesLE X
  let P : ℝ := A.card
  have hF : 1≤F := one_le_exp (mul_nonneg ha.le (rate_pos _).le)
  have hW : F^3≤P := by
    apply le_trans _ (show sqrt X≤P by simpa only [P,A,Nat.primesLE_card_eq_primeCounting] using hP)
    dsimp [F,depth];rw [←exp_nat_mul,sqrt_eq_rpow,rpow_def_of_pos hxp,exp_le_exp]
    nlinarith only [mul_le_mul_of_nonneg_right ha1 (rate_pos (X:ℝ)).le,rate_le hL,hL]
  have hA : P≤(A.card:ℝ)*F := by change P≤P*F;exact le_mul_of_one_le_right (Nat.cast_nonneg _) hF
  apply many A (deviates ε) hF hW hA
  change ((A.filter (deviates ε)).card:ℝ)≤2*P/F^4
  have hsame : A.filter (deviates ε)=primeSet (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-(p:ℝ)*log p/2|) X := by
    classical rfl
  rw [hsame]
  rw [←rate_eq (by linarith : 0<log (X:ℝ))] at hx
  have hcomp : exp (-b*rate X)≤(F^4)⁻¹ := by
    dsimp [F,depth];rw [←exp_nat_mul,←exp_neg,exp_le_exp]
    norm_num1
    nlinarith only [mul_le_mul_of_nonneg_right hab (rate_pos (X:ℝ)).le]
  change _≤Nat.primeCounting X*exp (-b*rate X) at hx
  have heq : (Nat.primeCounting X:ℝ)=P := by simp [P,A]
  rw [heq] at hx
  apply hx.trans
  rw [div_eq_mul_inv]
  exact mul_le_mul (by change P≤2*P;linarith only [show 0≤P from Nat.cast_nonneg _]) hcomp (exp_pos _).le (by dsimp [P];positivity)

#print axioms ordinary

#print axioms progressions
end
end Arxiv.«2501.03234».ThetaCenteredPrimeRuns
