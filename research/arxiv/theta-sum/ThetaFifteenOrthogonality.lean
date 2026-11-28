import ThetaJacobiFifteen
import ThetaPrimeSpectrum

/-! Exact cancellation below conductor fifteen and against every prime quadratic mode. -/
namespace Arxiv.«2501.03234».ThetaFifteenOrthogonality
open Finset Filter Topology ThetaJacobiRows ThetaJacobiFifteen ThetaConditionalRows ThetaPeriodMeans
open ThetaNaturalPrimeMeans

noncomputable abbrev w (q n : ℕ) : ℝ := (symbol q n:ℝ)

lemma periodic (q : ℕ) : OnMod q (w q) :=
  fun n => congrArg (Int.cast (R:=ℝ)) (symbol_mod q (dvd_refl q) n)

lemma bounded (q n : ℕ) [NeZero q] : |w q n| ≤ 1 := by
  by_cases h : n.Coprime q
  · rcases symbol_unit q h with h|h <;> simp [w,h]
  · simp [w,symbol_zero q h]

private lemma product_period {d e P : ℕ} (hd : d∣P) (he : e∣P)
    {f g : ℕ → ℝ} (hf : OnMod d f) (hg : OnMod e g) : OnMod P (fun n => f n*g n) :=
  fun n => congrArg₂ (·*·) (onMod_lift hd hf n) (onMod_lift he hg n)

private lemma common_mean {P M : ℕ} [NeZero P] [NeZero M] {f : ℕ → ℝ}
    (hf : OnMod P f) (hg : OnMod M f) : unitMean P f=unitMean M f := by
  rw [←unitMean_lift (Nat.dvd_mul_right P M) hf,unitMean_lift (Nat.dvd_mul_left M P) hg]

private lemma splitting {a b : ℕ} [NeZero a] [NeZero b] (hab : a*b=15) (n : ℕ) :
    w 15 n=w a n*w b n := by
  rw [←hab]
  simp only [w,symbol,jacobiSym.mul_right,Int.cast_mul]

private lemma missing_factor {a b d P : ℕ} [NeZero a] [NeZero b] [NeZero d] [NeZero P]
    (hab : a*b=15) (ha : a.Coprime b) (had : a.Coprime d) (hp : 15∣P) (hd : d∣P)
    (hz : unitMean a (w a)=0) {f : ℕ → ℝ} (hf : OnMod d f) :
    unitMean P (fun n => w 15 n*f n)=0 := by
  let g n := w b n*f n
  have hg : OnMod (b*d) g := product_period (Nat.dvd_mul_right b d) (Nat.dvd_mul_left d b) (periodic b) hf
  have he : (fun n => w 15 n*f n)=(fun n => w a n*g n) := by
    funext n; rw [splitting hab]; dsimp [g]; ring
  have hp' := product_period hp hd (periodic 15) hf
  rw [he] at hp' ⊢
  rw [common_mean hp' (product_period (Nat.dvd_mul_right a (b*d)) (Nat.dvd_mul_left (b*d) a) (periodic a) hg),
    unitMean_mul (ha.mul_right had) (periodic a) hg,hz,zero_mul]

private lemma prime_center (q : ℕ) [Fact q.Prime] (h : q≠2) :
    unitMean q (w q)=0 := by
  have he : w q=(fun n => (ThetaLegendreFactors.symbol q n:ℝ)) := by
    funext n
    simp only [w,symbol,←jacobiSym.legendreSym.to_jacobiSym,legendreSym,ThetaLegendreFactors.symbol,Int.cast_natCast]
  rw [he,ThetaPrimeSpectrum.symbol_unitMean_zero q h]

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Any periodic test missing either the 3-component or the 5-component has zero twist. -/
theorem missing_modulus {d P : ℕ} [NeZero d] [NeZero P]
    (hp : 15∣P) (hd : d∣P) (hmiss : ¬15∣d) {f : ℕ → ℝ} (hf : OnMod d f) :
    unitMean P (fun n => w 15 n*f n)=0 := by
  by_cases h3 : 3∣d
  · have h5 : ¬5∣d := by omega
    exact missing_factor (a:=5) (b:=3) (by decide) (by decide)
      ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h5) hp hd (prime_center 5 (by decide)) hf
  · exact missing_factor (a:=3) (b:=5) (by decide) (by decide)
      (Nat.prime_three.coprime_iff_not_dvd.mpr h3) hp hd (prime_center 3 (by decide)) hf

theorem against_period {d : ℕ} [NeZero d] (hAP : ProgressionMangoldt) (hd : ¬15∣d)
    {f : ℕ → ℝ} (hf : OnMod d f) :
    Tendsto (primeMean (fun n => w 15 n*f n)) atTop (𝓝 0) := by
  have h := periodic_prime_mean hAP (product_period (Nat.dvd_mul_right 15 d)
    (Nat.dvd_mul_left d 15) (periodic 15) hf)
  rwa [missing_modulus (Nat.dvd_mul_right 15 d) (Nat.dvd_mul_left d 15) hd hf] at h

theorem fifteen_center : unitMean 15 (w 15)=0 := by
  simpa only [mul_one] using missing_modulus (d:=1) (P:=15) (dvd_refl 15) (one_dvd _) (by decide)
    (f:=fun _ => (1:ℝ)) (fun _ => rfl)

#print axioms missing_modulus
#print axioms against_period
end Arxiv.«2501.03234».ThetaFifteenOrthogonality
