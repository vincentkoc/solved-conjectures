import ThetaFullResidualSupport
import ThetaLagSignCounts

/-! Positive close-pair excess for every bounded score taking value one
throughout a prescribed open residual interval in a reduced progression. -/
namespace Arxiv.«2501.03234».ThetaLocalMarkedCorrelations
open Real Filter Finset ThetaNaturalPrimeMeans ThetaPrimeDensity ThetaCharacterPrimeMeans
open ThetaFullResidualSupport ThetaPeriodicCorrelationWitness ThetaClassConcentration
open ThetaPrimeLagBounds ThetaLogarithmicLags
open scoped Topology
noncomputable section

private theorem score_sum (X D a : ℕ) (y d : ℝ) (f : ℕ → ℝ) (hb : ∀ n,|f n|≤1)
    (hf : ∀ p,p.Prime → p%D=a → |residual p-y|<d → f p=1) :
    2*((hits D a y d X).card:ℝ)-((primeSet (fun p => p%D=a) X).card:ℝ)≤
      ∑ p∈primeSet (fun p => p%D=a) X,f p := by
  classical
  let s := primeSet (fun p => p%D=a) X
  have h (p : ℕ) (hp : p∈s) : 2*(if |residual p-y|<d then (1:ℝ) else 0)-1≤f p := by
    obtain ⟨hp,ha⟩ : p∈Nat.primesLE X ∧ p%D=a := by simpa only [s,primeSet,mem_filter] using hp
    split_ifs with hh
    · rw [hf p (Nat.mem_primesLE.mp hp).2 ha hh];norm_num
    · have := (abs_le.mp (hb p)).1;linarith
  have heq : s.filter (fun p => |residual p-y|<d)=hits D a y d X := by
    ext p;simp only [s,hits,primeSet,mem_filter,and_assoc]
  simpa only [sum_sub_distrib,←mul_sum,sum_boole,sum_const,nsmul_eq_mul,mul_one,heq] using sum_le_sum h

theorem bounded_second (hAP : ProgressionMangoldt) {f : ℕ → ℝ} (hf : ∀ p,|f p|≤1) :
    ∀ᶠ X : ℕ in atTop,(∑ p∈Nat.primesLE X,(f p)^2)*log X≤2*X := by
  filter_upwards [(pnt hAP).eventually_lt_const (by norm_num : (1:ℝ)<2),eventually_ge_atTop (2:ℕ)] with X hh hx
  have hx' : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := (log_pos (show (1:ℝ)<X by exact_mod_cast hx)).le
  have hsq (p : ℕ) : (f p)^2≤1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hf p) 2
  have hs := sum_le_sum (s:=Nat.primesLE X) (fun p _ => hsq p)
  simp only [sum_const,nsmul_eq_mul,mul_one,Nat.primesLE_card_eq_primeCounting] at hs
  exact (mul_le_mul_of_nonneg_right hs hl).trans ((div_lt_iff₀ hx').mp hh).le

theorem scores (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q)
    (hu : r.Coprime q) (y : ℝ) {d : ℝ} (hd : 0<d) :
    ∃ D : ℕ,0<D ∧ q∣D ∧ ∃ c : ℝ,0<c ∧ ∀ f : ℕ → ℝ,(∀ p,|f p|≤1) →
      (∀ p,p.Prime → p%q=r → |residual p-y|<d → f p=1) → Scales D c f := by
  classical
  obtain ⟨T,_,hD,a,ha,hu',har,H⟩ := refinement hAP hq hr hu y hd (by norm_num : (0:ℝ)<1/4) 0
  let D := m T
  have hD' : 0<D := ThetaCompactModulus.positive T
  let v (p : ℕ) : ℝ := if p%D=a then 1 else 0
  let b : ℝ := 1/(2*(D.totient:ℝ))
  have hφ : 0<(D.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hD'
  have hb : 0<b := by dsimp [b];positivity
  have hlow := (prime_count_of_mangoldt (hAP hD' hu' ha)).eventually_const_lt
    (show b<1/(D.totient:ℝ) by dsimp [b];apply one_div_lt_one_div_of_lt hφ;linarith)
  refine ⟨D,hD',hD,(b/2)^2/12,by positivity,?_⟩
  intro f hb' hf
  apply of_witness (half_pos hb) (by norm_num : (0:ℝ)<2)
    (v:=v) (fun n => by dsimp [v];split_ifs <;> norm_num)
    (fun n j => by simp [v,Nat.add_mul_mod_self_left]) _ (bounded_second hAP hb')
  filter_upwards [H,hlow,eventually_ge_atTop (2:ℕ)] with X hh hlow hx
  have hx' : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := (log_pos (show (1:ℝ)<X by exact_mod_cast hx)).le
  have hmain := score_sum X D a y d f hb' (fun p hp hres => hf p hp (by
    rw [←Nat.mod_mod_of_dvd p hD,hres,har]))
  change (1-1/4:ℝ)*((primeSet (fun n => n%D=a) X).card:ℝ)≤((hits D a y d X).card:ℝ) at hh
  have hs : ((primeSet (fun n => n%D=a) X).card:ℝ)/2≤∑ p∈primeSet (fun n => n%D=a) X,f p := by linarith
  simp only [v,ite_mul,one_mul,zero_mul,←sum_filter]
  have hset : (Nat.primesLE X).filter (fun n => n%D=a)=primeSet (fun n => n%D=a) X := by
    ext p;simp only [primeSet,mem_filter]
  rw [hset]
  nlinarith only [((lt_div_iff₀ hx').mp hlow).le,mul_le_mul_of_nonneg_right
    (hs.trans (le_abs_self _)) hl]

#print axioms scores
end
end Arxiv.«2501.03234».ThetaLocalMarkedCorrelations
