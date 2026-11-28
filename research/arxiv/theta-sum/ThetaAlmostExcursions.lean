import ThetaAlmostTransfer
import ThetaFullResidualSupport
import ThetaLocalIntervalTests

/-! Positive counts for every open interval of residual values on almost every
short prime window, using only a lower estimate on ordinary prime counts. -/
namespace Arxiv.«2501.03234».ThetaAlmostExcursions
open Real Finset Filter ThetaLocalIntervalTests ThetaWindowApproximation ThetaAlmostPeriodicWindows
open ThetaLocalPrimeCounts ThetaIdentityFiber ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans
open scoped Topology
noncomputable section

def bump (q r : ℕ) (y d : ℝ) (p : ℕ) :=
  selectClass r q p*tent y d (residual p)

theorem nonnegative (q r : ℕ) (y d : ℝ) (p : ℕ) : 0≤bump q r y d p := by
  unfold bump selectClass tent
  split_ifs <;> simp

private theorem bounds (q r : ℕ) (y : ℝ) {d : ℝ} (hd : 0<d) (s : Finset ℕ) :
    d/2*(hits q r y (d/2) s).card≤∑ p∈s,bump q r y d p ∧
    (∑ p∈s,bump q r y d p)≤d*(hits q r y d s).card := by
  classical
  have mem {n : ℕ} {D : ℝ} : n∈hits q r y D s ↔ n∈s ∧ n%q=r ∧ |residual n-y|<D := by
    simp [hits,cell,and_assoc]
  constructor
  · calc _ = ∑ _p∈hits q r y (d/2) s,d/2 := by simp [mul_comm]
         _ ≤ ∑ p∈hits q r y (d/2) s,bump q r y d p := by
              apply sum_le_sum;intro p hp
              obtain ⟨_,hr,hh⟩ := mem.mp hp
              simp only [bump,selectClass,hr,if_true,one_mul,tent]
              exact (show d/2≤d-|residual p-y| by linarith).trans (le_max_right ..)
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun _ hn => (mem.mp hn).1)
            (fun p _ _ => nonnegative q r y d p)
  · calc _ ≤ ∑ p∈s,if p%q=r ∧ |residual p-y|<d then d else 0 := by
            apply sum_le_sum; intro p _
            by_cases hr : p%q=r
            · simp only [bump,selectClass,hr,if_true,one_mul,true_and,tent]
              split_ifs with h
              · exact max_le hd.le (sub_le_self _ (abs_nonneg _))
              · exact max_le le_rfl (sub_nonpos.mpr (le_of_not_gt h))
            · simp [bump,selectClass,hr]
         _ = _ := by
            rw [←sum_filter,sum_const,nsmul_eq_mul,mul_comm]
            have eqn : s.filter (fun p => p%q=r ∧ |residual p-y|<d)=hits q r y d s := by
              ext n;exact mem_filter.trans mem.symm
            rw [eqn]

theorem density {θ c : ℝ} (h : Lower θ c) (hc : 0<c) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (y : ℝ) {d : ℝ} (hd : 0<d) :
    ∃ δ : ℝ, 0<δ ∧ Almost (fun X n => ∀ H : ℕ, Admits θ X H →
      δ*H/log X≤((hits q r y d (sample n H)).card:ℝ)) := by
  obtain ⟨a,ha,hglobal⟩ := ThetaFullResidualSupport.density hAP hq hr hu y (half_pos hd)
  let f := bump q r y d
  have hap : ThetaPrimeLaw.Approximable f := by
    have hl : LipschitzWith 1 (tent y d) := by simpa using lip y d 0
    exact ThetaLocalWeightedLimits.approximable hq (selectClass_mod r q)
      (fun n => by simp [selectClass];split_ifs <;> norm_num) hl
  have hm : ∀ᶠ X : ℕ in atTop,d/2*a≤primeMean f X := by
    filter_upwards [hglobal,eventually_ge_atTop (2:ℕ)] with X hh hX
    have hpr : 0<(X.primeCounting:ℝ) := by
      have hp : 0<Nat.primeCounting 2 := by decide
      exact_mod_cast hp.trans_le (Nat.monotone_primeCounting hX)
    have heq : ThetaFullResidualSupport.hits q r y (d/2) X=hits q r y (d/2) (Nat.primesLE X) := by
      ext p;simp [ThetaFullResidualSupport.hits,ThetaPrimeDensity.primeSet,hits,cell,and_assoc]
    rw [heq] at hh
    apply (le_div_iff₀ hpr).mpr
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left hh (half_pos hd).le).trans (bounds q r y hd (Nat.primesLE X)).1
  let m := d/2*a
  have hm₀ : 0 < m := by dsimp [m];positivity
  refine ⟨c*m/(4*d),by positivity,?_⟩
  apply mono (ThetaAlmostTransfer.lower h hc hAP hap (nonnegative q r y d) hm₀ hm)
  filter_upwards [eventually_ge_atTop (2:ℕ)] with X hX
  intro n _ hb H hH
  have hlog := log_pos (show (1:ℝ)<X by exact_mod_cast (show 1<X by omega))
  have hHH : 0<(H:ℝ) := by exact_mod_cast hH.1
  have hb' := (hb H hH).trans (mul_le_mul_of_nonneg_left (bounds q r y hd (sample n H)).2 (div_nonneg hlog.le hHH.le))
  apply (div_le_iff₀ hlog).mpr
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)<4*d)]
  rw [div_mul_eq_mul_div,le_div_iff₀ hHH] at hb'
  linarith only [hb']

#print axioms density
end
end Arxiv.«2501.03234».ThetaAlmostExcursions
