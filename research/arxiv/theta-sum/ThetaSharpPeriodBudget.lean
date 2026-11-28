import ThetaPeriodBudget
import ThetaMissingPrimeBand
import ThetaConductorLayerLower
import ThetaPrimitiveCount

/-! Matching lower bound for prime theta prediction at bounded period size. -/
namespace Arxiv.«2501.03234».ThetaPeriodBudget
open Finset Filter Topology ThetaNaturalPrimeMeans ThetaFiniteProjection ThetaLevelCoefficients
open ThetaSpectralVariance ThetaFullVarianceTail ThetaConductorLayerLower ThetaMissingPrimeBand
noncomputable section

private def primeLayer (p : ℕ) : Finset Mode := if h : p=0 then ∅ else @layer p ⟨h⟩
private lemma primeLayer_eq (p : ℕ) [NeZero p] : primeLayer p=layer p := dif_neg (NeZero.ne _)

private lemma mass_prime {p : ℕ} (hp : p.Prime) (hh : 1025≤p) :
    1/(1048576*(p:ℝ)^2)≤∑ u∈primeLayer p,u.mass := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [primeLayer_eq]
  apply mass p (hp.odd_of_ne_two (by omega)) (by omega)
  simp only [ThetaPrimitiveCount.defect,hp.primeFactors,sum_singleton]
  have hr : (1025:ℝ)≤p := by exact_mod_cast hh
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

private lemma lower_band {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) {Y m : ℕ} [NeZero m] (hY : 1025≤Y)
    (hc : (Y:ℝ)≤((band Y m).card:ℝ)*Real.log Y) :
    1/((1048576*128^2)*(Y:ℝ)*Real.log Y)≤V-energy m := by
  classical
  let s := band Y m
  let t := s.biUnion primeLayer
  have hs {p : ℕ} (h : p∈s) : p.Prime ∧ Y<p ∧ p≤128*Y ∧ ¬p∣m := by
    obtain ⟨h₀,h₁,h₂⟩ := mem_filter.mp h
    exact ⟨Nat.prime_of_mem_primesLE h₀,h₁,Nat.le_of_mem_primesLE h₀,h₂⟩
  have hm {p : ℕ} (hp : p∈s) {u : Mode} (h : u∈primeLayer p) : u.modulus=p := by
    let : NeZero p := ⟨(hs hp).1.ne_zero⟩
    rw [primeLayer_eq] at h; exact mem_layer h
  have he : ∑ u∈t,u.mass = ∑ p∈s,∑ u∈primeLayer p,u.mass := by
    apply sum_biUnion
    intro p hp q hq hne
    apply disjoint_left.mpr; intro u hu hv
    exact hne ((hm hp hu).symm.trans (hm hq hv))
  have hmiss : ∀ u∈t, ¬u.modulus∣m := by
    intro u hu; obtain ⟨p,hp,hu⟩ := mem_biUnion.mp hu
    rw [hm hp hu]; exact (hs hp).2.2.2
  have H := ThetaFullVarianceTail.missing_mass hV hAP m
  have hsum := H.summable.sum_le_tsum t (fun u _ => by split_ifs; exact le_rfl; exact sq_nonneg _)
  rw [H.tsum_eq] at hsum
  have hE : ∑ u∈t,u.mass≤V-energy m := by
    apply le_trans _ hsum; apply sum_le_sum
    intro u hu; rw [if_neg (hmiss u hu)]
  let A : ℝ := 1048576*128^2
  have hA : 0<A := by dsimp [A]; norm_num
  have hy : (1:ℝ)<Y := by exact_mod_cast (show 2≤Y by omega)
  have hy' : 0<(Y:ℝ) := by linarith
  have hl := Real.log_pos hy
  have hrow {p} (hp : p∈s) :
      1/(A*(Y:ℝ)^2)≤∑ u∈primeLayer p,u.mass := by
    have ⟨hpr,hlo,hhi,_⟩ := hs hp
    apply le_trans _ (mass_prime hpr (by omega))
    apply one_div_le_one_div_of_le (by have := hpr.pos; positivity)
    have hr : (p:ℝ)≤128*Y := by exact_mod_cast hhi
    dsimp [A]; nlinarith only [pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) p) hr 2]
  have hproj : (s.card:ℝ)/(A*(Y:ℝ)^2) ≤ V-energy m := calc
    _ = ∑ _∈s,1/(A*(Y:ℝ)^2) := by simp [div_eq_mul_inv]
    _ ≤ _ := (sum_le_sum (fun _ hp => hrow hp)).trans (he ▸ hE)
  apply le_trans _ hproj
  change 1/(A*(Y:ℝ)*Real.log Y)≤_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  change (Y:ℝ)≤(s.card:ℝ)*Real.log Y at hc
  nlinarith only [mul_le_mul_of_nonneg_left hc (mul_nonneg hA.le hy'.le)]

/-- Every modulus of logarithm at most 6Y leaves variance of order at least
1/(Y log Y); the single period lcm(1,...,Y) attains this order. -/
theorem period_budget {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Y : ℕ in atTop,
      (∀ m : ℕ, [NeZero m] → Real.log m≤6*Y →
        1/((1048576*128^2)*(Y:ℝ)*Real.log Y)≤V-energy m) ∧
      (Real.log (Nat.lcmUpto Y)≤6*Y ∧ V-energy (Nat.lcmUpto Y)≤C/((Y:ℝ)*Real.log Y)) := by
  obtain ⟨C,hC,H⟩ := lcm_prediction hV hAP
  refine ⟨C,hC,?_⟩
  filter_upwards [H,omitted,eventually_ge_atTop 1025] with Y hy ho hY
  exact ⟨fun m _ hm => lower_band hV hAP hY (ho m (NeZero.pos m) hm),hy⟩

end
end Arxiv.«2501.03234».ThetaPeriodBudget
#print axioms Arxiv.«2501.03234».ThetaPeriodBudget.period_budget
