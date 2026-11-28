import Erdos478SexticEndpoints
import Erdos478SexticSplittingDegree
import Erdos478ExactEndpointCounts

/-!
# Exact prime frequencies for the sixth factorial gap

Outside two primes the endpoint count is zero, two, or six. Its first
moment is one and complete splitting has natural density one in 24.
-/

namespace Erdos478.CollisionLaw
noncomputable section
open Polynomial Finset Filter Topology SplittingDensity RootMoments SexticGap
open scoped Classical

def sexticFrequency (j : ℕ) : ℚ :=
  if j=0 then 7/12 else if j=2 then 3/8 else if j=6 then 1/24 else 0

private def coeffs (j : ℕ) : ℝ × ℝ × ℝ :=
  if j=0 then (1,-(1/2),2) else if j=2 then (0,1/2,-3) else if j=6 then (0,0,1) else (0,0,0)

private theorem sextic_indicator (j p : ℕ) [hpr : Fact p.Prime] (hp : max 719 (cutoff 6)<p) :
    event (fun p => (endpoints 6 p).card=j) p =
      (coeffs j).1 + (coeffs j).2.1 * RootMoments.roots (gapPoly 6) p +
        (coeffs j).2.2 * indicator (gapPoly 6) p := by
  have hbig : cutoff 6<p := (le_max_right ..).trans_lt hp
  have hl : 719<p := (le_max_left ..).trans_lt hp
  have hg := gap_degree (by decide : 0<6)
  have hsep := GapFamilies.separable_mod_above_resultant (gapPoly 6)
    (by rw [hg.natDegree_eq]; decide)
    (by simpa [gapPoly] using (GapFamilies.irreducible_gap_rat (by decide : 0<6)).separable)
    ((le_max_right ..).trans_lt hbig)
  have hr := count_roots _ hg.monic p hsep
  rw [← endpoint_count (by decide : 2≤6) hbig] at hr
  have hsat := saturated_iff (by decide : 2≤6) hbig
  have hs := sextic_endpoints_all_primes hpr.out
  rw [if_neg (by omega),if_neg (by omega)] at hs
  simp only [event,indicator,hr,hsat]
  rcases hs with h|h|h <;> simp only [h] <;>
    by_cases a : j=0 <;> by_cases b : j=2 <;> by_cases c : j=6 <;>
      norm_num [coeffs,a,b,c,eq_comm]

theorem sextic_count_mean (A : PrimeAverage) (j : ℕ) :
    Tendsto (fun X => A.avg X (event (fun p => (endpoints 6 p).card=j))) atTop
      (𝓝 (sexticFrequency j : ℝ)) := by
  let f := gapPoly 6
  have hg := gap_degree (by decide : 0<6)
  have hir : Irreducible (f.map (Int.castRingHom ℚ)) := by
    simpa [f,gapPoly] using GapFamilies.irreducible_gap_rat (by decide : 0<6)
  have H := split_mean A f hg.monic (hg.natDegree_eq ▸ (by decide : 0<6)) hir.separable
  rw [show Module.finrank ℚ (SplitField f)=24 from sextic_splitting_degree] at H
  let a := (coeffs j).1
  let b := (coeffs j).2.1
  let c := (coeffs j).2.2
  have eq : a*1+b*1+c*((24:ℕ):ℝ)⁻¹=(sexticFrequency j:ℝ) := by
    by_cases h : j=0 <;> by_cases h' : j=2 <;> by_cases h'' : j=6 <;>
      norm_num [a,b,c,coeffs,sexticFrequency,h,h',h'']
  apply mean_of_change A (b:=a • (1:ℕ→ℝ) + b • RootMoments.roots f + c • indicator f) (max 719 (cutoff 6))
  · intro p hp hpr
    let : Fact p.Prime := ⟨hpr⟩
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.one_apply,mul_one] using sextic_indicator j p hp
  · rw [← eq]
    simpa only [map_add,map_smul,smul_eq_mul] using
      (((constant_mean A).const_mul a).add ((first_mean A f hg.monic hir).const_mul b)).add (H.const_mul c)

#print axioms sextic_count_mean
end
end Erdos478.CollisionLaw
