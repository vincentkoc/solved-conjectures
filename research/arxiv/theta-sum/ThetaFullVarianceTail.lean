import ThetaSpectralVariance

/-! Explicit conductor cutoff for the full limiting prime theta variance. -/
namespace Arxiv.«2501.03234».ThetaFullVarianceTail
open Finset Filter Topology ThetaLevelCoefficients ThetaSpectralVariance
open ThetaNaturalPrimeMeans ThetaFiniteProjection
noncomputable section

local instance (n : ℕ) : NeZero n.factorial := ⟨(Nat.factorial_pos _).ne'⟩

/-- All primitive modes of conductor at most the chosen cutoff. -/
def through (Y : ℕ) : Finset Mode := by classical exact (modesAt Y.factorial).filter (fun u => u.modulus≤Y)

theorem mem_through (u : Mode) (Y : ℕ) : u∈through Y ↔ u.modulus≤Y := by
  classical
  simp only [through,mem_filter,mem_modesAt]
  exact ⟨And.right,fun h => ⟨Nat.dvd_factorial u.positive h,h⟩⟩

/-- Sum a conductor-wise finite majorant against the full Parseval expansion. -/
theorem cutoff_of_majorant {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) (Y : ℕ) {A : ℝ} (f : ℕ → ℝ)
    (hf : ∀ q, Y<q → ∀ t : Finset Mode, (∀ u∈t,u.modulus=q) → ∑ u∈t,u.mass ≤ f q)
    (hb : ∀ c : Finset ℕ, (∀ q∈c,Y<q) → ∑ q∈c,f q ≤ A) :
    ∑ u∈through Y,u.mass ≤ V ∧ V ≤ ∑ u∈through Y,u.mass+A := by
  classical
  have H := parseval hV hAP
  refine ⟨H.tsum_eq ▸ H.summable.sum_le_tsum (through Y) (fun u _ => sq_nonneg _),?_⟩
  apply le_of_tendsto H
  filter_upwards [eventually_ge_atTop (through Y)] with s hs
  let t := s \ through Y
  let c := t.image Mode.modulus
  have hyq (q : ℕ) (hq : q∈c) : Y<q := by
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
    exact lt_of_not_ge (fun h => (mem_sdiff.mp hu).2 ((mem_through u Y).mpr h))
  have htot : ∑ u∈t,u.mass ≤ A := by
    calc _ = ∑ q∈c,∑ u∈t with u.modulus=q,u.mass :=
               (sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem Mode.modulus hi) Mode.mass).symm
         _ ≤ ∑ q∈c,f q := sum_le_sum fun q hq => hf q (hyq q hq) _ (fun _ hu => (mem_filter.mp hu).2)
         _ ≤ _ := hb c hyq
  have he := sum_sdiff hs (f:=Mode.mass)
  change ∑ u∈t,u.mass+∑ u∈through Y,u.mass=∑ u∈s,u.mass at he
  linarith

/-- The variance left by a modulus is precisely the mass of its missing conductors. -/
theorem missing_mass {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) (m : ℕ) [NeZero m] :
    HasSum (fun u : Mode => if u.modulus∣m then 0 else u.mass) (V-energy m) := by
  classical
  let f (u : Mode) := if u∈modesAt m then u.mass else 0
  have H : HasSum f (∑ u∈modesAt m,f u) := hasSum_sum_of_ne_finset_zero (by
    intro u hu; simp only [f,if_neg hu])
  have he : ∑ u∈modesAt m,f u=energy m := by
    rw [←sum_modes m hAP]
    exact sum_congr rfl (fun u hu => if_pos hu)
  rw [he] at H
  apply ((parseval hV hAP).sub H).congr_fun
  intro u
  by_cases h : u.modulus∣m <;> simp [f,mem_modesAt,h]

#print axioms missing_mass
#print axioms cutoff_of_majorant
end
end Arxiv.«2501.03234».ThetaFullVarianceTail
