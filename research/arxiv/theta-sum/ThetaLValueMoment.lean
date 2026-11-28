import ThetaFourthMoment
import ThetaConductorDecay
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Uniform fourth moment at one over the nonprincipal characters of each conductor. -/
namespace Arxiv.«2501.03234».ThetaLValueMoment
open Finset Complex DirichletCharacter ThetaFourthMoment
noncomputable section
variable {q : ℕ} [NeZero q]
local notation "U" => (ZMod q)ˣ
private def b (n : ℕ) : ℝ := (n:ℝ)^(-(1/3):ℝ)

private theorem cube (n : ℕ) : b n^3=(n:ℝ)⁻¹ := by
  rw [b,←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num [Real.rpow_neg_one]

private theorem fourth (n : ℕ) : b n^4=(n:ℝ)^(-(4/3):ℝ) := by
  rw [b,←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

/-- A conductor-independent fourth-root coefficient mass. -/
def H : ℝ := ∑' n : ℕ,(n:ℝ)^(-(4/3):ℝ)

theorem H_bound : H≤4 := by
  let f (x : ℝ) := x^(-(4/3):ℝ)
  have hs : Summable (fun n : ℕ => f n) := Real.summable_nat_rpow.mpr (by norm_num)
  apply le_of_tendsto hs.hasSum.tendsto_sum_nat
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  obtain ⟨k,rfl⟩ : ∃ k,N=k+2 := ⟨N-2,by omega⟩
  have ha : AntitoneOn f (Set.Icc (1:ℝ) (1+k)) :=
    fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by norm_num)
  have hi := ha.sum_le_integral
  have he : (0:ℝ)∉Set.uIcc (1:ℝ) (1+k) := by
    rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg k))]
    simp
  dsimp only [f] at hi
  rw [integral_rpow (Or.inr ⟨by norm_num,he⟩)] at hi
  norm_num [Real.one_rpow] at hi
  change ∑ i∈range (k+2),f i ≤ 4
  rw [sum_range_succ',sum_range_succ']
  have h0 : f 0=0 := Real.zero_rpow (by norm_num)
  have h1 : f 1=1 := Real.one_rpow _
  simp only [Nat.cast_zero,Nat.cast_one,Nat.cast_add,h0,h1,zero_add,add_zero]
  have hsum : (∑ i∈range k,f ((i:ℝ)+1+1))=∑ i∈range k,(1+((i:ℝ)+1))^(-(4/3):ℝ) := by
    apply sum_congr rfl
    intro i _; dsimp only [f]; congr 1; ring
  rw [hsum]
  nlinarith [Real.rpow_nonneg (show (0:ℝ)≤1+k by positivity) (-(1/3):ℝ)]

private theorem harmonic_series (χ : DirichletCharacter ℂ q) :
    transform (fun u : U => b (u:ZMod q).val^3) χ = ∑ n∈range q,χ (n:ZMod q)/(n:ℂ) := by
  classical
  rw [transform]
  simp_rw [cube,ofReal_inv,ofReal_natCast]
  have h := ThetaReciprocalFibers.unit_sum_nat (n:=q) (fun n => χ (n:ZMod q)/(n:ℂ))
  simp only [ZMod.natCast_zmod_val] at h
  rw [←h.trans (sum_subset (filter_subset ..) (by
    intro n hn hnon
    have hnc : ¬n.Coprime q := fun hc => hnon (mem_filter.mpr ⟨hn,hc⟩)
    rw [χ.map_nonunit (fun hu => hnc ((ZMod.isUnit_iff_coprime n q).mp hu)),zero_div]))]
  simp only [div_eq_inv_mul]

private theorem coeff_mass : ∑ u : U,b (u:ZMod q).val^4 ≤ H := by
  rw [ThetaReciprocalFibers.unit_sum_nat (fun n => b n^4)]
  simp_rw [fourth]
  apply Summable.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact Real.summable_nat_rpow.mpr (by norm_num)

theorem moment (s : Finset (DirichletCharacter ℂ q)) (hs : ∀ χ∈s,χ≠1) :
    ∑ χ∈s, ‖LFunction χ 1‖^4 ≤ q.totient*(8*(H^3+1)) := by
  classical
  let T (χ : DirichletCharacter ℂ q) := transform (fun u : U => b (u:ZMod q).val^3) χ
  have h₁ (χ) (hχ : χ∈s) : ‖LFunction χ 1‖^4 ≤ 8*(‖T χ‖^4+1) := by
    have h := ThetaCharacterHarmonicLimit.harmonic_error χ (hs χ hχ) (NeZero.pos q)
    have hq : (q:ℝ)≠0 := by exact_mod_cast NeZero.ne q
    rw [div_self hq,←harmonic_series] at h
    have ht := norm_add_le (LFunction χ 1-T χ) (T χ)
    rw [sub_add_cancel] at ht
    have hb : ‖LFunction χ 1‖ ≤ ‖T χ‖+1 := by change ‖LFunction χ 1-T χ‖≤1 at h; linarith
    apply (pow_le_pow_left₀ (norm_nonneg _) hb 4).trans
    nlinarith only [sq_nonneg ((‖T χ‖-1)*(‖T χ‖+1)), sq_nonneg ((‖T χ‖-1)*‖T χ‖),
      sq_nonneg (‖T χ‖-1)]
  have hf := fourth_bound (fun u : U => b (u:ZMod q).val)
  have hu : ∑ χ∈s,‖T χ‖^4 ≤ (q.totient:ℝ)*H^3 := by
    apply (sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun _ _ _ => by positivity)).trans
    apply hf.trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) coeff_mass 3)
      (Nat.cast_nonneg _)
  have hc : (s.card:ℝ)≤q.totient := by
    have h := card_le_univ s
    rw [←Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q] at h
    exact_mod_cast h
  apply (sum_le_sum h₁).trans
  rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one]
  linarith

#print axioms H_bound
#print axioms moment
end
end Arxiv.«2501.03234».ThetaLValueMoment
