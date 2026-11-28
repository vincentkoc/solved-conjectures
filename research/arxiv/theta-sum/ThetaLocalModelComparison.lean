import ThetaLocalDyadicReference

/-! Normalized discrepancies for shifted periodic models and the bounded
moments of a dyadic prime sample. -/
namespace Arxiv.«2501.03234».ThetaLocalModelComparison
open Real Filter Finset ThetaLocalPrimeCounts ThetaLocalDyadicReference ThetaLocalSampledPowers
open ThetaCharacterPrimeMeans ThetaPrimeLaw ThetaDiagonalConstant ThetaPeriodMeans ThetaConditionalRows
noncomputable section

theorem full_length {X : ℕ} (hx : 1≤X) {θ : ℝ} (hθ : θ≤1) : (X:ℝ)^θ≤X := by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le (by exact_mod_cast hx : 1≤(X:ℝ)) hθ

theorem normalized {s M u ε : ℝ} (hm : 0<M) (hs : |s-M*u|≤ε*M) : |s/M-u|≤ε := by
  rw [show s/M-u=(s-M*u)/M by field_simp,abs_div,abs_of_pos hm,div_le_iff₀ hm]
  exact hs

theorem compare {θ : ℝ} (hθ : θ≤1) (h : Ordinary θ) {q : ℕ} (hq : 0<q)
    {D : ℝ} (g w : ℕ → ℝ) (hg : OnMod q g) (hw : OnMod q w)
    (hA : ∀ n, |g n|≤1) (hD : ∀ n, |w n|≤D) (k j : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∀ {Y : ℕ}, 1≤Y → (Y:ℝ)≤(log X)^j →
    ∀ N H : ℕ, H≤X → (X:ℝ)^θ≤H →
    let f (n : ℕ) := g n*(w n+residualModel Y N n)^k
    |avg X H f-avg X X f|≤ε := by
  let v (n : ℕ) := w n+diagonalConstant
  have hv : OnMod q v := fun n => congrArg (·+diagonalConstant) (hw n)
  have hbound (n : ℕ) : |v n|≤D+|diagonalConstant| :=
    (abs_add_le ..).trans (add_le_add_left (hD n) _)
  filter_upwards [original h hq g v hg hv hA hbound k j (half_pos hε),
      ThetaLocalMomentBudgets.count h,eventually_ge_atTop (1:ℕ)] with X hmodel hcount hx
  intro Y hy hcap N H hHX hlen f
  let P := q*Y.factorial
  let : NeZero P := ⟨(Nat.mul_pos hq (Nat.factorial_pos _)).ne'⟩
  let S (n : ℕ) := g n*(v n+(8/π^2)*ThetaPrimeTailTransfer.model Y N n)^k
  have heq : f=S := by funext n;dsimp [S,f,v,residualModel];rw [add_assoc]
  have hb (H : ℕ) (hH : H≤X) (hθH : (X:ℝ)^θ≤H) : |avg X H S-unitMean P S|≤ε/2 :=
    normalized (hcount H hH hθH).1 (hmodel hy hcap N H hH hθH)
  rw [heq]
  have hh := abs_sub_le (avg X H S) (unitMean P S) (avg X X S)
  rw [abs_sub_comm (unitMean P S)] at hh
  linarith only [hh,hb H hHX hlen,hb X le_rfl (full_length hx hθ)]

theorem shifted_moments (k : ℕ) (w : ℕ → ℝ) {D : ℝ} (hw : ∀ n,|w n|≤D) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop,
    (∑ p∈sample X X,|w p+residual p|^k)≤C*mass X X := by
  obtain ⟨C,hC,h⟩ := dyadic_moments k
  obtain ⟨A,hA,ha⟩ := pi_bound
  have hD := (abs_nonneg _).trans (hw 0)
  refine ⟨2^(k-1)*(C+A*D^k),by positivity,?_⟩
  filter_upwards [h,ha] with X hx hπ
  have hcard := (Nat.cast_le.mpr (card_le_card (fun _ hp => sample_sub hp (le_refl X)))).trans
    (by simpa only [Nat.primesLE_card_eq_primeCounting] using hπ : ((Nat.primesLE (2*X)).card:ℝ)≤A*mass X X)
  have H := sum_le_sum (s:=sample X X) (fun p _ =>
    (pow_le_pow_left₀ (abs_nonneg (w p+residual p)) ((abs_add_le ..).trans (add_le_add_left (hw p) _)) k).trans
      (add_pow_le hD (abs_nonneg _) k))
  rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul] at H
  nlinarith only [H,mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hcard (pow_nonneg hD k)) hx)
    (by positivity : 0≤(2:ℝ)^(k-1))]

#print axioms compare
#print axioms shifted_moments
end
end Arxiv.«2501.03234».ThetaLocalModelComparison
