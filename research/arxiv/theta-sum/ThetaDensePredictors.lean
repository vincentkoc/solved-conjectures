import ThetaPredictionSteps
import ThetaReflectedWindowMeans

/-! Interpolation between extreme arithmetic predictors inside an arbitrary
prescribed progression. -/
namespace Arxiv.«2501.03234».ThetaDensePredictors
open Real Filter Finset ThetaPredictionSteps ThetaClassConcentration ThetaUniformPrimePrediction
open ThetaSmoothConditionalModel ThetaPrimeTailTransfer ThetaIdentityFiber ThetaConditionalRows
open ThetaDiagonalConstant ThetaNaturalPrimeMeans
noncomputable section

theorem extremes (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hc : r.Coprime q)
    (B : ℝ) {z : ℝ} (hz : |z|=1) : ∀ᶠ T : ℕ in atTop, q∣m T ∧
    ∃ a< m T, a.Coprime (m T) ∧ a%q=r ∧ B≤z*prediction T a := by
  obtain ⟨η,hη,H⟩ := ThetaReflectedWindowMeans.uniform
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hquad := (tendsto_pow_atTop (n:=2) (by decide)).comp hl
  let c := 8/π^2
  have hcp : 0<c := by dsimp [c];positivity
  filter_upwards [H,((tendsto_const_mul_atTop_of_pos hη).mpr hl).eventually_ge_atTop (log q),
    hquad.eventually_ge_atTop (64*(B+|diagonalConstant|+1)/c)] with T hmodels hqT hlarge
  obtain ⟨hm,hd,a,ha,hu,har,hp⟩ := hmodels q r hq hr hc hqT z hz
  refine ⟨hd,a,ha,hu,har,?_⟩
  obtain ⟨Y,hY,h'⟩ := ((eventually_ge_atTop (m T)).and (calibrated hAP ha hu (by norm_num : (0:ℝ)<1))).exists
  obtain ⟨V,hV,H'⟩ := ((eventually_ge_atTop (max (m T) 3)).and h').exists
  have hv := hp Y hY V hV
  let A := cond (m T) a Y (standardWindow V)
  change (log T)^2/64≤z*A at hv
  have HE := (abs_le.mp H')
  have hlimit : B+|diagonalConstant|+1≤c*((log T)^2/64) := by
    change 64*(B+|diagonalConstant|+1)/c≤(log T)^2 at hlarge
    have HH := (div_le_iff₀ hcp).mp hlarge
    linarith only [HH]
  have hh := hlimit.trans (mul_le_mul_of_nonneg_left hv hcp.le)
  change -(1:ℝ)≤prediction T a-(diagonalConstant+c*A) ∧ prediction T a-(diagonalConstant+c*A)≤1 at HE
  rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp hz with h|h <;> subst z
  · simp only [one_mul] at hh ⊢;linarith only [hh,HE.1,neg_abs_le diagonalConstant]
  · simp only [neg_one_mul,mul_neg] at hh ⊢;linarith only [hh,HE.2,le_abs_self diagonalConstant]

private theorem discrete {f : ℕ → ℝ} {a ε : ℝ} {T U : ℕ} (hlo : f T<a)
    (hhi : a≤f U) (hTU : T≤U) (jump : ∀ j, T≤j → j < U → |f (j+1)-f j|≤ε) :
    ∃ j, T≤j ∧ j≤U ∧ |f j-a|≤ε := by
  classical
  have ex : ∃ j, T≤j ∧ a≤f j := ⟨U,hTU,hhi⟩
  let j := Nat.find ex
  obtain ⟨hT,hj⟩ := Nat.find_spec ex
  have hU : j≤U := Nat.find_min' ex ⟨hTU,hhi⟩
  have htj : T<j := lt_of_le_of_ne hT (fun e => hlo.not_ge (e ▸ hj))
  have hdiff : j-1+1=j := by omega
  have prev : f (j-1)<a := by
    by_contra! hn
    exact (Nat.find_min ex (show j-1<j by omega)) ⟨by omega,hn⟩
  have H := jump (j-1) (by omega) (by omega)
  rw [hdiff] at H
  refine ⟨j,hT,hU,?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hj)]
  linarith only [(abs_le.mp H).2,prev]

theorem dense (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hc : r.Coprime q)
    (y : ℝ) {ε : ℝ} (he : 0<ε) (N : ℕ) :
    ∃ T≥N, q∣m T ∧ ∃ a< m T, a.Coprime (m T) ∧ a%q=r ∧ |prediction T a-y|≤ε := by
  obtain ⟨J,hjumps⟩ := eventually_atTop.mp (small_jumps hAP he)
  obtain ⟨T,hT,hd,n,hn,hnc,hnr,hlo⟩ := ((eventually_ge_atTop (max J N)).and
    (extremes hAP hq hr hc (1-y) (z:=-1) (by norm_num))).exists
  have hm := ThetaCompactModulus.positive T
  obtain ⟨U,hU,_,a,ha,hac,han,hhi⟩ := ((eventually_ge_atTop T).and
    (extremes hAP hm hn hnc y (z:=1) (by norm_num))).exists
  change a%m T=n at han
  let f (j : ℕ) := prediction j (a%m j)
  have fT : f T<y := by dsimp only [f];rw [han];linarith only [hlo]
  have fU : y≤f U := by dsimp only [f];rw [Nat.mod_eq_of_lt ha];simpa only [one_mul] using hhi
  have cop (j : ℕ) (hj : j≤U) : (a%m j).Coprime (m j) := by
    change Nat.gcd (a%m j) (m j)=1
    rw [←Nat.gcd_rec]
    exact (hac.coprime_dvd_right (divides hj)).symm
  have H := discrete fT fU hU (fun j ht hju => by
    have H := hjumps j ((le_max_left ..).trans (hT.trans ht)) _ (Nat.mod_lt a (ThetaCompactModulus.positive (j+1)))
      (cop (j+1) (by omega))
    simpa only [f,Nat.mod_mod_of_dvd _ (divides (Nat.le_succ j))] using H)
  obtain ⟨j,ht,hj,H⟩ := H
  have hqj := hd.trans (divides ht)
  refine ⟨j,(le_max_right ..).trans (hT.trans ht),hqj,a%m j,Nat.mod_lt _ (ThetaCompactModulus.positive _),cop _ hj,?_,H⟩
  rw [Nat.mod_mod_of_dvd _ hqj,←Nat.mod_mod_of_dvd a hd,han,hnr]

#print axioms extremes
#print axioms dense
end
end Arxiv.«2501.03234».ThetaDensePredictors
