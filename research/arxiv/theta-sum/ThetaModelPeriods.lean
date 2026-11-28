import ThetaPrimePowerDigit
import ThetaDyadicLaw

/-! Exactly the odd prime-power digits are needed for prime-mean approximation. -/
namespace Arxiv.«2501.03234».ThetaModelPeriods
open Filter Topology Finset ThetaPrimitiveSpectrum ThetaPrimePowerDigit ThetaNaturalPrimeMeans
open ThetaPeriodMeans ThetaCharacterPrimeMeans ThetaPrimeLaw

/-- Periods that omit a fixed odd prime power have a common positive error threshold. -/
theorem digit_gap (hAP : ProgressionMangoldt) {p : ℕ} (hp : p.Prime) (ho : p≠2) (k : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ m : ℕ, 0 < m → ¬p^(k+1)∣m → ∀ g : ℕ → ℝ, OnMod m g →
      ∀ᶠ X in atTop, δ < primeMean (fun r => |residual r-g r|) X := by
  obtain ⟨χ,hχ,hodd⟩ := exists_primitive_odd hp ho k
  let : NeZero (p^(k+1)) := ⟨(pow_pos hp.pos _).ne'⟩
  have hpo := (hp.odd_of_ne_two ho).pow (n:=k+1)
  have hq : 1<p^(k+1) := one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero _)
  have hn := ((spectrum χ hχ hq hAP).2.mpr ⟨hpo,hodd⟩)
  rw [if_pos hpo] at hn
  have hpos := norm_pos_iff.mpr hn
  refine ⟨‖coefficient χ‖/2,half_pos hpos,?_⟩
  intro m hm hmiss g hg
  let : NeZero m := ⟨hm.ne'⟩
  exact model_obstruction χ hχ hpo hq hmiss hAP hg (half_lt_self hpos)

/-- Approximation to arbitrary prime-mean accuracy for each sufficiently late prescribed period. -/
def ApproximatingPeriods (m : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ j in atTop, ∃ g : ℕ → ℝ, OnMod (m j) g ∧
    ∀ᶠ X in atTop, primeMean (fun p => |residual p-g p|) X ≤ ε

private theorem necessary_power {m : ℕ → ℕ} (hm : ∀ j, 0 < m j)
    (hAP : ProgressionMangoldt) (h : ApproximatingPeriods m) {p : ℕ} (hp : p.Prime)
    (ho : p≠2) (k : ℕ) : ∀ᶠ j in atTop, p^(k+1)∣m j := by
  obtain ⟨δ,hδ,H⟩ := digit_gap hAP hp ho k
  filter_upwards [h δ hδ] with j hj
  by_contra hmiss
  obtain ⟨g,hg,he⟩ := hj
  exact (he.and (H (m j) (hm j) hmiss g hg)).exists.elim fun _ hX => hX.2.not_ge hX.1

theorem odd_moduli_of_powers {m : ℕ → ℕ}
    (h : ∀ {p : ℕ}, p.Prime → p≠2 → ∀ k : ℕ, ∀ᶠ j in atTop, p^(k+1)∣m j)
    (q : ℕ) (hq : Odd q) : ∀ᶠ j in atTop, q∣m j := by
  have sub (d : ℕ) (hd : d∈q.divisors) : ∀ᶠ j in atTop,
      (∃ p k : ℕ, p.Prime ∧ d=p^(k+1)) → d∣m j := by
    by_cases H : ∃ p k : ℕ, p.Prime ∧ d=p^(k+1)
    · obtain ⟨p,k,hp,rfl⟩ := H
      have ho : p≠2 := by
        intro he
        have hc := ((dvd_pow_self p (Nat.succ_ne_zero k)).trans (Nat.mem_divisors.mp hd).1)
        have htwo : 2 ∣ q := he ▸ hc
        have := Nat.odd_iff.mp hq
        omega
      filter_upwards [h hp ho k] with j hj
      exact fun _ => hj
    · exact .of_forall fun _ HH => (H HH).elim
  filter_upwards [(eventually_all_finset q.divisors).mpr sub] with j hj
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hd
  cases k with
  | zero => simp
  | succ k => exact hj _ (Nat.mem_divisors.mpr ⟨hd,hq.pos.ne'⟩) ⟨p,k,hp,rfl⟩


/-- A sequence permits arbitrary prime-mean accuracy iff every odd modulus eventually divides it. -/
theorem period_criterion {m : ℕ → ℕ} (hm : ∀ j, 0 < m j) (hAP : ProgressionMangoldt) :
    ApproximatingPeriods m ↔ ∀ q : ℕ, Odd q → ∀ᶠ j in atTop, q∣m j := by
  constructor
  · intro h
    exact odd_moduli_of_powers (fun hp ho k => necessary_power hm hAP h hp ho k)
  · intro h ε hε
    obtain ⟨T,V,H⟩ := residual_model_approximation hε
    obtain ⟨q,hq,hg⟩ := ThetaDyadicLaw.odd_model_period T V
    filter_upwards [h q hq] with j hj
    exact ⟨residualModel T V,onMod_lift hj hg,H⟩

/-- One family of models can be chosen independently of the requested accuracy. -/
theorem fixed_models_iff {m : ℕ → ℕ} (hm : ∀ j, 0 < m j) (hAP : ProgressionMangoldt) :
    (∃ g : ℕ → ℕ → ℝ, (∀ j, OnMod (m j) (g j)) ∧ ∀ ε : ℝ, 0<ε →
      ∀ᶠ j in atTop, ∀ᶠ X in atTop, primeMean (fun p => |residual p-g j p|) X ≤ ε) ↔
    ∀ q : ℕ, Odd q → ∀ᶠ j in atTop, q∣m j := by
  rw [←period_criterion hm hAP]
  constructor
  · rintro ⟨g,hg,h⟩ ε he
    filter_upwards [h ε he] with j hj
    exact ⟨g j,hg j,hj⟩
  · intro h
    classical
    let tol (n : ℕ) : ℝ := 1/((n:ℝ)+1)
    have H (n : ℕ) := eventually_atTop.mp (h (tol n) (by dsimp [tol]; positivity))
    choose t ht using H
    let index (j : ℕ) := Nat.findGreatest (fun n => t n ≤ j) j
    have he (j : ℕ) : ∃ g : ℕ → ℝ, OnMod (m j) g ∧ (t 0 ≤ j →
        ∀ᶠ X in atTop, primeMean (fun p => |residual p-g p|) X ≤ tol (index j)) := by
      by_cases hj : t 0 ≤ j
      · have hi : t (index j) ≤ j := Nat.findGreatest_spec (P:=fun n => t n ≤ j) (Nat.zero_le j) hj
        obtain ⟨g,hg,hg'⟩ := ht (index j) j hi
        exact ⟨g,hg,fun _ => hg'⟩
      · exact ⟨fun _ => 0,fun _ => rfl,fun hh => (hj hh).elim⟩
    choose g hg hG using he
    refine ⟨g,hg,?_⟩
    intro ε hε
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop n,eventually_ge_atTop (t n),eventually_ge_atTop (t 0)] with j hj htj h0
    have hi : n ≤ index j := Nat.le_findGreatest hj htj
    have hs : tol (index j) ≤ tol n := by
      dsimp [tol]
      gcongr
    exact (hG j h0).mono fun X hX => (hX.trans hs).trans hn.le

#print axioms fixed_models_iff

#print axioms digit_gap
#print axioms period_criterion
end Arxiv.«2501.03234».ThetaModelPeriods
