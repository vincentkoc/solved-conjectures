import ThetaResonancePacking

/-! Many reciprocal-sum obstructions lie strictly below the square-root scale. -/
namespace Arxiv.«2501.03234».ThetaSubcriticalResonance
open Finset Filter Real Asymptotics ThetaResonantLengths ThetaSquareRootWindow
open ThetaManyReciprocalSums ThetaResonancePacking ThetaBourgainGaraev
noncomputable section

private theorem absorption {b α : ℝ} (hb : 0<b) (hα : 0<α) (htop : α<1/3) :
    ∀ᶠ u : ℝ in atTop, 2*(32*log u+u^α)+1 ≤
      (b/2)*u^((1:ℝ)/3)/(log u)^((8:ℝ)/3) := by
  have h := (isLittleO_log_rpow_rpow_atTop ((8:ℝ)/3) (sub_pos.mpr htop)).bound
    (by positivity : 0 < b/136)
  have hh := (isLittleO_log_rpow_atTop hα).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [h,hh,tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)]
    with u H H' hv hu
  have hu₀ : 0<u := by linarith
  have hv₀ : 0<log u := by linarith
  change ‖(log u)^((8:ℝ)/3)‖ ≤ b/136*‖u^((1:ℝ)/3-α)‖ at H
  change ‖log u‖ ≤ 1*‖u^α‖ at H'
  simp only [Real.norm_of_nonneg (rpow_nonneg hu₀.le _),Real.norm_of_nonneg (rpow_nonneg hv₀.le _),
    Real.norm_of_nonneg hv₀.le,one_mul] at H H'
  have hp := one_le_rpow hu hα.le
  have he : u^α*u^((1:ℝ)/3-α) = u^((1:ℝ)/3) := by rw [←rpow_add hu₀];congr 1;ring
  apply (le_div_iff₀ (rpow_pos_of_pos hv₀ _)).mpr
  calc
    _ ≤ (68*u^α)*(b/136*u^((1:ℝ)/3-α)) := mul_le_mul (by linarith) H
      (rpow_nonneg hv₀.le _) (by positivity)
    _ = _ := by rw [←he];ring

def family (p : ℕ) [Fact p.Prime] (B α b : ℝ) : Prop :=
  ∃ E : Finset ℕ, E ⊆ lengths p 1 ∧ separated E ∧
    (∀ n∈E, (n:ℝ) ≤ B*exp (-(log p)^α)) ∧
    b*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3) ≤ E.card

theorem trim (G₀ : (p : ℕ) → [Fact p.Prime] → Finset ℕ)
    (hsub : ∀ p : ℕ, ∀ [Fact p.Prime], G₀ p ⊆ lengths p 1) {c : ℝ} (hc : 0<c)
    (H : ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      (S p:ℝ) ≤ (p:ℝ)*log p/100 → ∃ E : Finset ℕ, E ⊆ G₀ p ∧ separated E ∧
        c*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3) ≤ E.card) :
    ∀ α : ℝ, 0<α → α<1/3 → ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ B : ℝ, 0<B → (∀ t a : ZMod p, a≠0 → ‖ThetaReciprocalCutoff.kloosterman t a‖ ≤ 2*B) →
        (S p:ℝ) ≤ (p:ℝ)*log p/100 →
        ∃ E : Finset ℕ, E ⊆ G₀ p ∧ separated E ∧
          (∀ n∈E, (n:ℝ) ≤ B*exp (-(log p)^α)) ∧
          (c/2)*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3) ≤ E.card := by
  classical
  intro α hα htop
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [H,upper_logs,hlog.eventually (absorption hc hα htop),
    (tendsto_log_atTop.comp hlog).eventually_ge_atTop 1] with p H hU hshift hv
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro B hB hK hS
  obtain ⟨F,hF,hsep,hsize⟩ := H hp ho hS
  let u := log (p:ℝ)
  let U := log B
  let z := B*exp (-u^α)
  let E := F.filter fun (n : ℕ) => (n:ℝ)≤z
  let G := F.filter fun (n : ℕ) => ¬(n:ℝ)≤z
  have hpos : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hu : 0<u := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hz : 0<z := mul_pos hB (exp_pos _)
  have hlg : log z=U-u^α := by dsimp [z,U];rw [log_mul (by positivity) (exp_ne_zero _),log_exp];ring
  change 1≤log u at hv
  have hGs : separated G := fun n m hn hm => hsep n m (mem_filter.mp hn).1 (mem_filter.mp hm).1
  have hpack := packing G hGs (show U-u^α ≤ U+32*log u by linarith [rpow_nonneg hu.le α]) (by
    intro n hn
    have hh := hU hp ho 1 B hB hK n (hsub p (hF (mem_filter.mp hn).1))
    refine ⟨hh.1,?_,hh.2⟩
    rw [←hlg]
    exact log_le_log hz (le_of_lt (lt_of_not_ge (mem_filter.mp hn).2)))
  have hd : E.card+G.card=F.card := card_filter_add_card_filter_not ..
  have hd' : (E.card:ℝ)+(G.card:ℝ)=F.card := by exact_mod_cast hd
  refine ⟨E,fun _ hn => hF (mem_filter.mp hn).1,
    fun n m hn hm => hsep n m (mem_filter.mp hn).1 (mem_filter.mp hm).1,
    fun _ hn => (mem_filter.mp hn).2,?_⟩
  change 2*(32*log u+u^α)+1 ≤ (c/2)*u^((1:ℝ)/3)/(log u)^((8:ℝ)/3) at hshift
  change c*u^((1:ℝ)/3)/(log u)^((8:ℝ)/3) ≤ _ at hsize
  change (c/2)*u^((1:ℝ)/3)/(log u)^((8:ℝ)/3) ≤ _
  rw [show c*u^((1:ℝ)/3)/(log u)^((8:ℝ)/3) =
    2*((c/2)*u^((1:ℝ)/3)/(log u)^((8:ℝ)/3)) by ring] at hsize
  have hG : (G.card:ℝ) ≤ (c/2)*u^((1:ℝ)/3)/(log u)^((8:ℝ)/3) := by
    apply le_trans _ hshift
    linarith only [hpack]
  linarith only [hsize,hd',hG]

theorem many_below_completion (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧
    ∀ α : ℝ, 0<α → α<1/3 → ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ B : ℝ, 0<B → (∀ t a : ZMod p, a≠0 → ‖ThetaReciprocalCutoff.kloosterman t a‖ ≤ 2*B) →
        (S p:ℝ) ≤ (p:ℝ)*log p/100 →
        family p B α b := by
  obtain ⟨c,hc,H⟩ := many estimate
  exact ⟨c/2,by positivity,trim (fun p _ => lengths p 1) (fun _ _ => le_rfl) hc (H 1 (by norm_num))⟩

theorem elementary_and_weil (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧
    ∀ α : ℝ, 0<α → α<1/3 → ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      (S p:ℝ) ≤ (p:ℝ)*log p/100 →
        family p ((p:ℝ)^((3:ℝ)/4)) α b ∧ (CompleteEstimate p → family p (sqrt p) α b) := by
  obtain ⟨b,hb,H⟩ := many_below_completion estimate
  refine ⟨b,hb,fun α hα htop => ?_⟩
  filter_upwards [H α hα htop] with p h
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hsmall
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  exact ⟨h hp ho _ (rpow_pos_of_pos hx _) ThetaReciprocalCutoff.kloosterman_bound hsmall,
    fun hK => h hp ho _ (sqrt_pos.mpr hx) hK hsmall⟩

#print axioms trim
#print axioms many_below_completion
#print axioms elementary_and_weil
end
end Arxiv.«2501.03234».ThetaSubcriticalResonance
