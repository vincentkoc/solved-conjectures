import ThetaBackwardInterval

/-! Two-sided theta exceptions at length x^(13/25), uniformly in residue classes. -/
namespace Arxiv.«2501.03234».ThetaShortProgressions
open Finset Filter Real ThetaBackwardInterval ThetaShortPrimeInterval ThetaStrongOriginalTail
open ThetaStrongDeviation ThetaWeilShortIntervals
noncomputable section

def deviates (ε : ℝ) (p : ℕ) := ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|

/-- The two-sided exceptional count saves every fixed logarithmic power throughout
the backward interval of length x^0.52. The sole analytic input is the complete Weil bound. -/
theorem small (weil : Weil) {ε η : ℝ} (he : 0<ε) (hη : 0<η) (k : ℕ) :
    ∀ᶠ x : ℕ in atTop, ((window x (deviates ε)).card:ℝ)≤η*width x/(log x)^k := by
  let A := 2*(2:ℝ)^k/η
  have hA : 0<A := by dsimp [A]; positivity
  have hbad := tendsto_left.eventually (original_of_bound (square_root weil) he)
  have habs := tendsto_left.eventually (absorb_log_power hA (by norm_num : (0:ℝ)<2048) k)
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hbad,habs,admissible,hlog.eventually_ge_atTop 1] with x hb ha hx hl
  obtain ⟨hwide,hlen,hhi,hl2,hl1⟩ := hx
  change 1≤log (x:ℝ) at hl
  have hlog' : 0<log (x:ℝ) := by linarith
  let F := exp (rate (left x)/2048)
  have hF : 0<F := exp_pos _
  have hW : 0≤width x := by unfold width; positivity
  have h₁ := hb (length x) (by simpa only [←sqrt_eq_rpow] using hwide) hlen
  change ((window x (deviates ε)).card:ℝ) ≤ (length x:ℝ)/log (left x)*exp (-rate (left x)/2048) at h₁
  have h₂ : ((window x (deviates ε)).card:ℝ) ≤ 2*width x/F := by
    rw [show -rate (left x)/2048= -(rate (left x)/2048) by ring,exp_neg] at h₁
    rw [div_eq_mul_inv]
    exact h₁.trans (mul_le_mul_of_nonneg_right ((div_le_self (by positivity) hl1).trans hhi) (inv_nonneg.mpr hF.le))
  have hpow : (log (x:ℝ))^k ≤ (2:ℝ)^k*(1+log (left x))^k := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ hlog'.le (by linarith only [hl2]) _
  change (2*(2:ℝ)^k/η)*(1+log (left x))^k≤F at ha
  rw [div_mul_eq_mul_div,div_le_iff₀ hη] at ha
  have hgain : 2*(log (x:ℝ))^k≤η*F := by linarith only [mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤2),ha]
  apply h₂.trans
  rw [div_le_div_iff₀ hF (pow_pos hlog' k)]
  linarith only [mul_le_mul_of_nonneg_right hgain hW]

/-- Runbo Li, arXiv:2308.04458v8, Theorem 3, specialized to integer right endpoints and
a fixed nonnegative integral power of log. The hypothesis contains no theta sums. -/
def Ordinary (K : ℕ) : Prop := ∀ᶠ x : ℕ in atTop, ∀ q a : ℕ,
    0<q → (q:ℝ)≤(log x)^K → a.Coprime q →
    (1/250:ℝ)*width x/((q.totient:ℝ)*log x)≤((window x (fun p => p ≡ a [MOD q])).card:ℝ)

theorem scaled (weil : Weil) {ε η : ℝ} (he : 0<ε) (hη : 0<η) (K : ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ q : ℕ, 0<q → (q:ℝ)≤(log x)^K →
    ((window x (deviates ε)).card:ℝ)≤η*width x/((q.totient:ℝ)*log x) := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [small weil he hη (K+1),hlog.eventually_ge_atTop 1] with x hb hL
  intro q hq hsize
  change 1≤log (x:ℝ) at hL
  have hL' : 0<log (x:ℝ) := by linarith
  have hφ : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hφq : (q.totient:ℝ)≤q := by exact_mod_cast Nat.totient_le q
  apply hb.trans
  apply div_le_div_of_nonneg_left (by unfold width; positivity) (mul_pos hφ hL')
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right (hφq.trans hsize) hL'.le

/-- Each eligible reduced residue class has an arbitrarily small proportion of exceptions,
uniformly even as the modulus grows through the full range of the ordinary prime estimate. -/
theorem relative (weil : Weil) {K : ℕ} (li : Ordinary K) {ε δ : ℝ} (he : 0<ε) (hd : 0<δ) :
    ∀ᶠ x : ℕ in atTop, ∀ q a : ℕ, 0<q → (q:ℝ)≤(log x)^K → a.Coprime q →
    ((window x (fun p => p ≡ a [MOD q] ∧ deviates ε p)).card:ℝ)≤
      δ*((window x (fun p => p ≡ a [MOD q])).card:ℝ) := by
  filter_upwards [scaled weil he (by positivity : 0<δ/250) K,li] with x hb hl
  intro q a hq hm ha
  have hsub : window x (fun p => p ≡ a [MOD q] ∧ deviates ε p)⊆window x (deviates ε) := by
    intro p hp
    obtain ⟨hi,hp,h⟩ := mem_primes.mp hp
    exact mem_primes.mpr ⟨hi,hp,h.2⟩
  apply (Nat.cast_le.mpr (card_le_card hsub)).trans ((hb q hq hm).trans ?_)
  apply le_trans _ (mul_le_mul_of_nonneg_left (hl q a hq hm ha) hd.le)
  ring_nf
  rfl

/-- Every constant below the ordinary prime-count constant survives for primes satisfying
the one-sided theta inequality in each reduced class at the original interval length. -/
theorem positive (weil : Weil) {K : ℕ} (li : Ordinary K) {c γ : ℝ}
    (hc : c<1/2) (hγ : γ<1/250) :
    ∀ᶠ x : ℕ in atTop, ∀ q a : ℕ, 0<q → (q:ℝ)≤(log x)^K → a.Coprime q →
    γ*width x/((q.totient:ℝ)*log x) ≤
      ((window x (fun p => p ≡ a [MOD q] ∧ c*p*log p<(S p:ℝ))).card:ℝ) := by
  let ε := 1/2-c
  let η := 1/250-γ
  have he : 0<ε := sub_pos.mpr hc
  have hη : 0<η := sub_pos.mpr hγ
  filter_upwards [scaled weil he hη K,li] with x hb hl
  intro q a hq hm ha
  let A := window x (fun p => p ≡ a [MOD q])
  let G := window x (fun p => p ≡ a [MOD q] ∧ c*p*log p<(S p:ℝ))
  have hsub : A⊆window x (deviates ε) ∪ G := by
    intro p hp
    obtain ⟨hi,hp,hmod⟩ := mem_primes.mp hp
    rcases lt_or_ge (c*p*log p) (S p:ℝ) with h|h
    · exact mem_union_right _ (mem_primes.mpr ⟨hi,hp,hmod,h⟩)
    · apply mem_union_left _ (mem_primes.mpr ⟨hi,hp,?_⟩)
      unfold deviates
      apply le_trans _ (neg_le_abs _)
      dsimp [ε]
      linarith only [h]
  have hcard := (Nat.cast_le (α:=ℝ)).mpr ((card_le_card hsub).trans (card_union_le ..))
  rw [Nat.cast_add] at hcard
  have h := hl q a hq hm ha
  change _≤(A.card:ℝ) at h
  have hsplit : (1/250:ℝ)*width x/((q.totient:ℝ)*log x) =
      γ*width x/((q.totient:ℝ)*log x)+η*width x/((q.totient:ℝ)*log x) := by dsimp [η];ring
  rw [hsplit] at h
  change _≤(G.card:ℝ)
  linarith only [h,hcard,hb q hq hm]

#print axioms positive
#print axioms small
#print axioms scaled
#print axioms relative
end
end Arxiv.«2501.03234».ThetaShortProgressions
