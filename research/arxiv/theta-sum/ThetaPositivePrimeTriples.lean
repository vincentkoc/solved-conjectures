import ThetaFivePrimeMoment
import ThetaWeilShortIntervals

/-! Near-central disjoint triples for the canonical integer theta sum. -/
namespace Arxiv.«2501.03234».ThetaPositivePrimeTriples
open Finset Filter Real ThetaTernaryWindows ThetaTernaryErrorBudget
open ThetaTernaryDeletion ThetaTernaryPacking ThetaTernaryTransfer ThetaTernaryIncidence
open ThetaAlmostEqualPrimeTriples ThetaFivePrimeMoment
noncomputable section

def Statement (θ ε c b C : ℝ) : Prop :=
    ∀ᶠ n : ℕ in atTop, Odd n → ∃ D : Finset Triple,
      b^2*(n:ℝ)^θ/(108*C*(1+log n)) ≤ D.card ∧
      (∀ t∈D,t.1+t.2.1+t.2.2=n ∧ t.1≠t.2.1 ∧ t.1≠t.2.2 ∧ t.2.1≠t.2.2 ∧
        ∀ p∈vertices t, p.Prime ∧ |(p:ℝ)-(n:ℝ)/3|≤(n:ℝ)^θ ∧
          c*p*log p<(S p:ℝ) ∧ |(S p:ℝ)-p*log p/2|<ε*p*log p) ∧
      ∀ t∈D,∀ u∈D,t≠u → Disjoint (vertices t) (vertices u)

theorem from_control {θ ε c b C : ℝ} (control : Control θ) (hε : 0<ε) (hc : c<1/2)
    (hb : 0<b) (hC : 0<C) (ho : Ordinary θ 3 b) (hf : FivePrimeUpper θ C) :
    Statement θ ε c b C := by
  let η := min ε (1/2-c)
  have hη : 0<η := lt_min hε (sub_pos.mpr hc)
  filter_upwards [ThetaDisjointCentralPrimeTriples.original control hη hb
    (show 0<9*C by positivity) ho (lift hf)] with n hn hodd
  obtain ⟨D,hD,hsep,hlo⟩ := hn hodd
  refine ⟨D,?_,?_,hsep⟩
  · simpa only [width,show 12*(9*C)=108*C by ring] using hlo
  intro t ht
  obtain ⟨hmem,hd⟩ := mem_filter.mp (hD ht)
  obtain ⟨ha,hb',hc',hn'⟩ := mem.mp hmem
  refine ⟨hn',hd.1,hd.2.1,hd.2.2,?_⟩
  intro p hp
  have hg : p∈selected n θ η := by
    simp only [vertices,mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl;exact ha;exact hb';exact hc'
  obtain ⟨hw,herr⟩ := mem_selected.mp hg
  obtain ⟨hpr,hwin⟩ := mem_filter.mp hw
  have hp' := (Nat.mem_primesLE.mp hpr).2
  have hp₁ : 1≤(p:ℝ) := by exact_mod_cast hp'.one_lt.le
  have hpL : 0≤(p:ℝ)*log p := mul_nonneg (Nat.cast_nonneg _) (log_nonneg hp₁)
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left ε (1/2-c)) hpL
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right ε (1/2-c)) hpL
  have h₃ := (abs_lt.mp herr).1
  change min ε (1/2-c)*(p:ℝ)*log p > _ at herr
  change -(min ε (1/2-c)*(p:ℝ)*log p) < _ at h₃
  exact ⟨hp',hwin,by linarith only [h₂,h₃],by linarith only [h₁,herr]⟩

/-- The elementary theta estimate suffices above exponent 3/4. -/
theorem original {θ ε c b C : ℝ} (hθ : 3/4<θ) (ht : θ<1) (hε : 0<ε)
    (hc : c<1/2) (hb : 0<b) (hC : 0<C) (ho : Ordinary θ 3 b) (hf : FivePrimeUpper θ C) :
    Statement θ ε c b C :=
  from_control (of_power (by norm_num) hθ ht ThetaShortPrimeInterval.elementary) hε hc hb hC ho hf

/-- From the complete Weil estimate, the theta deletion works above exponent 1/2.
The two ordinary prime-pattern estimates retain their own ranges. -/
theorem weil {θ ε c b C : ℝ} (hθ : 1/2<θ) (ht : θ<1) (w : ThetaWeilShortIntervals.Weil)
    (hε : 0<ε) (hc : c<1/2) (hb : 0<b) (hC : 0<C) (ho : Ordinary θ 3 b)
    (hf : FivePrimeUpper θ C) : Statement θ ε c b C :=
  from_control (of_power (by norm_num) hθ ht (ThetaWeilShortIntervals.square_root w)) hε hc hb hC ho hf

#print axioms from_control
#print axioms original
#print axioms weil
end
end Arxiv.«2501.03234».ThetaPositivePrimeTriples
