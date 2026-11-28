import ThetaWindowApproximation
import ThetaCenteredOriginalTail

/-! Unconditional first-order control at almost every starting integer with
one explicit exceptional set for all lengths, including subpolynomial ones. -/
namespace Arxiv.«2501.03234».ThetaAlmostFirstOrder
open Real Filter Finset ThetaWindowApproximation ThetaLocalPrimeCounts ThetaPrimeDensity
noncomputable section

def width (a : ℝ) (X : ℕ) := exp (a*(log (X:ℝ))^(3/4:ℝ))

def failures (P : ℕ → Prop) (n H : ℕ) : Finset ℕ := by classical exact (sample n H).filter P

theorem mem_failures {P : ℕ → Prop} {n H p : ℕ} : p∈failures P n H ↔ p∈sample n H ∧ P p := by
  classical simp [failures]

def valid (P : ℕ → Prop) (a : ℝ) (X n : ℕ) := ∀ H : ℕ,0<H → H≤X →
  ((failures P n H).card:ℝ)≤H/(width a X*log X)

private theorem generic {P : ℕ → Prop} {a : ℝ} (ha : 0<a)
    (hp : ∀ᶠ Y : ℕ in atTop, ((primeSet P Y).card:ℝ)≤Y.primeCounting*exp (-(2*a)*(log (Y:ℝ))^(3/4:ℝ))) :
    ∀ᶠ X : ℕ in atTop, ((exceptional X (valid P a X)).card:ℝ)≤12*X/width a X := by
  classical
  let f (p : ℕ) : ℝ := if P p then 1 else 0
  have hf (p : ℕ) : 0≤f p := by dsimp [f];split_ifs <;> norm_num
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hp
  filter_upwards [eventually_ge_atTop Y,eventually_ge_atTop (2:ℕ),prime_budget] with X hXY hX hπ
  let V := width a X
  have hV : 0<V := exp_pos _
  have hlog := log_pos (show (1:ℝ)<X by exact_mod_cast (show 1<X by omega))
  have h3 : X≤3*X := by omega
  have hln := log_le_log (show 0<(X:ℝ) by positivity) (Nat.cast_le.mpr h3)
  have hr := rpow_le_rpow hlog.le hln (by norm_num : (0:ℝ)≤3/4)
  have hex : exp (-(2*a)*(log ((3*X:ℕ):ℝ))^(3/4:ℝ))≤1/(V*V) := by
    change _≤1/(exp _*exp _)
    rw [←exp_add,one_div,←exp_neg]
    exact exp_le_exp.mpr (by linarith only [mul_le_mul_of_nonneg_left hr ha.le])
  have hcon := (hY (3*X) (hXY.trans h3)).trans (mul_le_mul_of_nonneg_left hex (Nat.cast_nonneg _))
  have hsum : (∑ p∈Nat.primesLE (3*X),f p)=((primeSet P (3*X)).card:ℝ) := by
    simp [f,primeSet]
  have hh := finite hX f hf (show 0≤V⁻¹ by positivity)
  rw [hsum] at hh
  have heq (n : ℕ) : (∀ H : ℕ,0<H → H≤X → avg X n H f≤V⁻¹) ↔ valid P a X n := by
    apply forall_congr';intro H
    apply imp_congr_right;intro hH;apply imp_congr_right;intro _
    have hH' : 0<(H:ℝ) := by exact_mod_cast hH
    change (log X/H)*(∑ p∈sample n H,if P p then (1:ℝ) else 0)≤V⁻¹ ↔ (failures P n H).card≤H/(V*log X)
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one,div_mul_eq_mul_div,div_le_iff₀ hH',le_div_iff₀ (mul_pos hV hlog)]
    change log X*((failures P n H).card:ℝ)≤V⁻¹*H ↔ _
    rw [inv_mul_eq_div,le_div_iff₀ hV]
    constructor <;> intro e <;> linarith only [e,mul_left_comm (log (X:ℝ)) ((failures P n H).card:ℝ) V,
      mul_right_comm (log (X:ℝ)) ((failures P n H).card:ℝ) V,mul_comm V (log (X:ℝ))]
  have eqset : exceptional X (fun n => ∀ H : ℕ,0<H → H≤X → avg X n H f≤V⁻¹)=exceptional X (valid P a X) := by
    ext n;simp only [mem_exceptional,heq]
  rw [eqset] at hh
  have hupper : V⁻¹*((exceptional X (valid P a X)).card:ℝ)≤(12*X)/(V*V) :=
    hh.trans <| (mul_le_mul_of_nonneg_left hcon hlog.le).trans <| calc
      _ = ((3*X).primeCounting*log X)/(V*V) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hπ (mul_nonneg hV.le hV.le)
  change _≤(12*X)/V
  rw [inv_mul_eq_div,div_le_div_iff₀ hV (mul_pos hV hV)] at hupper
  apply (le_div_iff₀ hV).mpr
  apply le_of_mul_le_mul_right _ hV
  linarith only [hupper]

/-- Simultaneously for every 1≤H≤X, with a stretched-exponentially small
proportion of bad starting integers. This result has no prime-distribution input. -/
theorem original {ε : ℝ} (he : 0<ε) : ∃ a : ℝ,0<a ∧ ∀ᶠ X : ℕ in atTop,
    ((exceptional X (valid (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|) a X)).card:ℝ)≤12*X/width a X := by
  obtain ⟨b,hb,hh⟩ := ThetaCenteredOriginalTail.original he
  refine ⟨b/2,half_pos hb,generic (half_pos hb) ?_⟩
  rwa [show 2*(b/2)=b by ring]


/-- A common stretched-exponential saving for failure of each integer slope
in DeepMind's odd-prime lower conjecture, uniformly over all window lengths. -/
theorem pinned : ∃ a : ℝ, 0<a ∧ ∀ k : ℕ, ∀ᶠ X : ℕ in atTop,
    ((exceptional X (valid (fun p => Odd p ∧ ¬(k:ℤ)*p<S p) a X)).card:ℝ)≤12*X/width a X := by
  classical
  obtain ⟨a,ha,hh⟩ := original (by norm_num : (0:ℝ)<1/4)
  refine ⟨a,ha,?_⟩
  intro k
  have hlog := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (4*(k:ℝ))
  filter_upwards [hh,hlog,eventually_ge_atTop (2:ℕ)] with X hx hl hX
  apply le_trans _ hx
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  obtain ⟨hstart,hbad⟩ := mem_exceptional.mp hn
  apply mem_exceptional.mpr;refine ⟨hstart,fun he => hbad ?_⟩
  intro H hH hlH
  apply le_trans _ (he H hH hlH)
  apply Nat.cast_le.mpr
  apply card_le_card;intro p hp
  obtain ⟨hs,_,hfail⟩ := mem_failures.mp hp
  refine mem_failures.mpr ⟨hs,?_⟩
  obtain ⟨hI,_,_⟩ := ThetaShortPrimeInterval.mem_primes.mp hs
  have hXp := (mem_Ico.mp hstart).1.trans (mem_Ioc.mp hI).1.le
  have hlogp := hl.trans (log_le_log (show 0<(X:ℝ) by positivity) (Nat.cast_le.mpr hXp))
  have hS : (S p:ℝ)≤(k:ℝ)*p := by exact_mod_cast (le_of_not_gt hfail)
  exact (show (1/4:ℝ)*(p:ℝ)*log p≤-((S p:ℝ)-p*log p/2) by
    nlinarith only [hS,mul_le_mul_of_nonneg_right hlogp (Nat.cast_nonneg p (α:=ℝ))]).trans (neg_le_abs _)

#print axioms pinned

#print axioms original
end
end Arxiv.«2501.03234».ThetaAlmostFirstOrder
