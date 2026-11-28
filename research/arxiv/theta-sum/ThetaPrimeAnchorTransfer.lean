import ThetaPrimeStartDensity
import ThetaLocalIntervalTests
import ThetaAlmostPeriodicWindows

/-! Moving a start a small polynomial distance changes a scaled empirical
prime sum by at most the two boundary intervals. -/
namespace Arxiv.«2501.03234».ThetaPrimeAnchorTransfer
open Real Finset Filter ThetaWindowApproximation ThetaAlmostPeriodicWindows ThetaPrimeStartDensity
open ThetaLocalPrimeCounts ThetaShortPrimeInterval ThetaCharacterPrimeMeans
noncomputable section

def Controlled (f : ℕ → ℝ) := ∃ B : ℝ,0<B ∧ ∃ k : ℕ,∀ᶠ X : ℕ in atTop,
  ∀ p : ℕ,p.Prime → X≤p → p≤3*X → |f p|≤B*(log X)^k

theorem bounded {f : ℕ → ℝ} {B : ℝ} (h : ∀ p, |f p|≤B) : Controlled f := by
  refine ⟨|B|+1,by positivity,0,Eventually.of_forall ?_⟩
  intro X p _ _ _
  rw [pow_zero,mul_one];linarith only [h p,le_abs_self B]

private theorem strip {X n j H K : ℕ} (hx : 2≤X) (hn : X≤n) (hnj : n≤j)
    (hj : j≤2*X) (hk : j≤n+K) (hH : 0<H) (hh : H≤X)
    {B : ℝ} (hB : 0≤B) {f : ℕ → ℝ} (hf : ∀ p : ℕ,p.Prime → X≤p → p≤3*X → |f p|≤B) :
    |avg X n H f-avg X j H f|≤2*K*B*log X/H := by
  classical
  let F (p : ℕ) := if p.Prime then f p else 0
  have eqsum (a b : ℕ) : (∑ p∈sample a b,f p)=∑ p∈Ico (a+1) (a+b+1), F p := by
    dsimp only [F];rw [←sum_filter];congr 1;ext p
    simp only [sample,mem_primes,mem_Ioc,mem_filter,mem_Ico,and_true]
    aesop (add safe (by omega))
  let tail (a : ℕ) := ∑ p∈range (a+1),F p
  have repr {a b : ℕ} (hab : a≤b) : (∑ p∈Ico (a+1) (b+1),F p)=tail b-tail a :=
    eq_sub_of_add_eq' (sum_range_add_sum_Ico F (Nat.succ_le_succ hab))
  have bound {a b : ℕ} (hab : a≤b) (ha : X≤a) (hb : b≤3*X) (hlen : b≤a+K) :
      |tail b-tail a|≤K*B := by
    rw [←repr hab]
    calc _ ≤ ∑ p∈Ico (a+1) (b+1),|F p| := abs_sum_le_sum_abs ..
         _ ≤ ∑ _p∈Ico (a+1) (b+1),B := sum_le_sum (fun p hp => by
           obtain ⟨h₁,h₂⟩ := mem_Ico.mp hp
           dsimp only [F];split_ifs with h
           · exact hf p h (by omega) (by omega)
           · simpa using hB)
         _ ≤ _ := by simp only [sum_const,nsmul_eq_mul];apply mul_le_mul_of_nonneg_right _ hB
                     exact_mod_cast (show (Ico (a+1) (b+1)).card≤K by rw [Nat.card_Ico];omega)
  have h₁ := bound hnj hn (by omega) hk
  have h₂ := bound (Nat.add_le_add_right hnj H) (by omega) (by omega) (by omega)
  have hdiff : |(∑ p∈sample n H,f p)-(∑ p∈sample j H,f p)|≤2*K*B := by
    rw [eqsum,eqsum,repr (by omega),repr (by omega)]
    rw [show tail (n+H)-tail n-(tail (j+H)-tail j)=(tail j-tail n)-(tail (j+H)-tail (n+H)) by ring]
    exact (abs_sub ..).trans (by linarith only [h₁,h₂])
  rw [avg,avg,←mul_sub,abs_mul,abs_of_nonneg (div_nonneg (log_nonneg
    (by exact_mod_cast (show 1≤X by omega))) (Nat.cast_nonneg _))]
  apply (mul_le_mul_of_nonneg_left hdiff (div_nonneg (log_nonneg
    (by exact_mod_cast (show 1≤X by omega))) (Nat.cast_nonneg _))).trans_eq
  ring

theorem shift {θ : ℝ} (ht : 0<θ) (ht' : θ≤1) {f : ℕ → ℝ} (hf : Controlled f) {t : ℝ} (hpos : 0<t) :
    ∀ᶠ X : ℕ in atTop,∀ n j : ℕ,X≤n → n≤j → j≤2*X → j≤n+radius (θ/2) X →
      ∀ H : ℕ,Admits θ X H → |avg X n H f-avg X j H f|≤t := by
  obtain ⟨B,hB,k,hf⟩ := hf
  let α := θ/2
  have ha : 0<α := half_pos ht
  have hb : α<1 := by dsimp [α];linarith
  have hlogs := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (ThetaLocalExcursionScales.logs ha
    (show 0<4*B/t by positivity) (k+1))
  filter_upwards [hf,hlogs,radius_bounds ha hb (by norm_num : (0:ℝ)<1),eventually_ge_atTop (2:ℕ)] with X hf hL hR hx
  intro n j hn hj hhi hk H hH
  have hl := log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  have hX : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  apply (strip hx hn hj hhi hk hH.1 hH.2.1 (mul_nonneg hB.le (pow_nonneg hl k)) hf).trans
  apply (div_le_iff₀ (Nat.cast_pos.mpr hH.1)).mpr
  change (4*B/t)*(log X)^ (k+1)≤(X:ℝ)^α at hL
  rw [div_mul_eq_mul_div,div_le_iff₀ hpos] at hL
  have hprod : (X:ℝ)^α*(X:ℝ)^α=(X:ℝ)^θ := by rw [←rpow_add hX,show α+α=θ by dsimp [α];ring]
  have hh := mul_le_mul hR.2.2.1 hL (by positivity : 0≤4*B*(log X)^(k+1)) (by positivity : 0≤2*(X:ℝ)^α)
  have he := mul_le_mul_of_nonneg_left hH.2.2 hpos.le
  rw [pow_succ] at hh
  nlinarith only [hh,he,show (X:ℝ)^α*(X:ℝ)^α*t=(X:ℝ)^θ*t by rw [hprod]]

theorem transfer {θ : ℝ} (ht : 0<θ) (ht' : θ≤1) {f : ℕ → ℝ} (hf : Controlled f)
    {P Q : ℝ → Prop} {t : ℝ} (hp : 0<t)
    (hPQ : ∀ a b : ℝ, |a-b|≤t → P b → Q a)
    (h : Almost (fun X n => ∀ H : ℕ,Admits θ X H → P (avg X n H f))) :
    Typical (fun X n => ∀ H : ℕ,Admits θ X H → Q (avg X n H f)) := by
  apply ThetaPrimeStartDensity.transfer (half_pos ht) (show θ/2<1 by linarith) h
  filter_upwards [shift ht ht' hf hp] with X hX
  intro n hn hbound j hj hgood
  obtain ⟨hn',hbad⟩ := mem_missed.mp hn
  apply hbad
  intro H hH
  exact hPQ _ _ (hX n j (mem_Ico.mp (mem_filter.mp hn').1).1 (mem_Ioc.mp hj).1.le
    ((mem_Ioc.mp hj).2.trans hbound.le) (mem_Ioc.mp hj).2 H hH) (hgood H hH)

#print axioms transfer
end
end Arxiv.«2501.03234».ThetaPrimeAnchorTransfer
