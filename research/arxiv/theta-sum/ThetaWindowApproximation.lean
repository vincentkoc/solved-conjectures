import ThetaMaximalWindow
import ThetaLocalPrimeCounts
import ThetaPrimeLaw

/-! Upper density of starting points with a large approximation error in at
least one window. The exceptional set is shared by every window length. -/
namespace Arxiv.«2501.03234».ThetaWindowApproximation
open Real Finset Filter ThetaLocalPrimeCounts ThetaShortPrimeInterval ThetaNaturalPrimeMeans
noncomputable section

def starts (X : ℕ) := Ico X (2*X)
def avg (X n H : ℕ) (f : ℕ → ℝ) := log X/H*(∑ p∈sample n H,f p)
def exceptional (X : ℕ) (P : ℕ → Prop) : Finset ℕ := by classical exact (starts X).filter (fun n => ¬P n)
@[simp] theorem mem_exceptional {X n : ℕ} {P : ℕ → Prop} : n∈exceptional X P ↔ n∈starts X ∧ ¬P n := by classical simp [exceptional]

def Almost (P : ℕ → ℕ → Prop) := ∀ ε : ℝ, 0<ε → ∀ᶠ X : ℕ in atTop,
  ((exceptional X (P X)).card:ℝ)≤ε*X

theorem mono {P Q : ℕ → ℕ → Prop} (hp : Almost P)
    (h : ∀ᶠ X : ℕ in atTop, ∀ n∈starts X,P X n → Q X n) : Almost Q := by
  intro ε hε
  filter_upwards [hp ε hε,h] with X hx H
  apply le_trans _ hx
  apply Nat.cast_le.mpr;apply card_le_card
  intro n hn
  obtain ⟨hs,hh⟩ := mem_exceptional.mp hn
  exact mem_exceptional.mpr ⟨hs,fun hp => hh (H n hs hp)⟩

theorem inter {P Q : ℕ → ℕ → Prop} (hp : Almost P) (hq : Almost Q) :
    Almost (fun X n => P X n ∧ Q X n) := by
  classical
  intro ε hε
  filter_upwards [hp (ε/2) (half_pos hε),hq (ε/2) (half_pos hε)] with X h₁ h₂
  have hu : exceptional X (fun n => P X n ∧ Q X n)⊆exceptional X (P X)∪exceptional X (Q X) := by
    intro n hn;obtain ⟨hs,hh⟩ := mem_exceptional.mp hn
    by_cases h : P X n
    · exact mem_union_right _ (mem_exceptional.mpr ⟨hs,fun hq => hh ⟨h,hq⟩⟩)
    · exact mem_union_left _ (mem_exceptional.mpr ⟨hs,h⟩)
  have hc := (Nat.cast_le (α:=ℝ)).mpr ((card_le_card hu).trans (card_union_le ..))
  push_cast at hc; linarith only [hc,h₁,h₂]

private theorem window {X n H : ℕ} (f : ℕ → ℝ) :
    (∑ p∈Ioc n (n+H), if p.Prime then log X*f p else 0)=log X*∑ p∈sample n H,f p := by
  rw [mul_sum,←sum_filter]
  congr 1
  ext p; simp [sample,primes]

theorem finite {X : ℕ} (hX : 2≤X) (f : ℕ → ℝ) (hf : ∀ p,0≤f p) {τ : ℝ} (hτ : 0≤τ) :
    τ*(exceptional X (fun n => ∀ H : ℕ, 0<H → H≤X → avg X n H f≤τ)).card ≤
    log X*∑ p∈Nat.primesLE (3*X), f p := by
  classical
  have hl := log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  let F (p : ℕ) := if p.Prime then log X*f p else 0
  have hF (p : ℕ) : 0≤F p := by dsimp [F];split_ifs; exact mul_nonneg hl (hf p); exact le_rfl
  apply (ThetaMaximalWindow.count F hF hτ (L:=0) (U:=3*X) (fun _ _ => Nat.zero_le _) ?_).trans
  · rw [←sum_filter, mul_sum]
    apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => mul_nonneg hl (hf p))
    intro p hp;obtain ⟨hI,hp⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp hI).2,hp⟩
  · intro n hn
    obtain ⟨hn,hbad⟩ := mem_exceptional.mp hn
    push Not at hbad
    obtain ⟨H,hH,hHX,he⟩ := hbad
    obtain ⟨_,hn'⟩ := mem_Ico.mp hn
    refine ⟨H,hH,by omega,?_⟩
    change _≤∑ p∈Ioc n (n+H),if p.Prime then log X*f p else 0
    rw [window]
    have hHr : 0<(H:ℝ) := by exact_mod_cast hH
    dsimp [avg] at he
    rw [div_mul_eq_mul_div,(lt_div_iff₀ hHr)] at he
    exact he.le

theorem prime_budget : ∀ᶠ X : ℕ in atTop, (3*X).primeCounting*log X≤12*(X:ℝ) := by
  have hu := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Chebyshev.eventually_primeCounting_le zero_lt_one)
  simp only [Nat.floor_natCast] at hu
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hu
  filter_upwards [eventually_ge_atTop Y,eventually_ge_atTop (2:ℕ)] with X hx hX
  let P := 3*X
  have hP : X≤P := by dsimp [P];omega
  have hπ := hY P (hx.trans hP)
  have h2 : 2≤P := hX.trans hP
  have hlog := log_pos (show (1:ℝ)<P by exact_mod_cast (show 1<P by omega))
  have hxpos : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hmon := log_le_log hxpos (Nat.cast_le.mpr hP)
  have hπ' := (le_div_iff₀ hlog).mp hπ
  calc
    _ ≤ P.primeCounting*log P := mul_le_mul_of_nonneg_left hmon (Nat.cast_nonneg P.primeCounting)
    _ ≤ _ := hπ'.trans (by
      have hl := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      dsimp only [P];push_cast;nlinarith only [mul_le_mul_of_nonneg_right hl hxpos.le])

/-- A global prime mean error of δ costs at most 12δ/τ of the starting
integers, even when the length is selected after seeing the start. -/
theorem budget {δ τ : ℝ} (hδ : 0≤δ) (hτ : 0<τ) (f : ℕ → ℝ) (hf : ∀ p,0≤f p)
    (hm : ∀ᶠ Y : ℕ in atTop, primeMean f Y≤δ) : ∀ᶠ X : ℕ in atTop,
    ((exceptional X (fun n => ∀ H : ℕ, 0<H → H≤X → avg X n H f≤τ)).card:ℝ)≤
    (12*δ/τ)*X := by
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hm
  filter_upwards [eventually_ge_atTop Y,eventually_ge_atTop (2:ℕ),prime_budget] with X hx hX hu'
  let P := 3*X
  have hP : X≤P := by dsimp [P];omega
  have hmean := hY P (hx.trans hP)
  have h2 : 2≤P := hX.trans hP
  have hpr : (0:ℝ)<P.primeCounting := by
    have hp : 0<Nat.primeCounting 2 := by decide
    exact_mod_cast hp.trans_le (Nat.monotone_primeCounting h2)
  have hxl := log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  have hs := (div_le_iff₀ hpr).mp hmean
  have hcount := finite hX f hf hτ.le
  have hprod : _ ≤ (12*δ)*X := hcount.trans <| calc
    _ ≤ log X*(δ*P.primeCounting) := mul_le_mul_of_nonneg_left hs hxl
    _ = δ*(P.primeCounting*log X) := by ring
    _ ≤ δ*(12*X) := mul_le_mul_of_nonneg_left hu' hδ
    _ = _ := by ring
  rw [div_mul_eq_mul_div,le_div_iff₀ hτ,mul_comm _ τ]
  exact hprod

theorem difference {X n H : ℕ} (hX : 1≤X) (f g : ℕ → ℝ) :
    |avg X n H f-avg X n H g|≤avg X n H (fun p => |f p-g p|) := by
  rw [avg,avg,avg,←mul_sub,←sum_sub_distrib,abs_mul,
    abs_of_nonneg (div_nonneg (log_nonneg (by exact_mod_cast hX)) (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..)
    (div_nonneg (log_nonneg (by exact_mod_cast hX)) (Nat.cast_nonneg _))

#print axioms budget

end
end Arxiv.«2501.03234».ThetaWindowApproximation
