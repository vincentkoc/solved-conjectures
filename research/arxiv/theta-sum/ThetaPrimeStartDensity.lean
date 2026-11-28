import ThetaPrimeIntervalSieve
import ThetaMaximalWindow
import ThetaWindowApproximation
import ThetaLocalExcursionScales

/-! An exceptional set of integer starts transfers to prime starts if each
bad prime has a full short neighborhood of exceptional integers. -/
namespace Arxiv.«2501.03234».ThetaPrimeStartDensity
open Real Finset Filter ThetaPrimeIntervalSieve ThetaWindowApproximation
noncomputable section

def missed (X : ℕ) (P : ℕ → Prop) : Finset ℕ := by classical exact (marks X X).filter (fun p => ¬P p)
@[simp] theorem mem_missed {X p : ℕ} {P : ℕ → Prop} : p∈missed X P ↔ p∈marks X X ∧ ¬P p := by
  classical simp [missed]

def Typical (P : ℕ → ℕ → Prop) := ∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,
  ((missed X (P X)).card:ℝ)*log X≤ε*X

theorem sieve {α : ℝ} (hα : 0<α) : ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,
    ∀ K n : ℕ, K≤n → (X:ℝ)^α≤K → ((marks n K).card:ℝ)*log X≤C*K := by
  obtain ⟨B,hB,M,hM⟩ := (show ∃ B : ℝ,0<B ∧ ∃ M : ℕ,∀ H≥M,∀ n : ℕ,H≤n →
      ((marks n H).card:ℝ)*log H≤B*H by
    obtain ⟨B,hB,hh⟩ := uniform;exact ⟨B,hB,eventually_atTop.mp hh⟩)
  refine ⟨B/α,by positivity,?_⟩
  have hg := (tendsto_rpow_atTop hα).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hg.eventually_ge_atTop (M:ℝ),eventually_ge_atTop (1:ℕ)] with X hm hX
  intro K n hn hk
  have h' := hM K (by exact_mod_cast hm.trans hk) n hn
  have hx : 0<(X:ℝ) := by exact_mod_cast hX
  have hlog := log_le_log (rpow_pos_of_pos hx α) hk
  rw [log_rpow hx] at hlog
  rw [div_mul_eq_mul_div,le_div_iff₀ hα]
  linarith only [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α:=ℝ) (marks n K).card),h']

theorem charge {X K : ℕ} {C : ℝ} (hC : 0<C) (hX : 2≤X) (hK : 0<K) {s E : Finset ℕ}
    (hs : s⊆marks X X) (hbound : ∀ n∈s,((marks n K).card:ℝ)*log X≤C*K)
    (hcover : ∀ n∈s, n+K≤2*X ∧ Ioc n (n+K)⊆E) :
    (s.card:ℝ)*log X≤C*E.card := by
  classical
  let f (j : ℕ) : ℝ := if j∈E then 1 else 0
  have hf (j : ℕ) : 0≤f j := by dsimp [f];split_ifs <;> norm_num
  have hl := log_pos (show (1:ℝ)<X by exact_mod_cast (show 1<X by omega))
  have hh := ThetaMaximalWindow.cover f hf (div_nonneg hl.le hC.le)
    (L:=X) (U:=2*X) (fun n hn => (mem_Ico.mp (mem_filter.mp (hs hn)).1).1) hs (by
      intro n hn; obtain ⟨hu,he⟩ := hcover n hn
      refine ⟨K,hK,hu,?_⟩
      have sub : marks X X∩Ico n (n+K)⊆marks n K := by
        intro j hj; obtain ⟨hp,hi⟩ := mem_inter.mp hj; exact mem_filter.mpr ⟨hi,(mem_filter.mp hp).2⟩
      calc log X/C*((marks X X∩Ico n (n+K)).card:ℝ)
          ≤ log X/C*((marks n K).card:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card sub)) (div_nonneg hl.le hC.le)
        _ ≤ K := by rw [div_mul_eq_mul_div,div_le_iff₀ hC];linarith only [hbound n hn]
        _ = ∑ j∈Ioc n (n+K), f j := by
          rw [sum_congr rfl (fun j hj => if_pos (he hj) : ∀ j∈Ioc n (n+K),f j=(1:ℝ))]
          simp [Nat.card_Ioc])
  have hs' : (∑ j∈Ioc X (2*X),f j)≤(E.card:ℝ) := by
    dsimp [f];rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
    exact Nat.cast_le.mpr (card_le_card fun j hj => (mem_filter.mp hj).2)
  have hh' := hh.trans hs'
  rw [div_mul_eq_mul_div,div_le_iff₀ hC] at hh'
  linarith only [hh']

def radius (α : ℝ) (X : ℕ) := ⌈(X:ℝ)^α⌉₊

theorem radius_bounds {α : ℝ} (ha : 0<α) (hb : α<1) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ X : ℕ in atTop,1≤radius α X ∧ radius α X≤X ∧ (radius α X:ℝ)≤2*(X:ℝ)^α ∧
      (radius α X:ℝ)*log X≤ε*X := by
  have ht := (isLittleO_log_rpow_atTop (sub_pos.mpr hb)).bound (half_pos he)
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  filter_upwards [hn.eventually ht,eventually_ge_atTop (3:ℕ)] with X hX hx
  have hx' : 1≤(X:ℝ) := by exact_mod_cast (show 1≤X by omega)
  have hp : 0<(X:ℝ) := by linarith
  have h₁ := one_le_rpow hx' ha.le
  have h₂ := rpow_le_rpow_of_exponent_le hx' hb.le
  rw [rpow_one] at h₂
  have hg : radius α X≤X := Nat.ceil_le.mpr h₂
  have hR : (radius α X:ℝ)≤2*(X:ℝ)^α := (Nat.ceil_lt_add_one (rpow_nonneg hp.le α)).le.trans (by linarith)
  have hl := log_nonneg hx'
  change ‖log (X:ℝ)‖≤ε/2*‖(X:ℝ)^(1-α)‖ at hX
  simp only [norm_eq_abs,abs_of_nonneg hl,abs_of_nonneg (rpow_nonneg hp.le _)] at hX
  have prod : (X:ℝ)^α*(X:ℝ)^(1-α)=X := by rw [←rpow_add hp,add_sub_cancel,rpow_one]
  refine ⟨Nat.ceil_pos.mpr (rpow_pos_of_pos hp α),hg,hR,?_⟩
  calc _ ≤ (2*(X:ℝ)^α)*(ε/2*(X:ℝ)^(1-α)) := mul_le_mul hR hX hl (by positivity)
       _ = ε*((X:ℝ)^α*(X:ℝ)^(1-α)) := by ring
       _ = _ := by rw [prod]

/-- Shrink the right boundary by the polynomial radius. The discarded starts
have negligible prime-normalized count even with the trivial cardinality bound. -/
theorem transfer {α : ℝ} (ha : 0<α) (hb : α<1) {P Q : ℕ → ℕ → Prop}
    (hq : Almost Q) (h : ∀ᶠ X : ℕ in atTop, ∀ n∈missed X (P X), n+radius α X<2*X →
      ∀ j∈Ioc n (n+radius α X),¬Q X j) : Typical P := by
  classical
  obtain ⟨C,hC,hh⟩ := sieve ha
  intro ε hε
  filter_upwards [h,hh,hq (ε/(2*C)) (by positivity),radius_bounds ha hb (half_pos hε),eventually_ge_atTop (2:ℕ)]
    with X hf hs hQ hr hx
  let K := radius α X
  let D := missed X (P X)
  let g := D.filter (fun n => n+K<2*X)
  let z := D.filter (fun n => ¬n+K<2*X)
  have hg : g⊆marks X X := fun _ hn => (mem_missed.mp (mem_filter.mp hn).1).1
  have hin {n : ℕ} (hn : n∈D) : n∈Ico X (2*X) := by
    have hi := (mem_filter.mp (mem_missed.mp hn).1).1;simpa [two_mul] using hi
  have h₁ := charge (s:=g) (E:=exceptional X (Q X)) hC hx hr.1 hg (fun n hn =>
    hs K n (hr.2.1.trans (mem_Ico.mp (hin (mem_filter.mp hn).1)).1) (Nat.le_ceil _)) (by
      intro n hn;obtain ⟨hd,hi⟩ := mem_filter.mp hn
      refine ⟨hi.le,?_⟩
      intro j hj;exact mem_exceptional.mpr ⟨mem_Ico.mpr ⟨(mem_Ico.mp (hin hd)).1.trans (mem_Ioc.mp hj).1.le,(mem_Ioc.mp hj).2.trans_lt hi⟩,hf n hd hi j hj⟩)
  have hz : z⊆Ico (2*X-K) (2*X) := by
    intro n hn;obtain ⟨hd,hl⟩ := mem_filter.mp hn
    exact mem_Ico.mpr ⟨by omega,(mem_Ico.mp (hin hd)).2⟩
  have hz' : z.card≤K := (card_le_card hz).trans (by rw [Nat.card_Ico];omega)
  have heq : (g.card:ℝ)+(z.card:ℝ)=D.card := by exact_mod_cast card_filter_add_card_filter_not (s:=D) (fun n => n+K<2*X)
  have h₂ := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hz') (log_nonneg (by exact_mod_cast (show 1≤X by omega)))).trans hr.2.2.2
  have hmain := h₁.trans (mul_le_mul_of_nonneg_left hQ hC.le)
  change (D.card:ℝ)*log X≤ε*X
  have hc : C*(ε/(2*C)*X)=ε/2*X := by field_simp <;> ring
  rw [hc] at hmain
  rw [←heq,add_mul];linarith only [hmain,h₂]

#print axioms charge
#print axioms transfer
end
end Arxiv.«2501.03234».ThetaPrimeStartDensity
