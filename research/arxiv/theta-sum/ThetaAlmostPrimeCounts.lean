import ThetaWindowGrid

/-! Converting logarithmically sparse exceptions at each fixed length into
simultaneous estimates on ordinary primes throughout a range of lengths. -/
namespace Arxiv.«2501.03234».ThetaAlmostPrimeCounts
open Real Finset Filter ThetaWindowApproximation ThetaAlmostPeriodicWindows ThetaWindowGrid
open ThetaShortPrimeInterval ThetaLocalPrimeCounts
noncomputable section

/-- A per-length lower estimate for unweighted ordinary prime counts. -/
def FixedLower (β c : ℝ) := ∀ q : ℕ, 0<q → PerLength β (fun X n H =>
  ∀ b<q,b.Coprime q → c/(q.totient:ℝ) ≤ scaledCount X n H q b)

/-- The corresponding ordinary per-length asymptotic at fixed moduli. -/
def FixedLimit (β : ℝ) := ∀ q : ℕ, 0<q → ∀ δ : ℝ, 0<δ → PerLength β (fun X n H =>
  ∀ b<q, |scaledCount X n H q b-(if b.Coprime q then (1:ℝ)/q.totient else 0)|≤δ)

private theorem net {β θ : ℝ} (ht : 0<θ) (hβ : β<θ) {K : ℕ} (hK : 2≤K) :
    ∀ᶠ X : ℕ in atTop,∀ H : ℕ, Admits θ X H →
    ∃ A∈grid X K,∃ B∈grid X K, Admits β X A ∧ Admits β X B ∧ A≤H ∧ H≤B ∧
      (K:ℝ)*((H:ℝ)-A)≤H ∧ (K:ℝ)*((B:ℝ)-H)≤H ∧ H≤2*A ∧ B≤2*H := by
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  filter_upwards [((tendsto_rpow_atTop ht).comp hn).eventually_ge_atTop (K:ℝ),
    ((tendsto_rpow_atTop (sub_pos.mpr hβ)).comp hn).eventually_ge_atTop 2,eventually_ge_atTop (1:ℕ)] with X hk h2 hx
  intro H hH
  change (K:ℝ)≤(X:ℝ)^θ at hk
  change (2:ℝ)≤(X:ℝ)^(θ-β) at h2
  have hp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  obtain ⟨A,ha,B,hb,hA,haH,hHB,hBX,hlo,hhi⟩ := bracket (by omega : 0<K) (by exact_mod_cast hk.trans hH.2.2) hH.2.1
  have hlo' := (Nat.mul_le_mul_right (H-A) hK).trans hlo
  have hhi' := (Nat.mul_le_mul_right (B-H) hK).trans hhi
  have hAH : H≤2*A := by omega
  have hBH : B≤2*H := by omega
  rw [rpow_sub hp] at h2
  have hhalf := ((le_div_iff₀ (rpow_pos_of_pos hp β)).mp h2).trans hH.2.2
  have hreal : (H:ℝ)≤2*(A:ℝ) := by exact_mod_cast hAH
  have hAl : (X:ℝ)^β≤A := le_of_mul_le_mul_left (hhalf.trans hreal) (by norm_num : (0:ℝ)<2)
  refine ⟨A,ha,B,hb,⟨hA,haH.trans hH.2.1,hAl⟩,⟨hH.1.trans_le hHB,hBX,hAl.trans (by exact_mod_cast haH.trans hHB)⟩,
    haH,hHB,?_,?_,hAH,hBH⟩
  · exact_mod_cast (show (K:ℝ)*((H:ℝ)-(A:ℝ))≤H by rw [←Nat.cast_sub haH];exact_mod_cast hlo)
  · rw [←Nat.cast_sub hHB];exact_mod_cast hhi

private theorem monotone_count {X n A H q b : ℕ} (hX : 1≤X) (hA : 0<A) (ha : A≤H) :
    A*scaledCount X n A q b≤H*scaledCount X n H q b := by
  have hs : (sample n A).filter (fun p => p%q=b)⊆(sample n H).filter (fun p => p%q=b) := by
    intro p hp
    obtain ⟨hp,hr⟩ := mem_filter.mp hp
    obtain ⟨hi,hpr,ht⟩ := mem_primes.mp hp
    exact mem_filter.mpr ⟨mem_primes.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2.trans (Nat.add_le_add_left ha n)⟩,hpr,ht⟩,hr⟩
  have hA' : (A:ℝ)≠0 := Nat.cast_ne_zero.mpr hA.ne'
  have hH' : (H:ℝ)≠0 := Nat.cast_ne_zero.mpr (hA.trans_le ha).ne'
  have cancel {a : ℝ} (ha : a≠0) : a*(log X/a)=log X := by field_simp
  simp only [scaledCount,←mul_assoc,cancel hA',cancel hH']
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hs)) (log_nonneg (by exact_mod_cast hX))

theorem lower {β θ c : ℝ} (ht : 0<θ) (hβ : β<θ) (hc : 0≤c) (h : FixedLower β c) : Lower θ (c/2) := by
  intro q hq
  apply mono (uniform (h q hq) 2)
  filter_upwards [net ht hβ (le_refl 2),eventually_ge_atTop (1:ℕ)] with X hgrid hx
  intro n _ hh H hH b hb hu
  obtain ⟨A,ha,_,_,ha',_,haH,_,_,_,hHA,_⟩ := hgrid H hH
  have hs := (mul_le_mul_of_nonneg_left (hh A ha ha' b hb hu) (Nat.cast_nonneg A)).trans (monotone_count hx ha'.1 haH)
  have hcoef := mul_le_mul_of_nonneg_right (show (H:ℝ)≤2*A by exact_mod_cast hHA)
    (div_nonneg hc (Nat.cast_nonneg q.totient (α:=ℝ)))
  have hpos : 0<(H:ℝ) := by exact_mod_cast hH.1
  apply le_of_mul_le_mul_left (a:= (H:ℝ)) _ hpos
  rw [div_right_comm c 2]
  linarith only [hs,hcoef]

private theorem interpolate {A H B L V R u d : ℝ} (hA : 0≤A) (hH : 0<H)
    (hAH : A≤H) (hHB : H≤B) (hBH : B≤2*H) (hd : 0≤d)
    (hl : H-A≤d*H) (hr : B-H≤d*H) (_hu : 0≤u) (hu' : u≤1)
    (h₁ : |L-u|≤d) (h₂ : |R-u|≤d) (h₃ : A*L≤H*V) (h₄ : H*V≤B*R) :
    |V-u|≤3*d := by
  have h₅ := mul_le_mul_of_nonneg_left (abs_le.mp h₁).1 hA
  have h₆ := mul_le_mul_of_nonneg_left (abs_le.mp h₂).2 (hH.le.trans hHB)
  have hl' := (mul_le_of_le_one_right (sub_nonneg.mpr hAH) hu').trans hl
  have hr' := (mul_le_of_le_one_right (sub_nonneg.mpr hHB) hu').trans hr
  apply abs_le.mpr;constructor
  · apply le_of_mul_le_mul_left (a:=H) _ hH
    nlinarith only [hl',h₃,h₅,mul_le_mul_of_nonneg_right hAH hd,mul_nonneg hH.le hd]
  · apply le_of_mul_le_mul_left (a:=H) _ hH
    nlinarith only [hr',h₄,h₆,mul_le_mul_of_nonneg_right hBH hd]

theorem limit {β θ : ℝ} (ht : 0<θ) (hβ : β<θ) (h : FixedLimit β) : Equidistributed θ := by
  intro q hq t ht'
  let d := t/4
  have hd : 0<d := by dsimp [d];positivity
  let K := max 2 ⌈1/d⌉₊
  have hk : 2≤K := le_max_left ..
  have hk' : 1≤(K:ℝ)*d := (div_le_iff₀ hd).mp <| (Nat.le_ceil (1/d)).trans (Nat.cast_le.mpr (le_max_right ..))
  apply mono (uniform (h q hq d hd) K)
  filter_upwards [net ht hβ hk,eventually_ge_atTop (1:ℕ)] with X hgrid hx
  intro n _ hh H hH b hb
  obtain ⟨A,ha,B,hb',hA,hB,hAH,hHB,hl,hr,_,hBH⟩ := hgrid H hH
  let u := if b.Coprime q then (1:ℝ)/q.totient else 0
  have hu : 0≤u := by dsimp [u];split_ifs <;> positivity
  have hu' : u≤1 := by
    dsimp [u];split_ifs
    · exact one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1)
        (by exact_mod_cast (Nat.totient_pos.mpr hq) : (1:ℝ)≤q.totient) |>.trans_eq (one_div_one)
    · norm_num
  have bound (v : ℝ) (hv : 0≤v) (hh : (K:ℝ)*v≤H) : v≤d*H := by
    have ha := mul_le_mul_of_nonneg_right hk' hv
    have hb := mul_le_mul_of_nonneg_left hh hd.le
    nlinarith only [ha,hb]
  have hI := interpolate (Nat.cast_nonneg A) (Nat.cast_pos.mpr hH.1) (Nat.cast_le.mpr hAH)
    (Nat.cast_le.mpr hHB) (by exact_mod_cast hBH) hd.le
    (bound _ (sub_nonneg.mpr (Nat.cast_le.mpr hAH)) hl) (bound _ (sub_nonneg.mpr (Nat.cast_le.mpr hHB)) hr)
    hu hu' (hh A ha hA b hb) (hh B hb' hB b hb) (monotone_count hx hA.1 hAH) (monotone_count hx hH.1 hHB)
  exact hI.trans (by dsimp only [d];linarith)

#print axioms lower
#print axioms limit
end
end Arxiv.«2501.03234».ThetaAlmostPrimeCounts
