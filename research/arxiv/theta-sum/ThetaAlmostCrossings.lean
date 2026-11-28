import ThetaAlmostExcursions
import ThetaCrossingFrequency

/-! Almost-all windows force many distinct adjacent sign changes in every
dyadic interval, even when some prescribed windows have no prime-count estimate. -/
namespace Arxiv.«2501.03234».ThetaAlmostCrossings
open Real Finset Filter ThetaWindowApproximation ThetaAlmostPeriodicWindows ThetaLocalIntervalTests
open ThetaLocalPrimeCounts ThetaConsecutiveCrossings ThetaShortPrimeInterval ThetaNaturalPrimeMeans
noncomputable section

theorem windows {θ c : ℝ} (h : Lower θ c) (hc : 0<c) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) :
    Almost (fun X n => ∀ H : ℕ,Admits θ X H → Crossing n H q r) := by
  obtain ⟨a,ha,h₁⟩ := ThetaAlmostExcursions.density h hc hAP hq hr hu 2 (d:=1) (by norm_num)
  obtain ⟨b,hb,h₂⟩ := ThetaAlmostExcursions.density h hc hAP hq hr hu (-2) (d:=1) (by norm_num)
  obtain ⟨P,hP⟩ := eventually_atTop.mp eventually_nonzero
  apply mono (inter h₁ h₂)
  filter_upwards [eventually_ge_atTop (2:ℕ),eventually_ge_atTop P] with X hX hXP
  intro n hn hh H hH
  have hl := log_pos (show (1:ℝ)<X by exact_mod_cast (show 1<X by omega))
  have hHH : 0<(H:ℝ) := by exact_mod_cast hH.1
  have extract (A y : ℝ) (hA : 0<A)
      (h : A*H/log X≤((hits q r y 1 (sample n H)).card:ℝ)) :
      ∃ p∈(sample n H).filter (fun p => p%q=r), |deviation p-y|<1 := by
    have he := (show 0<A*H/log X by positivity).trans_le h
    obtain ⟨p,hp⟩ := card_pos.mp (by exact_mod_cast he)
    exact ⟨p,(mem_filter.mp hp).1,(mem_filter.mp hp).2⟩
  apply of_signs
  · intro p hp
    obtain ⟨hI,hp',_⟩ := mem_primes.mp (mem_filter.mp hp).1
    exact hP p (hXP.trans ((mem_Ico.mp hn).1.trans (mem_Ioc.mp hI).1.le)) hp'
  · obtain ⟨p,hp,hs⟩ := extract a 2 ha (hh.1 H hH)
    exact ⟨p,hp,by linarith only [(abs_lt.mp hs).1]⟩
  · obtain ⟨p,hp,hs⟩ := extract b (-2) hb (hh.2 H hH)
    exact ⟨p,hp,by linarith only [(abs_lt.mp hs).2]⟩

private theorem incidence {X H q r : ℕ} (hH : 0<H) {g : Finset ℕ}
    (hg : ∀ n∈g, X≤n ∧ n+H≤2*X ∧ Crossing n H q r) :
    (g.card:ℝ)/H≤(ThetaCrossingFrequency.starts X q r).card := by
  classical
  let D := ThetaCrossingFrequency.starts X q r
  let f (p : ℕ) : ℝ := if p∈D then 1 else 0
  have hH' : 0<(H:ℝ) := by exact_mod_cast hH
  have hf (p : ℕ) : 0≤f p := by dsimp [f];split_ifs <;> norm_num
  have hh := ThetaMaximalWindow.count f hf (one_div_nonneg.mpr hH'.le)
    (s:=g) (L:=X) (U:=2*X) (fun n hn => (hg n hn).1) (by
      intro n hn;obtain ⟨hx,hb,a,b,han,hab,hb',ha',hp',har,hbr,hs,hgap⟩ := hg n hn
      have haD : a∈D := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hx.trans_lt han,hab.le.trans (hb'.trans hb)⟩,
        ha',har,b,hab,hb'.trans hb,hp',hbr,hs,hgap⟩
      refine ⟨H,hH,hb,?_⟩
      have hm : a∈Ioc n (n+H) := mem_Ioc.mpr ⟨han,hab.le.trans hb'⟩
      simpa [f,haD,hH'.ne'] using (single_le_sum (f:=f) (fun j _ => hf j) hm))
  have hsub : (Ioc X (2*X)).filter (·∈D)⊆D := fun p hp => (mem_filter.mp hp).2
  change (1/(H:ℝ))*(g.card:ℝ)≤∑ p∈Ioc X (2*X),if p∈D then (1:ℝ) else 0 at hh
  rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one,one_div_mul_eq_div] at hh
  exact hh.trans (Nat.cast_le.mpr (card_le_card hsub))

/-- The left endpoint of each pair is counted once. The two primes are
consecutive within the specified progression, including the ordinary case q=1. -/
theorem frequency {θ : ℝ} (h₀ : 0≤θ) (h₁ : θ<1) {q r : ℕ}
    (hw : Almost (fun X n => ∀ H : ℕ,Admits θ X H → Crossing n H q r)) :
    ∀ᶠ X : ℕ in atTop,(X:ℝ)^(1-θ)/4≤((ThetaCrossingFrequency.starts X q r).card:ℝ) := by
  classical
  have hg := (tendsto_rpow_atTop (sub_pos.mpr h₁)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hw (1/4) (by norm_num),hg.eventually_ge_atTop 8,eventually_ge_atTop (2:ℕ)] with X hbad hlarge hX
  let H := ⌈(X:ℝ)^θ⌉₊
  have hx : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hpow := one_le_rpow (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega)) h₀
  have hHH : 0<H := Nat.ceil_pos.mpr (rpow_pos_of_pos hx θ)
  have hreal : (H:ℝ)≤2*(X:ℝ)^θ := calc
    _ ≤ (X:ℝ)^θ+1 := (Nat.ceil_lt_add_one (rpow_nonneg hx.le θ)).le
    _ ≤ _ := by linarith only [hpow]
  have hprod : (X:ℝ)^(1-θ)*(X:ℝ)^θ=X := by rw [←rpow_add hx,sub_add_cancel,rpow_one]
  have hlen : 4*H≤X := by
    have he := mul_le_mul_of_nonneg_right hlarge (rpow_nonneg hx.le θ)
    change 8*(X:ℝ)^θ≤(X:ℝ)^(1-θ)*(X:ℝ)^θ at he
    exact_mod_cast (show 4*(H:ℝ)≤X by linarith only [hprod,he,hreal])
  let B := exceptional X (fun n => ∀ K : ℕ,Admits θ X K → Crossing n K q r)
  let A := Ico X (2*X-H)
  let G := A \ B
  have hA : A⊆starts X := by
    intro n hn;obtain ⟨hn,hb⟩ := mem_Ico.mp hn;exact mem_Ico.mpr ⟨hn,by omega⟩
  have hlow : (X:ℝ)/2≤G.card := by
    have ha : A.card=X-H := by simp only [A,Nat.card_Ico];omega
    have hcard := card_le_card (inter_subset_right (s₁:=A) (s₂:=B))
    have hh := card_sdiff_add_card_inter A B
    have hcast : (A.card:ℝ)=(X:ℝ)-H := by rw [ha,Nat.cast_sub (by omega)]
    have hcount : (A.card:ℝ)≤G.card+(B.card:ℝ) := by exact_mod_cast (show A.card≤G.card+B.card by dsimp [G];omega)
    change (B.card:ℝ)≤1/4*(X:ℝ) at hbad
    have hlen' : 4*(H:ℝ)≤X := by exact_mod_cast hlen
    linarith only [hcount,hcast,hbad,hlen']
  have hbound := incidence (q:=q) (r:=r) hHH (g:=G) (by
    intro n hn;obtain ⟨ha,hb⟩ := mem_sdiff.mp hn
    have hc := mem_Ico.mp ha
    refine ⟨hc.1,by omega,?_⟩
    by_contra hh
    exact hb (mem_exceptional.mpr ⟨hA ha,fun hx => hh (hx H ⟨hHH,by omega,Nat.le_ceil _⟩)⟩))
  have hd := (div_le_iff₀ (Nat.cast_pos.mpr hHH : (0:ℝ)<H)).mp hbound
  have hu := mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg (α:=ℝ) (ThetaCrossingFrequency.starts X q r).card)
  apply (le_of_mul_le_mul_right ?_ (rpow_pos_of_pos hx θ))
  rw [div_mul_eq_mul_div,hprod]
  nlinarith only [hlow,hd,hu]

#print axioms windows
#print axioms frequency
end
end Arxiv.«2501.03234».ThetaAlmostCrossings
