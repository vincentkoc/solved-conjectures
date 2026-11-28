import ThetaRowProgressionDiscrepancy
import ThetaPrimeDensity

/-! A 64th-power band form of the ordinary Siegel--Walfisz counting estimate. -/
namespace Arxiv.«2501.03234».ThetaSiegelWalfiszBand
open Real Finset Filter ThetaRowProgressionDiscrepancy
noncomputable section

/-- A theta-free prime-counting version, centered at the total prime count.
An extra inverse logarithm absorbs the usual implied constant. -/
def Ordinary : Prop := ∀ A B : ℕ, ∀ᶠ X : ℕ in atTop, ∀ q b : ℕ,
    0 < q → (q:ℝ)≤(log X)^A → b < q → b.Coprime q →
    |(((Nat.primesLE X).filter (fun p => p%q=b)).card:ℝ)-
      (X.primeCounting:ℝ)/q.totient| ≤ X/(log X)^B

def band (N : ℕ) := (Nat.primesLE (N^64)).filter (N^56≤·)

theorem mem_band {p N : ℕ} : p∈band N ↔ p.Prime ∧ N^56≤p ∧ p≤N^64 := by
  simp only [band,mem_filter,Nat.mem_primesLE]; tauto

theorem log_power (B : ℕ) : ∀ᶠ N : ℕ in atTop, (log (N:ℝ))^B≤N := by
  have h := ((isLittleO_log_rpow_rpow_atTop (B:ℝ) (by norm_num : (0:ℝ)<1)).natCast_atTop).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [h,eventually_ge_atTop (1:ℕ)] with N hh hN
  have hl := log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)
  simpa [rpow_natCast,Real.norm_eq_abs,abs_of_nonneg hl,abs_of_nonneg (pow_nonneg hl B)] using hh

/-- Removing primes below the band costs at most its lower endpoint. The
estimate holds also on nonunit residues, which contain no primes in the band. -/
theorem classes (hsw : Ordinary) (A B : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, 0 < q → (q:ℝ)≤(log N)^A →
    Classes (band N) q (N^64).primeCounting (2*(N:ℝ)^64/(log N)^B) := by
  have hlim : Tendsto (fun N : ℕ => N^64) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [hlim.eventually (hsw A B),log_power A,log_power B,eventually_ge_atTop (2:ℕ)] with N H ha hb hN
  intro q hq hqa b hbq
  have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hlog := log_pos hn
  have hlog' : log (N:ℝ)≤log (N^64:ℕ) := by
    rw [Nat.cast_pow,log_pow]; norm_num; linarith
  have hqN : q≤N := by exact_mod_cast hqa.trans ha
  let F := (Nat.primesLE (N^64)).filter (fun p => p%q=b)
  let G := (band N).filter (fun p => p%q=b)
  have hsub : G⊆F := fun p hp => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
  have hδ : 0≤(N:ℝ)^64/(log N)^B := by positivity
  change |(G.card:ℝ)-(if b.Coprime q then (N^64).primeCounting/(q.totient:ℝ) else 0)|≤_
  by_cases hcop : b.Coprime q
  · rw [if_pos hcop]
    have hsmall : F \ G ⊆ range (N^56) := by
      intro p hp; obtain ⟨hf,hg⟩ := mem_sdiff.mp hp
      apply mem_range.mpr
      by_contra! he
      exact hg (mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hf).1,he⟩,(mem_filter.mp hf).2⟩)
    have hcard := card_le_card hsmall
    rw [card_range,card_sdiff_of_subset hsub] at hcard
    have hGFN := card_le_card hsub
    have hF : (F.card:ℝ)≤G.card+(N:ℝ)^56 := by
      exact_mod_cast (show F.card≤G.card+N^56 by omega)
    have hcost : (N:ℝ)^56≤(N:ℝ)^64/(log N)^B := by
      rw [le_div_iff₀ (pow_pos hlog _)]
      calc _ ≤ (N:ℝ)^56*N := mul_le_mul_of_nonneg_left hb (by positivity)
           _ = (N:ℝ)^57 := by ring
           _ ≤ _ := pow_le_pow_right₀ hn.le (by decide)
    have h := H q b hq (hqa.trans (pow_le_pow_left₀ hlog.le hlog' _)) hbq hcop
    have hgt : (N^64:ℕ)/(log (N^64:ℕ))^B≤(N:ℝ)^64/(log N)^B := by
      rw [Nat.cast_pow]; apply div_le_div_of_nonneg_left (by positivity) (pow_pos hlog _) _
      exact pow_le_pow_left₀ hlog.le (by simpa only [Nat.cast_pow] using hlog') _
    change |(F.card:ℝ)-_|≤_ at h
    have hGF : (G.card:ℝ)≤F.card := by exact_mod_cast card_le_card hsub
    rcases abs_le.mp (h.trans hgt) with ⟨hl,hu⟩
    rw [mul_div_assoc]
    apply abs_le.mpr
    constructor <;> linarith only [hl,hu,hF,hcost,hGF,hδ]
  · have hG : G=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hx,he⟩ := mem_filter.mp hp
      obtain ⟨hpr,hl,_⟩ := mem_band.mp hx
      have hpq : p.Coprime q := hpr.coprime_iff_not_dvd.mpr fun h => by
        have hle := Nat.le_of_dvd hq h
        have hpow : N<N^56 := by
          calc N=N^1 := by simp
               _ < _ := Nat.pow_lt_pow_right (by omega) (by decide)
        omega
      apply hcop; rw [←he,←ZMod.isUnit_iff_coprime,ZMod.natCast_mod,ZMod.isUnit_iff_coprime]
      exact hpq
    simp only [if_neg hcop,hG,card_empty,Nat.cast_zero,sub_zero,abs_zero]
    positivity

#print axioms classes
end
end Arxiv.«2501.03234».ThetaSiegelWalfiszBand
