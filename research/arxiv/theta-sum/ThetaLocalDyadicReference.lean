import ThetaLocalSampledPowers
import ThetaLocalPowerStability
import ThetaEmpiricalPrimeMoments

/-! Comparison of logarithmic-integral and prime-count normalizations in
the long reference window. -/
namespace Arxiv.«2501.03234».ThetaLocalDyadicReference
open Real Finset Filter ThetaLocalPrimeCounts ThetaShortPrimeInterval ThetaCharacterPrimeMeans
open ThetaNaturalPrimeMeans
open scoped Topology
noncomputable section

def avg (X H : ℕ) (f : ℕ → ℝ) := (∑ p∈sample X H,f p)/mass X H

theorem twice : Tendsto (fun X : ℕ => 2*X) atTop atTop :=
  tendsto_atTop_mono (fun X : ℕ => show X≤2*X by omega) tendsto_id

theorem pi_bound : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop,
    ((2*X).primeCounting:ℝ)≤C*mass X X := by
  have hu := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Chebyshev.eventually_primeCounting_le zero_lt_one)
  simp only [Nat.floor_natCast] at hu
  refine ⟨4*(log 4+1),by positivity,?_⟩
  filter_upwards [twice.eventually hu,eventually_ge_atTop (2:ℕ)] with X h hx
  have hp : 0<(X:ℝ) := by exact_mod_cast (by omega : 0<X)
  have hl : 0<log (X:ℝ) := log_pos (by exact_mod_cast hx)
  have hlog := log_le_log hp (show (X:ℝ)≤(2*X:ℕ) by exact_mod_cast (show X≤2*X by omega))
  change ((2*X).primeCounting:ℝ)≤(log 4+1)*(2*X:ℕ)/log ((2*X:ℕ):ℝ) at h
  have hU := (le_div_iff₀ (hl.trans_le hlog)).mp h
  push_cast at hU hlog
  apply le_trans _ (mul_le_mul_of_nonneg_left (mass_lower hx (le_refl X)) (by positivity : 0≤4*(log 4+1)))
  rw [←mul_div_assoc,le_div_iff₀ (by positivity)]
  linarith only [hU,mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (2*X).primeCounting)]

theorem sample_sub {X H p : ℕ} (hp : p∈sample X H) (hH : H≤X) : p∈Nat.primesLE (2*X) := by
  obtain ⟨hi,hp,_⟩ := mem_primes.mp hp
  exact Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp hi).2.trans (by omega),hp⟩

theorem dyadic_add (X : ℕ) (f : ℕ → ℝ) :
    (∑ p∈sample X X,f p)+(∑ p∈Nat.primesLE X,f p)=∑ p∈Nat.primesLE (2*X),f p := by
  classical
  have hs : sample X X=(Nat.primesLE (2*X) \ Nat.primesLE X : Finset ℕ) := by
    apply Finset.ext; intro p
    rw [Finset.mem_sdiff,Nat.mem_primesLE,Nat.mem_primesLE]
    simp only [sample,mem_primes,mem_Ioc,and_true]
    constructor
    · rintro ⟨⟨h₁,h₂⟩,hp⟩
      exact ⟨⟨by omega,hp⟩,fun h => h₁.not_ge h.1⟩
    · rintro ⟨⟨h₂,hp⟩,h₁⟩
      exact ⟨⟨by by_contra! h;exact h₁ ⟨h,hp⟩,by omega⟩,hp⟩
  rw [hs,sum_sdiff (show Nat.primesLE X⊆Nat.primesLE (2*X) by
    intro p hp; obtain ⟨h₁,h₂⟩ := Nat.mem_primesLE.mp hp; exact Nat.mem_primesLE.mpr ⟨by omega,h₂⟩)]

theorem relative_count {θ : ℝ} (ordinary : Ordinary θ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
    |((sample X H).card:ℝ)-mass X H|≤ε*mass X H := by
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ordinary 0 2,ht.eventually_ge_atTop (2/ε),eventually_ge_atTop (2:ℕ)] with X hv hl hx
  intro H hh hθ
  have h := hv H hh hθ 1 (by decide) (by simp) 0 (by decide) (by decide)
  have hs : ((sample X H).filter (fun p => p%1=0))=sample X H := filter_eq_self.mpr fun p _ => Nat.mod_one p
  rw [hs,Nat.totient_one,Nat.cast_one,div_one] at h
  have hlp : 0<log (X:ℝ) := log_pos (by exact_mod_cast hx)
  apply h.trans (le_trans _ (mul_le_mul_of_nonneg_left (mass_lower hx hh) hε.le))
  rw [←mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
  have hh := (div_le_iff₀ hε).mp hl
  change 2≤log (X:ℝ)*ε at hh
  nlinarith only [mul_le_mul_of_nonneg_left hh (show 0≤H*log (X:ℝ) by positivity)]

theorem dyadic_moments (k : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop,
    (∑ p∈sample X X,|residual p|^k)≤C*mass X X := by
  obtain ⟨C,hC,hπ⟩ := pi_bound
  by_cases hk : k=0
  · subst k
    refine ⟨C,hC,?_⟩
    filter_upwards [hπ] with X hx
    simpa only [pow_zero,sum_const,nsmul_eq_mul,mul_one] using
      ((Nat.cast_le.mpr (card_le_card (fun _ hp => sample_sub hp (le_refl X)))).trans
        (by simpa only [Nat.primesLE_card_eq_primeCounting] using hx) :
      ((sample X X).card:ℝ)≤C*mass X X)
  obtain ⟨D,hD,hm⟩ := ThetaEmpiricalPrimeMoments.logarithmic
  let V := (D*(1+log k)^2)^k
  have hV : 0<V := by
    have hl := log_nonneg (by exact_mod_cast (show 1≤k by omega) : 1≤(k:ℝ))
    dsimp [V]; positivity
  have hlim := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).comp twice
  refine ⟨C*V,by positivity,?_⟩
  filter_upwards [hπ,twice.eventually hm,hlim.eventually_ge_atTop ((k:ℝ)^2)] with X hx h hL
  have hlk : 0≤log (k:ℝ) := log_nonneg (by exact_mod_cast (show 1≤k by omega))
  have hM := h k (by omega) (hL.trans (le_mul_of_one_le_right ((sq_nonneg _).trans hL) (by linarith only [hlk])))
  apply (sum_le_sum_of_subset_of_nonneg (fun _ hp => sample_sub hp (le_refl X)) (fun p _ _ => pow_nonneg (abs_nonneg _) k)).trans
  change (∑ p∈Nat.primesLE (2*X),|residual p|^k)≤_
  exact hM.trans (by change (↑(2*X).primeCounting:ℝ)*V≤_;nlinarith only [mul_le_mul_of_nonneg_right hx hV.le])

#print axioms dyadic_moments
#print axioms relative_count
end
end Arxiv.«2501.03234».ThetaLocalDyadicReference
