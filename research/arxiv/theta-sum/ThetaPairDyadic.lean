import ThetaPrimeStartDensity
import ThetaLocalDyadicReference

/-! The true dyadic prime mass, the prime-relative exceptional set, and
the weighted first mark of a directed pair. -/
namespace Arxiv.«2501.03234».ThetaPairDyadic
open Real Filter Finset ThetaPrimeDensity ThetaNaturalPrimeMeans ThetaLocalDyadicReference
open ThetaWindowApproximation ThetaLocalPrimeCounts ThetaPrimeStartDensity ThetaShortPrimeInterval
open ThetaPrimeIntervalSieve
open scoped Topology
noncomputable section

def total (f : ℕ → ℝ) (X : ℕ) := log X/X*(∑ p∈Nat.primesLE X,f p)

theorem cumulative (hAP : ProgressionMangoldt) {f : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto (primeMean f) atTop (𝓝 a)) : Tendsto (total f) atTop (𝓝 a) := by
  have hπ : Tendsto (fun N : ℕ => (N.primeCounting:ℝ)*log N/N) atTop (𝓝 1) := by
    simpa [primeSet,Nat.mod_one,Nat.primesLE_card_eq_primeCounting] using
      prime_count_of_mangoldt (hAP (q:=1) (a:=0) (by decide) (by decide) (by decide))
  have hh := hf.mul hπ
  rw [mul_one] at hh
  apply hh.congr'
  filter_upwards [Nat.tendsto_primeCounting.eventually_gt_atTop (0:ℕ)] with X hx
  have hne : (X.primeCounting:ℝ)≠0 := by exact_mod_cast hx.ne'
  change ((∑ p∈Nat.primesLE X,f p)/X.primeCounting)*(X.primeCounting*log X/X)=_
  dsimp [total];field_simp

theorem first (hAP : ProgressionMangoldt) {f : ℕ → ℝ} {a : ℝ} (hf : Tendsto (primeMean f) atTop (𝓝 a)) :
    Tendsto (fun X : ℕ => avg X X X f) atTop (𝓝 a) := by
  have h₁ := cumulative hAP hf
  have hl := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).comp twice
  have hz : Tendsto (fun X : ℕ => log 2/log ((2*X:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hl
  have hratio := (tendsto_const_nhds (x:=(2:ℝ))).mul ((tendsto_const_nhds (x:=(1:ℝ))).sub hz)
  have hh := (hratio.mul (h₁.comp twice)).sub h₁
  convert hh.congr' _ using 1
  · ring_nf
  filter_upwards [eventually_ge_atTop (2:ℕ)] with X hx
  have hX : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hlog := log_pos (show (1:ℝ)<2*X by exact_mod_cast (show 1<2*X by omega))
  have hsum := dyadic_add X f
  change 2*(1-log 2/log ((2*X:ℕ):ℝ))*total f (2*X)-total f X=avg X X X f
  simp only [total,ThetaWindowApproximation.avg,Nat.cast_mul,Nat.cast_ofNat]
  rw [←hsum];field_simp
  rw [log_mul (by norm_num : (2:ℝ)≠0) hX.ne']
  ring

theorem ones : Tendsto (primeMean (fun _ => (1:ℝ))) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Nat.tendsto_primeCounting.eventually_gt_atTop (0:ℕ)] with X hx
  simp [primeMean,Nat.primesLE_card_eq_primeCounting,show (X.primeCounting:ℝ)≠0 by exact_mod_cast hx.ne']

theorem mass (hAP : ProgressionMangoldt) :
    Tendsto (fun X : ℕ => ((sample X X).card:ℝ)*log X/X) atTop (𝓝 1) := by
  simpa [ThetaWindowApproximation.avg,mul_div_assoc,mul_comm,mul_left_comm,mul_assoc,div_eq_mul_inv] using first hAP ones

theorem subset {X : ℕ} (hX : 2≤X) : sample X X⊆marks X X := by
  intro p hp
  obtain ⟨hi,hp,_⟩ := mem_primes.mp hp
  obtain ⟨hl,hr⟩ := mem_Ioc.mp hi
  have hn : p≠2*X := by intro he;rw [he] at hp;exact (Nat.not_prime_mul (by decide : 2≠1) (by omega : X≠1)) hp
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hl.le,by omega⟩,hp⟩

theorem relative (hAP : ProgressionMangoldt) {P : ℕ → ℕ → Prop} (h : Typical P) :
    Tendsto (fun X : ℕ => ((missed X (P X)).card:ℝ)/(sample X X).card) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr;intro ε he
  have hm := (mass hAP).eventually_const_lt (show (1:ℝ)/2<1 by norm_num)
  filter_upwards [h (ε/4) (by positivity),hm,eventually_ge_atTop (2:ℕ)] with X hh hm hx
  have hX : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_pos (show (1:ℝ)<X by exact_mod_cast hx)
  change 1/2<((sample X X).card:ℝ)*log X/X at hm
  rw [lt_div_iff₀ hX] at hm
  have hM : 0<((sample X X).card:ℝ) := pos_of_mul_pos_left (lt_trans (by positivity) hm) hl.le
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity),div_lt_iff₀ hM]
  apply (mul_lt_mul_iff_left₀ hl).mp
  linarith only [hh,mul_lt_mul_of_pos_left hm he,mul_pos he hX]

#print axioms first
#print axioms relative
end
end Arxiv.«2501.03234».ThetaPairDyadic
