import ThetaPrimeAnchorTransfer
import ThetaAlmostPrimeDistribution

/-! Lower-density transfer for an arbitrary set of prime marks. -/
namespace Arxiv.«2501.03234».ThetaPairExcursionDensity
open Real Filter Finset ThetaWindowApproximation ThetaAlmostPeriodicWindows
open ThetaPrimeStartDensity ThetaPrimeAnchorTransfer ThetaShortPrimeInterval ThetaLocalPrimeCounts
open scoped Topology
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def mark (P : ℕ → Prop) (p : ℕ) : ℝ := if P p then 1 else 0

theorem avg_mark (X n H : ℕ) (P : ℕ → Prop) : avg X n H (mark P) =
    log X/H*((sample n H).filter P).card := by
  simp only [avg,mark,←sum_filter,sum_const,nsmul_eq_mul,mul_one]

theorem anchored {θ a : ℝ} (ht : 0<θ) (ht' : θ≤1) (ha : 0<a) {P : ℕ → Prop}
    (h : Almost (fun X n => ∀ H : ℕ,Admits θ X H →
      a*H/log X≤(((sample n H).filter P).card:ℝ))) :
    Typical (fun X n => ∀ H : ℕ,Admits θ X H → a/2≤avg X n H (mark P)) := by
  have hh : Almost (fun X n => ∀ H : ℕ,Admits θ X H → a≤avg X n H (mark P)) := by
    apply ThetaWindowApproximation.mono h
    filter_upwards [eventually_ge_atTop (2:ℕ)] with X hx
    intro n _ h H hH
    have hl := log_pos (show (1:ℝ)<X by exact_mod_cast hx)
    have hcard := (div_le_iff₀ hl).mp (h H hH)
    rw [avg_mark,div_mul_eq_mul_div,le_div_iff₀ (Nat.cast_pos.mpr hH.1)]
    linarith only [hcard]
  apply ThetaPrimeAnchorTransfer.transfer (P:=fun b => a≤b) (Q:=fun b => a/2≤b)
    ht ht' (bounded (B:=1) (fun p => by dsimp [mark];split_ifs <;> norm_num)) (half_pos ha) _ hh
  intro x y hxy hy
  linarith only [(abs_le.mp hxy).1,hy]

theorem dyadic {P : ℕ → Prop} {a : ℝ} (ha : 0<a)
    (h : Almost (fun X n => ∀ H : ℕ,Admits (1/2) X H →
      a*H/log X≤(((sample n H).filter P).card:ℝ))) :
    ∀ᶠ X : ℕ in atTop,a/3*X≤(((sample X X).filter P).card:ℝ)*log X := by
  filter_upwards [h (1/8) (by norm_num),eventually_ge_atTop (64:ℕ)] with X hbad hX
  let H := X/2
  let A := Ico X (2*X-H)
  let G (n : ℕ) := ∀ K : ℕ,Admits (1/2) X K → a*K/log X≤(((sample n K).filter P).card:ℝ)
  have hlen : X≤3*H := by dsimp [H];omega
  have hH : H≤X := Nat.div_le_self ..
  have hs : (X:ℝ)^(1/2:ℝ)≤H := by
    rw [←sqrt_eq_rpow]
    apply sqrt_le_iff.mpr
    refine ⟨Nat.cast_nonneg _,?_⟩
    have h₃ : 3≤(H:ℝ) := by exact_mod_cast (show 3≤H by dsimp [H];omega)
    have hlen' : (X:ℝ)≤3*H := by exact_mod_cast hlen
    nlinarith only [hlen',mul_nonneg (Nat.cast_nonneg (α:=ℝ) H) (sub_nonneg.mpr h₃)]
  have had : Admits (1/2) X H := ⟨by dsimp [H];omega,hH,hs⟩
  have hex : ∃ n∈A,G n := by
    by_contra! hn
    have hs : A⊆exceptional X G := by
      intro n hn'
      obtain ⟨h₁,h₂⟩ := mem_Ico.mp hn'
      exact mem_exceptional.mpr ⟨mem_Ico.mpr ⟨h₁,by omega⟩,hn n hn'⟩
    have hh := (Nat.cast_le (α:=ℝ)).mpr (card_le_card hs)
    have hA : A.card=X-H := by dsimp [A];rw [Nat.card_Ico];omega
    rw [hA,Nat.cast_sub hH] at hh
    change ((exceptional X G).card:ℝ)≤1/8*X at hbad
    have hsm : 2*H≤X := by dsimp [H];omega
    have hh' : 2*(H:ℝ)≤X := by exact_mod_cast hsm
    linarith only [hh,hbad,hh',show 0<(X:ℝ) by exact_mod_cast (show 0<X by omega)]
  obtain ⟨n,hn,hg⟩ := hex
  obtain ⟨hn₁,hn₂⟩ := mem_Ico.mp hn
  have hsub : (sample n H).filter P⊆(sample X X).filter P := by
    intro p hp
    obtain ⟨hp,hP⟩ := mem_filter.mp hp
    obtain ⟨hi,hp,_⟩ := mem_primes.mp hp
    obtain ⟨hl,hr⟩ := mem_Ioc.mp hi
    exact mem_filter.mpr ⟨mem_primes.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,hp,trivial⟩,hP⟩
  have hl := log_pos (show (1:ℝ)<X by exact_mod_cast (show 1<X by omega))
  have hh := ((div_le_iff₀ hl).mp (hg H had)).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hsub)) hl.le)
  have hh' : (X:ℝ)≤3*H := by exact_mod_cast hlen
  linarith only [hh,mul_le_mul_of_nonneg_left hh' ha.le]

#print axioms anchored
#print axioms dyadic
end
end Arxiv.«2501.03234».ThetaPairExcursionDensity
