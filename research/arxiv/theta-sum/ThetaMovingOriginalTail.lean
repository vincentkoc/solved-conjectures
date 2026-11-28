import ThetaUniformPrimeBand
import ThetaPrimeConcentration

/-! Uniform finite exceptional counts for moving absolute deviations. -/
namespace Arxiv.«2501.03234».ThetaMovingOriginalTail
open Finset Real Filter ThetaPrimeDensity
noncomputable section

def exceptions (d : ℝ) (X : ℕ) :=
  primeSet (fun p => d*(p:ℝ)≤|(S p:ℝ)-(p:ℝ)*log p/2|) X

theorem original_of : ∃ A D H : ℝ, 0<A ∧ 0<D ∧ 1≤H ∧ ∀ᶠ X : ℕ in atTop,
    ∀ {h : ℝ} {k : ℕ}, H≤h → 1≤k → (k:ℝ)≤exp (h/8) → 128*(k:ℝ)^2*h≤log X →
      ∀ P : ℕ → Prop, (∀ p, p.Prime → p≤X → X≤p^2 → P p →
        A*h^2*(p:ℝ)≤|(S p:ℝ)-(p:ℝ)*log p/2|) → ((primeSet P X).card:ℝ)≤
        D*Nat.primeCounting X*exp (-((k:ℝ)*h)/128) := by
  classical
  obtain ⟨A,B,hA,hB,hb⟩ := ThetaUniformPrimeBand.band
  obtain ⟨H,h₀⟩ := eventually_atTop.mp hb
  let c := log 2/2
  have hc : 0<c := div_pos (log_pos (by norm_num)) (by norm_num)
  let D := (1+B)*2^64*64/c
  have hD : 0<D := by dsimp [D];positivity
  refine ⟨A,D,max 1 H,hA,hD,le_max_left ..,?_⟩
  filter_upwards [eventually_ge_atTop ((256:ℕ)^64),prime_count_lower] with X hX hcount
  intro h k hh hk hke hsize P hP
  obtain ⟨N,hN,_,hlo,hhi⟩ := ThetaPrimeConcentration.dyadic_cover hX
  have hx : 0<(X:ℝ) := by exact_mod_cast (show 0<X from (show 0<(256:ℕ)^64 by positivity).trans_le hX)
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hL := log_le_log hx (show (X:ℝ)≤(N:ℝ)^64 by exact_mod_cast hlo)
  rw [log_pow] at hL
  have hcap : 2*(k:ℝ)^2*h≤log N := by norm_num at hL;linarith
  let E := primeSet P X
  let U := E.filter (N^56≤·)
  have hu := h₀ h ((le_max_right ..).trans hh) hN hk hke hcap U (by
    intro p hp
    obtain ⟨he,hl⟩ := mem_filter.mp hp
    change p∈primeSet P X at he
    simp only [primeSet,mem_filter,Nat.mem_primesLE] at he
    refine ⟨he.1.2,hl,he.1.1.trans hlo,?_⟩
    have hp' : 0<(p:ℝ) := by exact_mod_cast he.1.2.pos
    have hid : ((S p:ℝ)/p-log p/2)*p=(S p:ℝ)-p*log p/2 := by field_simp
    apply (mul_le_mul_iff_left₀ hp').mp
    have hxpp : X≤p^2 := calc
      X ≤ N^64 := hlo
      _ ≤ N^(56*2) := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = _ := pow_mul N 56 2
      _ ≤ _ := Nat.pow_le_pow_left hl 2
    simpa only [←hid,abs_mul,abs_of_pos hp'] using hP p he.1.2 he.1.1 hxpp he.2)
  have hsub : E⊆range (N^56) ∪ U := by
    intro p he
    rcases lt_or_ge p (N^56) with hl|hl
    · exact mem_union_left _ (mem_range.mpr hl)
    · exact mem_union_right _ (mem_filter.mpr ⟨he,hl⟩)
  have hcard : (E.card:ℝ)≤(N:ℝ)^56+U.card := by
    exact_mod_cast (card_le_card hsub).trans ((card_union_le ..).trans_eq (by rw [card_range]))
  let Q := (k:ℝ)*h
  have hh' : 0≤h := by linarith only [(le_max_left 1 H).trans hh]
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hq : Q≤log N := by
    have hkk : (k:ℝ)≤(k:ℝ)^2 := by nlinarith only [mul_le_mul_of_nonneg_left hk' (Nat.cast_nonneg (α:=ℝ) k)]
    dsimp only [Q];linarith only [mul_le_mul_of_nonneg_right hkk hh',hcap,mul_nonneg (sq_nonneg (k:ℝ)) hh']
  have hq' : 0≤Q := by dsimp [Q];positivity
  have hLN : 0<log (N:ℝ) := log_pos (by exact_mod_cast hN)
  have hsmall : (N:ℝ)^56*log N≤(N:ℝ)^64*exp (-Q/128) := by
    calc _ ≤ (N:ℝ)^56*N := mul_le_mul_of_nonneg_left (log_le_self hn.le) (by positivity)
         _ = (N:ℝ)^57 := by ring
         _ ≤ _ := by
           have hp (m : ℕ) : (N:ℝ)^m=exp ((m:ℝ)*log N) := by rw [exp_nat_mul,exp_log hn]
           rw [hp 57,hp 64,←exp_add,exp_le_exp]
           norm_num
           linarith
  have hscale : (N:ℝ)^64≤2^64*(X:ℝ) := by exact_mod_cast hhi
  have hcount' : c*(X:ℝ)≤Nat.primeCounting X*(64*log N) := hcount.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hL) (Nat.cast_nonneg _))
  have hmain : (1+B)*(N:ℝ)^64≤D*Nat.primeCounting X*log N := calc
    _ ≤ (1+B)*(2^64*(X:ℝ)) := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (D/64)*(c*(X:ℝ)) := by dsimp [D];field_simp
    _ ≤ (D/64)*(Nat.primeCounting X*(64*log N)) := mul_le_mul_of_nonneg_left hcount' (by positivity)
    _ = _ := by ring
  change (E.card:ℝ)≤_
  apply (mul_le_mul_iff_left₀ hLN).mp
  calc _ ≤ ((1+B)*(N:ℝ)^64)*exp (-Q/128) := by linarith only [mul_le_mul_of_nonneg_right hcard hLN.le,hu,hsmall]
       _ ≤ (D*Nat.primeCounting X*log N)*exp (-Q/128) := mul_le_mul_of_nonneg_right hmain (exp_pos _).le
       _ = _ := by ring

theorem original : ∃ A D H : ℝ, 0<A ∧ 0<D ∧ 1≤H ∧ ∀ᶠ X : ℕ in atTop,
    ∀ {h : ℝ} {k : ℕ}, H≤h → 1≤k → (k:ℝ)≤exp (h/8) → 128*(k:ℝ)^2*h≤log X →
      ((exceptions (A*h^2) X).card:ℝ)≤D*Nat.primeCounting X*exp (-((k:ℝ)*h)/128) := by
  obtain ⟨A,D,H,hA,hD,hH,hb⟩ := original_of
  refine ⟨A,D,H,hA,hD,hH,?_⟩
  filter_upwards [hb] with X hX
  intro h k hh hk he hs
  exact hX hh hk he hs _ (fun _ _ _ _ h => h)

#print axioms original_of
#print axioms original
end
end Arxiv.«2501.03234».ThetaMovingOriginalTail
