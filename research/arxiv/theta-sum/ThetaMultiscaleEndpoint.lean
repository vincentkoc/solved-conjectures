import ThetaEndpointScales
import ThetaPrimeConcentration

/-! Prime-counting endpoint transfer for the multiscale signed theta estimate. -/
namespace Arxiv.«2501.03234».ThetaMultiscaleEndpoint
open Finset Filter Real ThetaPrimeDensity ThetaDenominatorBandScales ThetaPrimeBandCalibration ThetaEndpointScales
open scoped Topology
noncomputable section

private theorem member {X p : ℕ} {Q : ℕ → Prop} : p∈primeSet Q X ↔ p≤X ∧ p.Prime ∧ Q p := by
  classical simp only [primeSet,mem_filter,Nat.mem_primesLE,and_assoc]

theorem transfer : ∃ A : ℝ,0<A ∧ ∀ Q : ℕ → Prop,
    (∀ᶠ p : ℕ in atTop,p.Prime → Q p → A*(width p)^2 ≤ |(S p:ℝ)/p-log p/2|) →
    ∀ᶠ X : ℕ in atTop,((primeSet Q X).card:ℝ) ≤
      Nat.primeCounting X*exp (-(rate X/33554432)) := by
  classical
  obtain ⟨A,D,hA,hD,hband⟩ := band
  refine ⟨A,hA,fun Q hQ => ?_⟩
  let B : ℝ := (1+D)*2^64
  let t : ℝ := log 2/2
  have ht : 0<t := by dsimp [t];positivity
  have hB : 0<B := by dsimp [B];positivity
  have hab := index_tendsto.eventually (absorb (K:=128*B/t) (by positivity))
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨N₀,h₀⟩ := eventually_atTop.mp (((index_tendsto.eventually hband).and hab).and (hlog.eventually_ge_atTop 1))
  obtain ⟨p₀,hp₀⟩ := eventually_atTop.mp hQ
  filter_upwards [eventually_ge_atTop ((256:ℕ)^64),eventually_ge_atTop ((max N₀ p₀)^64),
    prime_count_lower] with X hX hbig hcheb
  obtain ⟨N,hN,hlow,hlo,hhi⟩ := ThetaPrimeConcentration.dyadic_cover hX
  have hN₀ : max N₀ p₀ ≤ N := by
    by_contra! lt
    exact (Nat.pow_lt_pow_left lt (by norm_num : 64≠0)).not_ge (hbig.trans hlo)
  obtain ⟨⟨hb,ha⟩,hlogN⟩ := h₀ N ((le_max_left ..).trans hN₀)
  let h := index N
  obtain ⟨hP,h2P⟩ := bracket hlogN
  let E := primeSet Q X
  let U := E.filter (N^56≤·)
  have hU := hb N hN hP U (by
    intro p hp
    obtain ⟨he,hh⟩ := mem_filter.mp hp
    obtain ⟨hx,hpr,hq⟩ := member.mp he
    have hnp := (Nat.le_self_pow (by decide : 56≠0) N).trans hh
    exact ⟨hpr,hh,hx.trans hlo,hp₀ p (((le_max_right ..).trans hN₀).trans hnp) hpr hq⟩)
  have hsub : E⊆range (N^56) ∪ U := by
    intro p hp
    rcases lt_or_ge p (N^56) with hl|hu
    · exact mem_union_left _ (mem_range.mpr hl)
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,hu⟩)
  have hc : (E.card:ℝ)≤(N:ℝ)^56+U.card := by
    exact_mod_cast (card_le_card hsub).trans ((card_union_le ..).trans_eq (by rw [card_range]))
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hx : 0<(X:ℝ) := by exact_mod_cast ((show 0<(256:ℕ)^64 by positivity).trans_le hX)
  have hsmall : (N:ℝ)^56 ≤ (N:ℝ)^64*exp (-saving h) := by
    have eq (k : ℕ) : (N:ℝ)^k=exp ((k:ℝ)*log N) := by rw [exp_nat_mul,exp_log hn]
    rw [eq 56,eq 64,←exp_add,exp_le_exp];norm_num
    linarith only [(saving_le h).2,hP,(bound_scale h).1]
  have hNX : N ≤ X := (Nat.le_self_pow (by decide : 56≠0) N).trans (hlow.trans (Nat.div_le_self ..))
  have hXP : (scale h:ℝ) ≤ log X := hP.trans (log_le_log hn (by exact_mod_cast hNX))
  have hlX := log_le_log hx (show (X:ℝ)≤(N:ℝ)^64 by exact_mod_cast hlo)
  rw [log_pow] at hlX
  norm_num only [Nat.cast_ofNat] at hlX
  change log (N:ℝ) ≤ 2*(scale h:ℝ) at h2P
  have hceil : log X ≤ 128*(scale h:ℝ) := by linarith only [hlX,h2P]
  have hscale : (N:ℝ)^64≤2^64*(X:ℝ) := by exact_mod_cast hhi
  let w := (h:ℝ)+2
  have hw : 1≤w := by dsimp [w];linarith [Nat.cast_nonneg (α:=ℝ) h]
  have hw₀ : 0≤w := by linarith
  have hcount : (E.card:ℝ) ≤ B*w*X*exp (-saving h) := by
    have h₁ := mul_le_mul_of_nonneg_right hw (show 0≤(N:ℝ)^64*exp (-saving h) by positivity)
    change (U.card:ℝ) ≤ D*w*(N:ℝ)^64*exp (-saving h) at hU
    calc _ ≤ (1+D)*w*(N:ℝ)^64*exp (-saving h) := by linarith only [hc,hU,hsmall,h₁]
         _ ≤ (1+D)*w*(2^64*(X:ℝ))*exp (-saving h) :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity)) (exp_pos _).le
         _ = _ := by dsimp [B];ring
  change t*(X:ℝ) ≤ (Nat.primeCounting X:ℝ)*log X at hcheb
  have hlog' := mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg (α:=ℝ) (Nat.primeCounting X))
  have hprime : (X:ℝ) ≤ (Nat.primeCounting X:ℝ)*(128*(scale h:ℝ)/t) := by
    rw [←mul_div_assoc,le_div_iff₀ ht];linarith only [hcheb,hlog']
  have hfinal : (E.card:ℝ) ≤ (Nat.primeCounting X:ℝ)*exp (-(saving h/2)) := by
    have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprime (mul_nonneg hB.le hw₀)) (exp_pos (-saving h)).le
    have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (α:=ℝ) (Nat.primeCounting X))) (exp_pos (-saving h)).le
    calc _ ≤ B*w*((Nat.primeCounting X:ℝ)*(128*(scale h:ℝ)/t))*exp (-saving h) := hcount.trans h₁
         _ = (Nat.primeCounting X:ℝ)*((128*B/t)*w*(scale h:ℝ))*exp (-saving h) := by ring
         _ ≤ (Nat.primeCounting X:ℝ)*exp (saving h/2)*exp (-saving h) := h₂
         _ = _ := by rw [mul_assoc,←exp_add];congr 2;ring
  exact hfinal.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg (compare hXP hceil))) (Nat.cast_nonneg _))

#print axioms transfer
end
end Arxiv.«2501.03234».ThetaMultiscaleEndpoint
