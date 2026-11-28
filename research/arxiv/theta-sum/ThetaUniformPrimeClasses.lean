import ThetaWorstPrimeClasses

/-! Transfer Maynard's ordinary lower bound to every reduced class in a growing range. -/
namespace Arxiv.«2501.03234».ThetaUniformPrimeClasses
open Finset Filter Real ThetaPrimeDensity ThetaOccupancyScales
noncomputable section
open scoped Classical

def primes (X q a : ℕ) := (Nat.primesLE X).filter (fun p => p%q=a)

/-- Maynard, On the Brun--Titchmarsh theorem, Theorem 3.2, after multiplication
by the positive denominator, restricted to integral endpoints. -/
def Maynard : Prop := ∃ c : ℝ,0<c ∧ ∀ᶠ q : ℕ in atTop,∀ X a : ℕ,q^8≤X → a<q → a.Coprime q →
  c*((X:ℝ)*log q) ≤ ((primes X q a).card:ℝ)*(sqrt q*q.totient*log X)

def bad (P : ℕ → Prop) (X q a : ℕ) := ((primes X q a).filter P).card

theorem saving_tendsto : Tendsto saving atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [bounds,(tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (exp b)]
    with X hx hb
  apply exp_le_exp.mp
  have hL := hx.2.1
  have h := hx.2.2.2.2.1
  exact hb.trans ((by nlinarith [sq_nonneg (log (X:ℝ)),mul_nonneg (sq_nonneg (log (X:ℝ))) (by linarith : 0≤log (X:ℝ))] : log (X:ℝ)≤(1+log (X:ℝ))^3).trans h)

private theorem mass (H : Maynard) :
    ∃ Q : ℕ,∀ᶠ X : ℕ in atTop,∀ q a : ℕ,Q≤q → (q:ℝ)≤exp (saving X) → q^8≤X →
      a<q → a.Coprime q → (X:ℝ) ≤ (primes X q a).card*exp (4*saving X) := by
  obtain ⟨c,hc,h⟩ := H
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp (h.and ((tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1))
  refine ⟨Q,?_⟩
  filter_upwards [bounds,saving_tendsto.eventually_ge_atTop (log (1/c))] with X hx hc' q a hq he h8 ha hg
  obtain ⟨hom,hlog⟩ := hQ q hq
  have h₀ := hom X a h8 ha hg
  have hq1 : 1≤(q:ℝ) := by
    by_contra! hn
    have hz : q=0 := by exact_mod_cast (Nat.lt_one_iff.mp (show q<1 by exact_mod_cast hn))
    change 1≤log (q:ℝ) at hlog
    norm_num [hz] at hlog
  have hs : sqrt (q:ℝ) ≤ q := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith [mul_nonneg (by linarith : 0≤(q:ℝ)-1) (Nat.cast_nonneg (α:=ℝ) q)]⟩
  have ht : (q.totient:ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hL := hx.2.1
  have hL' : log (X:ℝ) ≤ exp (saving X) := by
    apply le_trans _ hx.2.2.2.2.1
    nlinarith [sq_nonneg (log (X:ℝ)),mul_nonneg (sq_nonneg (log (X:ℝ))) (by linarith : 0≤log (X:ℝ))]
  have hprod := mul_le_mul_of_nonneg_right (mul_le_mul (hs.trans he) (ht.trans he) (by positivity) (exp_pos _).le) (by linarith : 0≤log (X:ℝ))
  have hprod' := hprod.trans (mul_le_mul_of_nonneg_left hL' (by positivity))
  have hc₁ : 1/c ≤ exp (saving X) := by
    rw [←exp_log (by positivity : 0<1/c)]
    exact exp_le_exp.mpr hc'
  have hc₂ : 1≤ c*exp (saving X) := by rwa [div_le_iff₀ hc,mul_comm] at hc₁
  have hnum := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Nat.cast_nonneg (α:=ℝ) X) hlog) hc.le
  have hb := (hnum.trans h₀).trans (mul_le_mul_of_nonneg_left hprod' (Nat.cast_nonneg _))
  calc (X:ℝ) ≤ X*(c*exp (saving X)) := le_mul_of_one_le_right (Nat.cast_nonneg _) hc₂
       _ = c*X*exp (saving X) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hb (exp_pos _).le
       _ = _ := by rw [show (4:ℝ)=(4:ℕ) by norm_num,exp_nat_mul];ring

private theorem discard (P : ℕ → Prop) (X q a : ℕ) :
    ((primes X q a).filter P).card≤(primeSet P X).card := by
  apply card_le_card
  intro p hp
  obtain ⟨h,hp⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨(mem_filter.mp h).1,hp⟩

theorem relative (H : Maynard) (P : ℕ → Prop)
    (hP : ∀ᶠ X : ℕ in atTop,((primeSet P X).card:ℝ) ≤ X.primeCounting*exp (-(8*saving X))) :
    ∃ Q : ℕ,∀ᶠ X : ℕ in atTop,∀ q a : ℕ,Q≤q → (q:ℝ)≤exp (saving X) → q^8≤X →
      a<q → a.Coprime q →
      (bad P X q a:ℝ) ≤ (primes X q a).card*exp (-(4*saving X)) ∧
      0<((primes X q a).filter (fun p => ¬P p)).card := by
  obtain ⟨Q,hQ⟩ := mass H
  refine ⟨Q,?_⟩
  filter_upwards [hP,hQ,bounds] with X hE hM hx q a hq he h8 ha hg
  have hm := hM q a hq he h8 ha hg
  have hπ : X.primeCounting ≤ X := by
    rw [←Nat.primesLE_card_eq_primeCounting]
    have hsub : Nat.primesLE X ⊆ Icc 1 X := fun p hp =>
      mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos,(Nat.mem_primesLE.mp hp).1⟩
    simpa using card_le_card hsub
  have h := (Nat.cast_le.mpr (discard P X q a) : (((primes X q a).filter P).card:ℝ)≤_).trans
    (hE.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hπ) (exp_pos _).le))
  have hrel := h.trans (mul_le_mul_of_nonneg_right hm (exp_pos _).le)
  rw [mul_assoc,←exp_add,show 4*saving X+-(8*saving X)=-(4*saving X) by ring] at hrel
  refine ⟨hrel,?_⟩
  have hpos : 0<((primes X q a).card:ℝ) := by
    by_contra! h
    linarith only [mul_nonpos_of_nonpos_of_nonneg h (exp_pos (4*saving X)).le,hm,hx.1]
  have hlt := hrel.trans_lt (mul_lt_of_lt_one_right hpos (exp_lt_one_iff.mpr (by linarith only [hx.2.2.1])))
  have hn : ((primes X q a).filter P).card<(primes X q a).card := by exact_mod_cast hlt
  have hh := card_filter_add_card_filter_not (s:=primes X q a) P
  omega

private theorem eighth : ∀ᶠ X : ℕ in atTop,∀ q : ℕ,(q:ℝ)≤exp (saving X) → q^8≤X := by
  filter_upwards [bounds] with X hx q he
  have hu := log_nonneg hx.2.1
  have hs : 8*saving X≤log (X:ℝ) := by
    have h := div_le_self (by linarith only [hx.2.1] : 0≤log (X:ℝ)) (by linarith only [hu] : 1≤1+log (log (X:ℝ)))
    unfold saving
    linarith only [h,hx.2.1]
  have h : (q:ℝ)^8 ≤ X := by
    calc _ ≤ (exp (saving X))^8 := pow_le_pow_left₀ (Nat.cast_nonneg _) he 8
         _ = exp (8*saving X) := by rw [show (8:ℝ)=(8:ℕ) by norm_num,exp_nat_mul]
         _ ≤ _ := (le_log_iff_exp_le hx.1).mp hs
  exact_mod_cast h

/-- Every reduced class in the indicated range, with one absolute residual constant. -/
theorem centered (H : Maynard) : ∃ A : ℝ,0<A ∧ ∃ Q : ℕ,∀ᶠ X : ℕ in atTop,
    ∀ q a : ℕ,Q≤q → (q:ℝ)≤exp (saving X) → a<q → a.Coprime q →
      (bad (fun p : ℕ => A*(1+log (log p))^2≤|(S p:ℝ)/p-log p/2|) X q a:ℝ) ≤
        (primes X q a).card*exp (-(4*saving X)) := by
  obtain ⟨A,hA,hP⟩ := ThetaMultiscaleExceptions.original_centered
  have hscale (X : ℕ) : log (X:ℝ)/(1+log (log X))/33554432=8*saving X := by unfold saving;ring
  simp_rw [hscale] at hP
  obtain ⟨Q,h⟩ := relative H _ hP
  refine ⟨A,hA,Q,?_⟩
  filter_upwards [h,eighth] with X h h8 q a hq he ha hg
  exact (h q a hq he (h8 q he) ha hg).1

theorem slope (H : Maynard) (k : ℕ) : ∃ Q : ℕ,∀ᶠ X : ℕ in atTop,
    ∀ q a : ℕ,Q≤q → (q:ℝ)≤exp (saving X) → a<q → a.Coprime q →
      (bad (fun p => S p≤(k:ℤ)*p) X q a:ℝ) ≤
        (primes X q a).card*exp (-(4*saving X)) := by
  have hP := ThetaMultiscaleExceptions.original_slope k
  have hscale (X : ℕ) : log (X:ℝ)/(1+log (log X))/33554432=8*saving X := by unfold saving;ring
  simp_rw [hscale] at hP
  obtain ⟨Q,h⟩ := relative H _ hP
  refine ⟨Q,?_⟩
  filter_upwards [h,eighth] with X h h8 q a hq he ha hg
  exact (h q a hq he (h8 q he) ha hg).1

#print axioms centered
#print axioms slope
#print axioms relative
end
end Arxiv.«2501.03234».ThetaUniformPrimeClasses
