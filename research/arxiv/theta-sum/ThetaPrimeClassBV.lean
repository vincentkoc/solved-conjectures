import ThetaPositivePrimeLevel
import Mathlib.Data.Set.Card

/-! The unweighted Set.ncard Bombieri--Vinogradov statement at prime theta slopes. -/
namespace Arxiv.«2501.03234».ThetaPrimeClassBV
open Finset Filter Real ThetaPositiveDistribution ThetaWorstPrimeClasses ThetaOccupancyScales
noncomputable section

def ordinaryCount (x : ℝ) (q : ℕ) (a : ZMod q) : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q)=a ∧ p≤x}.ncard

def slopeCount (k : ℕ) (x : ℝ) (q : ℕ) (a : ZMod q) : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q)=a ∧ p≤x ∧ (k:ℤ)*p<S p}.ncard

def selectedCount (P : ℕ → Prop) (x : ℝ) (q : ℕ) (a : ZMod q) : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q)=a ∧ p≤x ∧ ¬P p}.ncard

theorem selected_slope (k : ℕ) : selectedCount (fun p => S p≤(k:ℤ)*p)=slopeCount k := by
  funext x q a
  simp only [selectedCount,slopeCount,not_le]

def Sparse (P : ℕ → Prop) := ∀ᶠ X : ℕ in atTop,∀ Q : ℕ,(Q:ℝ)^2 ≤ X*exp (saving X) →
  total (ThetaPrimeDensity.primeSet P X) Q ≤ X.primeCounting*exp (-(2*saving X))

def error (F : ℝ → (q : ℕ) → ZMod q → ℕ) (x : ℝ) (q : ℕ) : ℝ :=
  ⨆ a : (ZMod q)ˣ, |(F x q a:ℝ)-(⌊x⌋₊.primeCounting:ℝ)/q.totient|

/-- Definitionally the ordinary unweighted hypothesis at the cited revision. -/
def Ordinary : Prop := ∀ θ < (1/2:ℝ),∀ A ≥ (1:ℝ),∃ C > (0:ℝ),∀ x ≥ (3:ℝ),
  ∑ q∈Icc 1 ⌊x^θ⌋₊,error ordinaryCount x q ≤ C*x/(log x)^A

private theorem counts (P : ℕ → Prop) (X q : ℕ) [NeZero q] (a : ZMod q) :
    ordinaryCount X q a = count (ThetaPrimeDensity.primeSet (fun _ => True) X) q a.val ∧
    selectedCount P X q a = count (ThetaPrimeDensity.primeSet (fun p => ¬P p) X) q a.val := by
  classical
  have hr (p : ℕ) : (p:ZMod q)=a ↔ p%q=a.val := by
    rw [←ZMod.val_natCast q p];exact (ZMod.val_injective q).eq_iff.symm
  constructor
  · unfold ordinaryCount count
    rw [←Set.ncard_coe_finset]
    congr 1;ext p
    simp only [Set.mem_ofPred_eq,Finset.mem_coe,mem_filter,ThetaPrimeDensity.primeSet,Nat.mem_primesLE,
      hr,Nat.cast_le,and_true]
    tauto
  · unfold selectedCount count
    rw [←Set.ncard_coe_finset]
    congr 1;ext p
    simp only [Set.mem_ofPred_eq,Finset.mem_coe,mem_filter,ThetaPrimeDensity.primeSet,Nat.mem_primesLE,
      hr,Nat.cast_le]
    tauto

theorem one_selected (P : ℕ → Prop) (X q : ℕ) (hq : 0<q) :
    error (selectedCount P) X q ≤ error ordinaryCount X q+worst (ThetaPrimeDensity.primeSet P X) q := by
  let : NeZero q := ⟨hq.ne'⟩
  unfold error
  apply ciSup_le
  intro a
  have h := class_change P (le_rfl (a:=X)) (ZMod.val_lt (a:ZMod q))
    ((⌊(X:ℝ)⌋₊.primeCounting:ℝ)/q.totient)
  obtain ⟨ho,hs⟩ := counts P X q a
  rw [←ho,←hs] at h
  let F (b : (ZMod q)ˣ) := |(ordinaryCount X q b:ℝ)-(⌊(X:ℝ)⌋₊.primeCounting:ℝ)/q.totient|
  have hb := le_ciSup (Finite.bddAbove_range F) a
  change F a ≤ ⨆ b,F b at hb
  change _ ≤ (⨆ b,F b)+_
  linarith only [(abs_le.mp h).2,hb]

/-- Integer-endpoint consequence of the real-endpoint source with the same
units, floor cutoff, normalization, exponent range and arbitrary log power. -/
theorem from_sparse (H : Ordinary) {θ A : ℝ} (hθ : θ<1/2) (hA : 1≤A) {P : ℕ → Prop} (hP : Sparse P) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,
      ∑ q∈Icc 1 ⌊(X:ℝ)^θ⌋₊,error (selectedCount P) X q ≤ C*X/(log X)^A := by
  obtain ⟨C,hC,ho⟩ := H θ hθ A hA
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [hP,ThetaPositivePrimeLevel.absorption (show 0<A by linarith),
    ThetaOccupancyScales.bounds,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop 3] with X hE hsave hx h3
  let Q := ⌊(X:ℝ)^θ⌋₊
  have hQ : (Q:ℝ)^2 ≤ X*exp (saving X) := by
    have hf := Nat.floor_le (rpow_nonneg hx.1.le θ)
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) Q) hf 2
    rw [←rpow_mul_natCast hx.1.le] at hpow
    have hh : (X:ℝ)^(θ*(2:ℕ)) ≤ X := by
      calc _ ≤ (X:ℝ)^(1:ℝ) := rpow_le_rpow_of_exponent_le (by linarith) (by norm_num;linarith)
           _ = _ := rpow_one _
    exact (hpow.trans hh).trans (le_mul_of_one_le_right hx.1.le (one_le_exp (by linarith only [hx.2.2.1])))
  calc _ ≤ ∑ q∈Icc 1 Q,(error ordinaryCount X q+worst (ThetaPrimeDensity.primeSet P X) q) :=
            sum_le_sum (fun q hq => one_selected P X q (mem_Icc.mp hq).1)
       _ = (∑ q∈Icc 1 Q,error ordinaryCount X q)+total (ThetaPrimeDensity.primeSet P X) Q := by rw [total,sum_add_distrib]
       _ ≤ C*X/(log X)^A+(X:ℝ)/(log X)^A := add_le_add (ho X h3) ((hE Q hQ).trans hsave)
       _ = _ := by ring

theorem slope (H : Ordinary) {θ A : ℝ} (hθ : θ<1/2) (hA : 1≤A) (k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,
      ∑ q∈Icc 1 ⌊(X:ℝ)^θ⌋₊,error (slopeCount k) X q ≤ C*X/(log X)^A := by
  simpa only [selected_slope] using from_sparse H hθ hA (ThetaWorstPrimeClasses.slope k)

#print axioms one_selected
#print axioms from_sparse
#print axioms slope
end
end Arxiv.«2501.03234».ThetaPrimeClassBV
