import ThetaLargeIdentityMeans
import ThetaUnboundedExcursions

/-! Second-moment conversion of a large class mean into a quantitative tail probability. -/
namespace Arxiv.«2501.03234».ThetaClassTailSize
open Finset Filter MeasureTheory ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaPrimeDensity
open ThetaDiagonalConstant ThetaDyadicLaw ThetaLargeIdentityMeans ThetaFactorialSequence ThetaPrimeLaw ThetaProfiniteUnits
open scoped Topology

private theorem count_from_mean (X : ℕ) (C a : ℝ) (ha : 0≤ a)
    (f : ℕ → ℝ) (D : Finset ℕ) (hD : D⊆Nat.primesLE X)
    (hmean : D.card*(a+1) ≤ ∑ p∈D,f p)
    (henergy : ∑ p∈Nat.primesLE X,(f p)^2 ≤ C*X.primeCounting) :
    (D.card:ℝ)^2 ≤ ((primeSet (fun p => a< f p) X).card:ℝ)*(C*X.primeCounting) := by
  classical
  let A := D.filter (fun p => a< f p)
  let G := primeSet (fun p => a< f p) X
  have hsub : A⊆G := fun p hp => mem_filter.mpr ⟨hD (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩
  have hA : (D.card:ℝ)≤∑ p∈G,f p := by
    have hb : ∑ p∈D,f p ≤ ∑ p∈D, (a+(if a< f p then f p else 0)) := by
      apply sum_le_sum; intro p _; split_ifs <;> linarith
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←sum_filter] at hb
    have hG := sum_le_sum_of_subset_of_nonneg (f:=f) hsub (fun i hi _ => ha.trans (mem_filter.mp hi).2.le)
    dsimp only [A] at hG; linarith
  have hcs := sum_mul_sq_le_sq_mul_sq G (fun _ => (1:ℝ)) f
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hA 2).trans (hcs.trans ?_)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _ => sq_nonneg (f i))).trans henergy

/-- Uniformly for large T, a positive proportion of all primes exceed the
specified centered threshold, with an explicit dependence on the modulus. -/
theorem prime_lower (hAP : ProgressionMangoldt) : ∃ C : ℝ, 0< C ∧ ∀ᶠ T : ℕ in atTop,
    ∀ᶠ X : ℕ in atTop, X.primeCounting/(C*((modulus T:ℕ):ℝ)^2) ≤
      ((primeSet (fun p => diagonalConstant+(Real.log T)^2/(32*Real.pi^2)<(S p:ℝ)/p-Real.log p/2) X).card:ℝ) := by
  obtain ⟨_,V,_,_,_,_,hsec,_⟩ := S_prime_class_statistics hAP
  let K := |V|+1
  have hK : 0< K := by dsimp [K]; positivity
  refine ⟨4*K,by positivity,?_⟩
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [means hAP,ht.eventually_ge_atTop (8*Real.pi),eventually_ge_atTop (2:ℕ)] with T hh hlog hT
  let m := modulus T
  have hm : 2≤ m := Nat.le_of_dvd (pow_pos (Nat.factorial_pos _) _) ((Nat.dvd_factorial (by decide : 0<2) hT).trans (dvd_pow_self _ (by omega : T≠0)))
  have hm' : 0<(m:ℝ) := by exact_mod_cast (by omega : 0< m)
  have hφ : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0< m)
  obtain ⟨L,hL,H⟩ := hh
  let a := (Real.log T)^2/(32*Real.pi^2)
  have ha : 0≤ a := by dsimp [a]; positivity
  have he : diagonalConstant+a+1< L := by
    have hsq := pow_le_pow_left₀ (by positivity : 0≤8*Real.pi) (show 8*Real.pi≤ Real.log T from hlog) 2
    dsimp [a]; field_simp at hL ⊢; nlinarith [Real.pi_pos]
  have hfrac : 1/(2*(m:ℝ)) < 1/m.totient := by
    apply one_div_lt_one_div_of_lt hφ
    have hle : (m.totient:ℝ)≤ m := by exact_mod_cast Nat.totient_le m
    linarith
  have hD := (class_prime_density hAP (by omega) (Nat.coprime_one_left _) hm).eventually_const_lt hfrac
  have hE := hsec.eventually_le_const (show V< K by dsimp [K]; linarith [le_abs_self V])
  filter_upwards [H.eventually_const_lt he,hD,hE,((tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting).eventually_gt_atTop 0,
    class_nonempty hAP (by omega) (Nat.coprime_one_left _) hm] with X hmean hden he' hx hpos
  let D := primeSet (fun p => p%m=1) X
  let f (p : ℕ) := residual p-diagonalConstant
  have hcard : 0<(D.card:ℝ) := by exact_mod_cast card_pos.mpr hpos
  have hmean' : (D.card:ℝ)*(a+1) ≤ ∑ p∈D,f p := by
    change diagonalConstant+a+1 < (∑ p∈D,residual p)/(D.card:ℝ) at hmean
    have h := (lt_div_iff₀ hcard).mp hmean
    simp only [f,sum_sub_distrib,sum_const,nsmul_eq_mul]
    linarith
  have he'' : ∑ p∈Nat.primesLE X,(f p)^2 ≤ K*X.primeCounting := (div_le_iff₀ (by exact hx)).mp he'
  have hsub : D⊆Nat.primesLE X := by
    intro p hp; simp only [D,primeSet,mem_filter] at hp; exact hp.1
  have hc := count_from_mean X K a ha f D hsub hmean' he''
  have hd : (X.primeCounting:ℝ)/(2*m) ≤ D.card := by
    change 1/(2*(m:ℝ)) < (D.card:ℝ)/X.primeCounting at hden
    have h := ((lt_div_iff₀ (by exact hx)).mp hden).le
    rw [div_eq_inv_mul,←one_div]; exact h
  have hS : primeSet (fun p => a< f p) X=primeSet (fun p => diagonalConstant+a<(S p:ℝ)/p-Real.log p/2) X := by
    apply congrArg (fun P : ℕ → Prop => primeSet P X)
    funext p; apply propext
    change a < (S p:ℝ)/p-Real.log p/2-diagonalConstant ↔ _
    constructor <;> intro h <;> linarith
  rw [hS] at hc
  have hbound := (pow_le_pow_left₀ (by positivity : 0≤(X.primeCounting:ℝ)/(2*m)) hd 2).trans hc
  rw [div_le_iff₀ (by positivity : 0<4*K*(m:ℝ)^2)]
  change 0<(X.primeCounting:ℝ) at hx
  let N : ℝ := (primeSet (fun p => diagonalConstant+a<(S p:ℝ)/p-Real.log p/2) X).card
  change ((X.primeCounting:ℝ)/(2*m))^2 ≤ N*(K*X.primeCounting) at hbound
  change (X.primeCounting:ℝ)≤N*(4*K*(m:ℝ)^2)
  rw [div_pow,div_le_iff₀ (by positivity)] at hbound
  apply (mul_le_mul_iff_left₀ hx).mp
  · calc (X.primeCounting:ℝ)*X.primeCounting = (X.primeCounting:ℝ)^2 := by ring
         _ ≤ _ := hbound
         _ = _ := by ring

#print axioms prime_lower
end Arxiv.«2501.03234».ThetaClassTailSize
