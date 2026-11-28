import ThetaCompatibleMeans
import ThetaClassTailSize

/-! Quantified opposite excursions over primes in a prescribed reduced class. -/
namespace Arxiv.«2501.03234».ThetaCompatibleCounts
open Finset Filter Real ThetaCharacterPrimeMeans ThetaLevelCoefficients ThetaProgressionProjection
open ThetaPrimeDensity ThetaDyadicLaw ThetaNaturalPrimeMeans ThetaFactorialSequence ThetaClassTailSize
open ThetaDiagonalConstant
open scoped Topology
noncomputable section

private lemma count {m q n r : ℕ} [NeZero m] (hn : n< m) (hnc : n.Coprime m)
    (hqm : q∣m) (hr : n%q=r) (hAP : ProgressionMangoldt)
    {s a K : ℝ} (hs : s^2=1) (ha : 0≤ a) (hK : 0< K)
    (hp : a+1< s*predictor m n) (hE : ∀ᶠ X : ℕ in atTop,primeMean (fun p => (centered p)^2) X≤ K) :
    ∀ᶠ X : ℕ in atTop, X.primeCounting/(4*K*(m:ℝ)^2) ≤
      ((primeSet (fun p => p%q=r ∧ a< s*centered p) X).card:ℝ) := by
  classical
  have hm' : 0< (m:ℝ) := by exact_mod_cast NeZero.pos m
  have hφ : 0< (m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)
  have hfrac : 1/(2*(m:ℝ))< 1/m.totient := by
    apply one_div_lt_one_div_of_lt hφ
    have h := Nat.totient_le m
    exact_mod_cast (by omega : m.totient< 2*m)
  have hD := (class_prime_density hAP (NeZero.pos m) hnc hn).eventually_const_lt hfrac
  have hlim := (class_mean m n hnc hn hAP).const_mul s
  filter_upwards [hD,hlim.eventually_const_lt hp,hE,class_nonempty hAP (NeZero.pos m) hnc hn,
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting).eventually_gt_atTop 0]
    with X hden hmean he' hnemp hx
  let D := primeSet (fun p => p%m=n) X
  let f (p : ℕ) := if p%q=r then s*centered p else 0
  have hd : 0< (D.card:ℝ) := by exact_mod_cast card_pos.mpr hnemp
  have hmean' : (D.card:ℝ)*(a+1) ≤ ∑ p∈D,f p := by
    have heq : ∑ p∈D,f p=s*∑ p∈D,centered p := by
      rw [mul_sum]; apply sum_congr rfl; intro p hp
      simp only [D,primeSet,mem_filter] at hp
      have H := hp.2
      change p%m=n at H
      simp only [f,if_pos (show p%q=r by rw [←Nat.mod_mod_of_dvd p hqm,H,hr])]
    rw [heq]
    change a+1< s*((∑ p∈D,centered p)/D.card) at hmean
    rw [←mul_div_assoc] at hmean
    simpa only [mul_comm (D.card:ℝ)] using ((lt_div_iff₀ hd).mp hmean).le
  have he'' : ∑ p∈Nat.primesLE X,(f p)^2 ≤ K*X.primeCounting := by
    apply le_trans _ ((div_le_iff₀ (by exact hx : 0 < (X.primeCounting:ℝ))).mp (show (∑ p∈Nat.primesLE X,(centered p)^2)/(X.primeCounting:ℝ) ≤ K from he'))
    apply sum_le_sum; intro p _
    dsimp [f]; split_ifs <;> simp [mul_pow,hs,sq_nonneg]
  have hsub : D⊆Nat.primesLE X := by
    intro p hp; simp only [D,primeSet,mem_filter] at hp; exact hp.1
  have hh := count_from_mean X K a ha f D hsub hmean' he''
  have hEq : primeSet (fun p => a< f p) X = primeSet (fun p => p%q=r ∧ a< s*centered p) X := by
    apply congrArg (fun P : ℕ → Prop => primeSet P X)
    funext p; apply propext; dsimp [f]; split_ifs <;> simp_all only [true_and,false_and,not_lt.mpr ha]
  rw [hEq] at hh
  have hd' : (X.primeCounting:ℝ)/(2*m) ≤ D.card := by
    change 1/(2*(m:ℝ)) < (D.card:ℝ)/X.primeCounting at hden
    have h := ((lt_div_iff₀ (by exact hx)).mp hden).le
    rw [div_eq_inv_mul,←one_div]; exact h
  have hbound := (pow_le_pow_left₀ (by positivity : 0≤ (X.primeCounting:ℝ)/(2*m)) hd' 2).trans hh
  rw [div_le_iff₀ (by positivity : 0< 4*K*(m:ℝ)^2)]
  let N : ℝ := (primeSet (fun p => p%q=r ∧ a< s*centered p) X).card
  change ((X.primeCounting:ℝ)/(2*m))^2 ≤ N*(K*X.primeCounting) at hbound
  change (X.primeCounting:ℝ)≤ N*(4*K*(m:ℝ)^2)
  rw [div_pow,div_le_iff₀ (by positivity)] at hbound
  apply (mul_le_mul_iff_left₀ (by exact hx : 0< (X.primeCounting:ℝ))).mp
  calc (X.primeCounting:ℝ)*X.primeCounting = (X.primeCounting:ℝ)^2 := by ring
       _ ≤ _ := hbound
       _ = _ := by ring

/-- Two opposite tails have a lower fraction among all primes in the specified
class, for each large factorial parameter and then each sufficiently large X. -/
theorem sequence_counts (hAP : ProgressionMangoldt) :
    ∃ C : ℝ, 0< C ∧ ∀ q r : ℕ, 0< q → r< q → r.Coprime q →
      ∀ᶠ T : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
        let a := (log T)^2/(32*Real.pi^2)
        let N := X.primeCounting/(C*(modulus T:ℝ)^2)
        N≤ ((primeSet (fun p => p%q=r ∧ diagonalConstant+a< residual p) X).card:ℝ) ∧
        N≤ ((primeSet (fun p => p%q=r ∧ residual p< diagonalConstant-a) X).card:ℝ) := by
  classical
  obtain ⟨_,V,_,_,_,_,hsec,_⟩ := S_prime_class_statistics hAP
  let K := |V|+1
  have hK : 0< K := by dsimp [K]; positivity
  refine ⟨4*K,by positivity,?_⟩
  intro q r hq hr hc
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hE := hsec.eventually_le_const (show V< K by dsimp [K]; linarith [le_abs_self V])
  filter_upwards [ThetaCompatibleMeans.both hAP hq hr hc,ht.eventually_ge_atTop (8*Real.pi)] with T H hl
  obtain ⟨hm,hqm,n,hn,s,hs,hnc,hsc,hnq,hsq,h₁,h₂⟩ := H
  let m := modulus T
  let : NeZero m := ⟨by exact (show 0 < m by omega).ne'⟩
  let a := (log T)^2/(32*Real.pi^2)
  have ha : 0≤ a := by dsimp [a]; positivity
  have hheight : a+1< (log T)^2/(8*Real.pi^2) := by
    have hsq := pow_le_pow_left₀ (by positivity : 0≤ 8*Real.pi) (show 8*Real.pi≤ log T from hl) 2
    dsimp [a]; field_simp; nlinarith [Real.pi_pos]
  have pos := count hn hnc hqm hnq hAP (s:=1) (by norm_num) ha hK
    (by simpa only [one_mul] using hheight.trans_le h₁) hE
  rw [neg_div] at h₂
  have neg := count hs hsc hqm hsq hAP (s:=-1) (by norm_num) ha hK
    (by rw [neg_one_mul]; linarith only [hheight,h₂]) hE
  filter_upwards [pos,neg] with X hp hn
  constructor
  · apply hp.trans; apply Nat.cast_le.mpr; apply card_le_card
    intro p h; simp only [primeSet,mem_filter] at h ⊢; obtain ⟨h,hq',hh⟩ := h
    exact ⟨h,hq',by change a< 1*(residual p-diagonalConstant) at hh; linarith⟩
  · apply hn.trans; apply Nat.cast_le.mpr; apply card_le_card
    intro p h; simp only [primeSet,mem_filter] at h ⊢; obtain ⟨h,hq',hh⟩ := h
    exact ⟨h,hq',by change a< (-1)*(residual p-diagonalConstant) at hh; linarith⟩

#print axioms sequence_counts
end
end Arxiv.«2501.03234».ThetaCompatibleCounts
