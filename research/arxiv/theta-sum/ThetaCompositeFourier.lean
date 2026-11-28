import ThetaFrequencyFibers
import ThetaGcdMass

/-! For odd k the principal gcd term in S(k) comes from the zero divisors at
nonzero additive frequencies. -/
namespace Arxiv.«2501.03234».ThetaCompositeFourier
open Finset ThetaFourier ThetaOddSquare ThetaFrequencyFibers
variable {k : ℕ} [NeZero k]

private lemma gcd_nonzero :
    (∑ t∈univ.erase (0:ZMod k),t.val.gcd k)+k=gcdMass k := by
  rw [sum_nonzero (f:=fun t : ZMod k => t.val.gcd k)]
  have he : ∑ n∈Ico 1 k,(n:ZMod k).val.gcd k = ∑ n∈Ico 1 k,n.gcd k :=
    sum_congr rfl (fun n hn => by rw [ZMod.val_natCast_of_lt (mem_Ico.mp hn).2])
  rw [he]
  have hk := NeZero.pos k
  unfold gcdMass
  have H := sum_Ico_eq_sum_range (fun j : ℕ => j.gcd k) 1 (k+1)
  rw [sum_Ico_succ_top (by omega),Nat.gcd_self] at H
  simpa only [Nat.add_sub_cancel,Nat.add_comm 1] using H

private noncomputable def singular (t : ZMod k) : ℕ := ∑ a∈odds k,if a*t=0 then 1 else 0

private lemma singular_card (ho : k%2=1) (t : ZMod k) :
    2*singular t+1=t.val.gcd k := by
  have H := zero_fiber t
  rw [←sum_erase_add _ _ (mem_univ (0:ZMod k)),split_sign ho] at H
  simpa only [singular,two_mul,sum_add_distrib,neg_mul,neg_eq_zero,zero_mul,if_true] using H

private lemma sum_singular (ho : k%2=1) :
    2*(∑ t∈univ.erase (0:ZMod k),singular t)+2*(k/2)+k=gcdMass k := by
  have hcard : (univ.erase (0:ZMod k)).card=k-1 := by simp
  calc _ = (∑ t∈univ.erase (0:ZMod k),(2*singular t+1))+k := by
         rw [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one,hcard,Nat.cast_id]
         omega
       _ = _ := by simp_rw [singular_card ho]; exact gcd_nonzero

private lemma amp_pair (ho : k%2=1) {t : ZMod k} (ht : t≠0) :
    amp (odds k) t+amp (odds k) (-t)= -1 := by
  have H := orthog t
  rw [if_neg ht,←sum_erase_add _ _ (mem_univ (0:ZMod k)),split_sign ho] at H
  simpa only [amp,mul_zero,AddChar.map_zero_eq_one,sum_add_distrib,←eq_neg_iff_add_eq_zero,
    mul_comm t,neg_mul,mul_neg,zero_mul] using H

private noncomputable def regular (t : ZMod k) : ℂ := if t=0 then 0 else amp (odds k) t
private noncomputable def rest (t : ZMod k) : ℂ := ∑ a∈odds k,regular (a*t)

private theorem split_slice (t : ZMod k) :
    ∑ a∈odds k,amp (odds k) (a*t)=((odds k).card:ℂ)*singular t+rest t := by
  have he (a : ZMod k) : amp (odds k) (a*t)=((odds k).card:ℂ)*(if a*t=0 then 1 else 0)+regular (a*t) := by
    by_cases h : a*t=0
    · simp [h,regular,amp]
    · simp [h,regular]
  simp_rw [he,sum_add_distrib,←mul_sum]
  simp [singular,rest]

private theorem regular_bound (ho : k%2=1) (t : ZMod k) : ‖rest t‖ ≤ (k:ℝ)*harmonic (k/2) := by
  have h (a : ZMod k) : ‖regular (a*t)‖ ≤ weight (a*(2*t)) := by
    by_cases hz : a*t=0
    · rw [show a*(2*t)=2*(a*t) by ring,hz]; simp [regular,weight]
    · rw [regular,if_neg hz,show a*(2*t)=2*(a*t) by ring]
      apply amp_le_weight ho
      obtain ⟨v,hv⟩ := two_unit (p:=k) ho
      rw [←hv]; simpa using hz
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun a _ => h a)).trans
  exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by unfold weight; positivity)).trans (slice_weight ho _)

private theorem total_singular (ho : k%2=1) :
    2*(∑ t∈univ.erase (0:ZMod k),amp (odds k) (-t)*(singular t:ℂ))=
    -((∑ t∈univ.erase (0:ZMod k),singular t:ℕ):ℂ) := by
  have H : (∑ t∈univ.erase (0:ZMod k),amp (odds k) (-t)*(singular t:ℂ))=
      ∑ t∈univ.erase (0:ZMod k),amp (odds k) t*(singular t:ℂ) := by
    apply sum_nbij' (fun t => -t) (fun t => -t) <;> simp [singular]
  rw [two_mul,H] -- rewrite the first copy back before combining frequency pairs
  conv_lhs => lhs; rw [←H]
  push_cast
  rw [←sum_add_distrib,←sum_neg_distrib]
  apply sum_congr rfl
  intro t ht
  rw [←add_mul,add_comm,amp_pair ho (mem_erase.mp ht).1,neg_one_mul]

private theorem decomposition (ho : k%2=1) :
    (k:ℂ)*S k+(k/2:ℕ)*((gcdMass k:ℂ)-k)=
    4*∑ t∈univ.erase (0:ZMod k),amp (odds k) (-t)*rest t := by
  let m := k/2
  have hm : k=2*m+1 := by dsimp [m]; omega
  have hmk : (k:ℂ)=2*(m:ℂ)+1 := by exact_mod_cast hm
  have hs := S_triples ho
  have htrip := expand_triples (odds k)
  rw [←sum_erase_add _ _ (mem_univ (0:ZMod k))] at htrip
  simp only [neg_zero,mul_zero,amp,AddChar.map_zero_eq_one,sum_const,nsmul_eq_mul,mul_one] at htrip
  change (k:ℂ)*triples (odds k)=
    (∑ t∈univ.erase (0:ZMod k),amp (odds k) (-t)*∑ a∈odds k,amp (odds k) (a*t))+
    (odds k).card*((odds k).card*(odds k).card) at htrip
  simp_rw [split_slice,mul_add,sum_add_distrib] at htrip
  have hfactor (t : ZMod k) : amp (odds k) (-t)*((odds k).card*(singular t:ℂ))=
     (odds k).card*(amp (odds k) (-t)*(singular t:ℂ)) := by ring
  simp_rw [hfactor,←mul_sum] at htrip
  have hc : (odds k).card=m := card_odds ho
  rw [hc] at hs htrip
  have hsg := total_singular (k:=k) ho
  have hg : 2*((∑ t∈univ.erase (0:ZMod k),singular t:ℕ):ℂ)+2*(m:ℂ)+k=gcdMass k := by
    exact_mod_cast sum_singular (k:=k) ho
  change (k:ℂ)*S k+(m:ℂ)*_ = _
  linear_combination (k:ℂ)*hs + 4*htrip + 2*(m:ℂ)*hsg - (m:ℂ)*hg - 2*(m:ℂ)^2*hmk

/-- Uniform composite-modulus extension of the prime centered Fourier estimate. -/
theorem centered_gcd_bound (ho : k%2=1) :
    |(k:ℝ)*S k+(k/2:ℕ)*((gcdMass k:ℝ)-k)| ≤ 4*((k:ℝ)*harmonic (k/2))^2 := by
  have hm := mass_odds (p:=k) ho
  have hs : ‖∑ t∈univ.erase (0:ZMod k),amp (odds k) (-t)*rest t‖ ≤ ((k:ℝ)*harmonic (k/2))^2 := by
    apply (norm_sum_le _ _).trans
    calc _ ≤ ∑ t∈univ.erase (0:ZMod k),‖amp (odds k) (-t)‖*((k:ℝ)*harmonic (k/2)) := by
           apply sum_le_sum; intro t _; rw [norm_mul]; gcongr; exact regular_bound ho t
         _ ≤ _ := by
           rw [←sum_mul,sq]
           apply mul_le_mul_of_nonneg_right _ ((mass_nonneg _).trans hm)
           apply le_trans _ hm
           apply le_of_eq
           exact sum_nbij' (fun t => -t) (fun t => -t) (by simp) (by simp) (by simp) (by simp) (by simp)
  have H := congrArg norm (decomposition ho)
  rw [norm_mul] at H
  have he : ‖(k:ℂ)*S k+(k/2:ℕ)*((gcdMass k:ℂ)-k)‖=|(k:ℝ)*S k+(k/2:ℕ)*((gcdMass k:ℝ)-k)| := by
    rw [←Real.norm_eq_abs,←Complex.norm_real]; push_cast; rfl
  rw [←he,H,show ‖(4:ℂ)‖=4 by norm_num]
  exact mul_le_mul_of_nonneg_left hs (by norm_num)

#print axioms decomposition
#print axioms centered_gcd_bound
end Arxiv.«2501.03234».ThetaCompositeFourier
