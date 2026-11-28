import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-! Reciprocal-totient tail by summing over squarefree divisor multiples. -/
namespace Arxiv.«2501.03234».ThetaTotientTail
open Finset
noncomputable section

private theorem multiples (s : Finset ℕ) {d : ℕ} (hd : 0<d) (Y : ℕ) (hY : 0<Y)
    (hs : ∀ n∈s,Y≤n ∧ d∣n) :
    ∑ n∈s,1/(n:ℝ)^2 ≤ 2/((d:ℝ)*Y) := by
  induction s using Finset.induction_on_min generalizing Y with
  | empty => simp; positivity
  | insert n s hmin ih =>
    have hh := hs n (mem_insert_self n s)
    have hn : 0<n := hY.trans_le hh.1
    have hn' : 0<(n:ℝ) := by exact_mod_cast hn
    have hd' : 0<(d:ℝ) := by exact_mod_cast hd
    have hY' : 0<(Y:ℝ) := by exact_mod_cast hY
    have hdn : (d:ℝ)≤n := by exact_mod_cast Nat.le_of_dvd hn hh.2
    have hsmall := ih (n+d) (by omega) (by
      intro k hk
      have hdk := (hs k (mem_insert_of_mem hk)).2
      have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt (hmin k hk)) (Nat.dvd_sub hdk hh.2)
      exact ⟨by have := hmin k hk; omega,hdk⟩)
    rw [sum_insert (fun h => (hmin n h).false)]
    push_cast at hsmall
    calc _ ≤ 1/(n:ℝ)^2 + 2/((d:ℝ)*(n+d)) := by linarith
         _ ≤ 2/((d:ℝ)*n) := by
             field_simp
             nlinarith only [mul_nonneg hd'.le (sub_nonneg.mpr hdn)]
         _ ≤ _ := by gcongr; exact_mod_cast hh.1

private def w (p : ℕ) : ℝ := ((p:ℝ)-1)⁻¹
private def a (t : Finset ℕ) : ℝ := ∏ p∈t,w p
private def d (t : Finset ℕ) : ℕ := ∏ p∈t,p

private theorem totient_product {n : ℕ} (hn : 0<n) : (n:ℝ)/n.totient=∏ p∈n.primeFactors,((p:ℝ)/(p-1)) := by
  have ht : 0<(n.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  let s := n.primeFactors
  have hs (p : ℕ) (hp : p∈s) : 2≤p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hd : 0<∏ p∈s,((p:ℝ)-1) := prod_pos (fun p hp => by
    have hh : (2:ℝ)≤p := by exact_mod_cast hs p hp
    linarith)
  change (n:ℝ)/n.totient=∏ p∈s,((p:ℝ)/(p-1))
  rw [prod_div_distrib,div_eq_div_iff ht.ne' hd.ne']
  have hprod : (∏ p∈s,((p:ℝ)-1))=(((∏ p∈s,(p-1)):ℕ):ℝ) := by
    rw [Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (by have := hs p hp; omega),Nat.cast_one]
  rw [hprod,←Nat.cast_prod,mul_comm _ (n.totient:ℝ)]
  exact_mod_cast (Nat.totient_mul_prod_primeFactors n).symm

private theorem calc_row (P : Finset ℕ) {n : ℕ} (hn : 0<n) (hs : n.primeFactors⊆P) :
    (n:ℝ)/n.totient=∑ t∈P.powerset,if t⊆n.primeFactors then a t else 0 := by
  classical
  have he : P.powerset.filter (·⊆n.primeFactors)=n.primeFactors.powerset := by
    ext t
    simp only [mem_filter,mem_powerset,and_iff_right_iff_imp]
    exact fun h => h.trans hs
  rw [←sum_filter,he,totient_product hn]
  unfold a
  rw [←prod_one_add]
  apply prod_congr rfl
  intro p hp
  have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  dsimp only [w]
  field_simp [show (p:ℝ)-1≠0 by linarith]
  ring

theorem reciprocal_pair_tail (s : Finset ℕ) (L : ℕ) (hL : 2≤L) (h : ∀ p∈s,L≤p) :
    ∑ p∈s,((p:ℝ)-1)⁻¹/p ≤ 1/((L:ℝ)-1) := by
  change ∑ p∈s,w p/p ≤ 1/((L:ℝ)-1)
  induction s using Finset.induction_on_min generalizing L with
  | empty =>
    have h : (2:ℝ)≤L := by exact_mod_cast hL
    simp only [sum_empty]; exact div_nonneg (by norm_num) (by linarith)
  | insert p s hmin ih =>
    have hLp := h p (mem_insert_self p s)
    have hp : (2:ℝ)≤p := by exact_mod_cast hL.trans hLp
    have hsmall := ih (p+1) (by omega) (by intro k hk; exact hmin k hk)
    rw [sum_insert (fun hmm => (hmin p hmm).false)]
    push_cast at hsmall
    rw [add_sub_cancel_right] at hsmall
    calc _ ≤ w p / p + 1/(p:ℝ) := by linarith
         _ = 1/((p:ℝ)-1) := by dsimp only [w]; field_simp [show (p:ℝ)-1≠0 by linarith]; ring
         _ ≤ _ := by
             have hLr : (2:ℝ)≤L := by exact_mod_cast hL
             exact one_div_le_one_div_of_le (by linarith) (sub_le_sub_right (by exact_mod_cast hLp) _)

private theorem prime_sum (P : Finset ℕ) (hs : ∀ p∈P,2≤p) :
    ∑ p∈P,w p/p ≤ 1 := by
  have h := reciprocal_pair_tail P 2 (by decide) hs
  norm_num at h
  exact h

private theorem product_le (P : Finset ℕ) (hs : ∀ p∈P,2≤p) :
    ∑ t∈P.powerset,a t/(d t:ℝ) ≤ 3 := by
  have he (t : Finset ℕ) : a t/(d t:ℝ)=∏ p∈t,(w p/p) := by
    rw [a,d,Nat.cast_prod,prod_div_distrib]
  simp_rw [he]
  rw [←prod_one_add]
  calc _ ≤ ∏ p∈P,Real.exp (w p/p) := by
             apply prod_le_prod
             · intro p hp; have h : (2:ℝ)≤p := by exact_mod_cast hs p hp
               have hh : 0<(p:ℝ)-1 := by linarith
               exact add_nonneg zero_le_one (div_nonneg (inv_nonneg.mpr hh.le) (Nat.cast_nonneg _))
             · intro p _; linarith [Real.add_one_le_exp (w p/p)]
       _ = Real.exp (∑ p∈P,w p/p) := (Real.exp_sum ..).symm
       _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (prime_sum P hs)
       _ ≤ 3 := Real.exp_one_lt_three.le

/-- A finite tail estimate valid even when only a subset of conductors is used. -/
theorem bound (Y : ℕ) (hY : 0<Y) (s : Finset ℕ) (hs : ∀ n∈s,Y≤n) :
    ∑ n∈s,1/((n:ℝ)*n.totient) ≤ 6/Y := by
  classical
  let P := s.biUnion Nat.primeFactors
  have hP (p : ℕ) (hp : p∈P) : 2≤p := by
    obtain ⟨n,_,hn⟩ := mem_biUnion.mp hp
    exact (Nat.prime_of_mem_primeFactors hn).two_le
  have hsub (n : ℕ) (hn : n∈s) : n.primeFactors⊆P := fun _ hp => mem_biUnion.mpr ⟨n,hn,hp⟩
  have hrow (n : ℕ) (hn : n∈s) : 1/((n:ℝ)*n.totient)=
      (∑ t∈P.powerset,if t⊆n.primeFactors then a t else 0)*(1/(n:ℝ)^2) := by
    rw [←calc_row P (hY.trans_le (hs n hn)) (hsub n hn)]
    have h : 0<(n:ℝ) := by exact_mod_cast hY.trans_le (hs n hn)
    field_simp
  have hm (t : Finset ℕ) (ht : t∈P.powerset) :
      ∑ n∈s with t⊆n.primeFactors,1/(n:ℝ)^2 ≤ 2/((d t:ℝ)*Y) := by
    have hd : 0<d t := prod_pos (fun p hp => by have := hP p (mem_powerset.mp ht hp); omega)
    apply multiples _ hd _ hY
    intro n hn
    obtain ⟨hsn,htn⟩ := mem_filter.mp hn
    exact ⟨hs n hsn,(prod_dvd_prod_of_subset t n.primeFactors id htn).trans (Nat.prod_primeFactors_dvd n)⟩
  calc _ = ∑ n∈s,(∑ t∈P.powerset,if t⊆n.primeFactors then a t else 0)*(1/(n:ℝ)^2) := sum_congr rfl hrow
       _ = ∑ t∈P.powerset,a t*∑ n∈s with t⊆n.primeFactors,1/(n:ℝ)^2 := by
             simp only [sum_mul,sum_filter,mul_sum,ite_mul,mul_ite,zero_mul,mul_zero]
             rw [sum_comm]
       _ ≤ ∑ t∈P.powerset,a t*(2/((d t:ℝ)*Y)) := by
             apply sum_le_sum
             intro t ht
             apply mul_le_mul_of_nonneg_left (hm t ht)
             apply prod_nonneg
             intro p hp
             have hh : (2:ℝ)≤p := by exact_mod_cast hP p (mem_powerset.mp ht hp)
             exact inv_nonneg.mpr (show 0≤(p:ℝ)-1 by linarith)
       _ = (∑ t∈P.powerset,a t/(d t:ℝ))*(2/Y) := by rw [sum_mul]; apply sum_congr rfl; intros; ring
       _ ≤ 3*(2/Y) := mul_le_mul_of_nonneg_right (product_le P hP) (by positivity)
       _ = _ := by ring

#print axioms bound
end
end Arxiv.«2501.03234».ThetaTotientTail
