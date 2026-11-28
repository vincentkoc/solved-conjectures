import ThetaIdentityFiber
import ThetaReciprocalBlocks
import ThetaTotientTail

/-! Summable envelope for rows off an identity progression. -/
namespace Arxiv.«2501.03234».ThetaSmoothRows
open Finset ThetaIdentityFiber
noncomputable section
private theorem ratio_product (s : Finset ℕ) (hs : ∀ p∈s,2≤p) :
    ∏ p∈s,((p:ℝ)/(p-1))≤ s.card+1 := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert p s hmax ih =>
    have hp := hs p (mem_insert_self p s)
    have hps : p∉s := fun h => (hmax p h).false
    have hsmall := ih (fun a ha => hs a (mem_insert_of_mem ha))
    have hsub : s⊆Ico 2 p := fun a ha => mem_Ico.mpr ⟨hs a (mem_insert_of_mem ha),hmax a ha⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Ico] at hcard
    have hle : s.card+2≤p := by omega
    have hreal : (s.card:ℝ)+2≤p := by exact_mod_cast hle
    have hdp : 0<(p:ℝ)-1 := by
      have hh : (2:ℝ)≤p := by exact_mod_cast hp
      linarith
    rw [prod_insert hps,card_insert_of_notMem hps,Nat.cast_add,Nat.cast_one]
    apply (mul_le_mul_of_nonneg_left hsmall (div_nonneg (Nat.cast_nonneg _) hdp.le)).trans
    rw [div_mul_eq_mul_div,div_le_iff₀ hdp]
    nlinarith

/-- Reciprocal totient density is bounded logarithmically, uniformly in the modulus. -/
theorem totient_ratio {n : ℕ} (hn : 0<n) : (n:ℝ)/n.totient≤2*(2+Real.log n) := by
  let s := n.primeFactors
  have hs (p : ℕ) (hp : p∈s) : 2≤p := (Nat.prime_of_mem_primeFactors hp).two_le
  have ht2 : 2^s.card ≤ n := by
    calc _ = ∏ _p∈s,2 := by simp
         _ ≤ ∏ p∈s,p := prod_le_prod (by intros; omega) hs
         _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) s.card)
    (by exact_mod_cast ht2 : (2:ℝ)^s.card≤(n:ℝ))
  rw [Real.log_pow] at hlog
  have hhalf : 1/2≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [ThetaTotientTail.totient_product hn]
  apply (ratio_product s hs).trans
  nlinarith only [hlog,mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg s.card)]


def logWeight (g : ℕ) : ℝ := (1+Real.log g)/g
def tailWeight (s : ℕ) : ℝ := ((s:ℝ)^(19/16:ℝ))⁻¹

theorem logWeight_nonneg (g : ℕ) : 0≤logWeight g := by
  rcases g with _|g
  · simp [logWeight]
  · unfold logWeight; apply div_nonneg _ (by positivity)
    have h := Real.log_nonneg (by exact_mod_cast Nat.succ_pos g : (1:ℝ)≤g+1)
    push_cast; linarith

theorem envelope {m d P : ℕ} [NeZero P] (hm : 1 < m) (hd : 1 < d) (hmP : m∣P) (hdP : d∣P) (K : ℕ) :
    |rowMean m d P K|/d ≤ 1080*logWeight (m.gcd d)*tailWeight (d/(m.gcd d)) := by
  let g := m.gcd d
  let s := d/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hs : 0<s := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hg
  have hds : g*s=d := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hreal : (d:ℝ)=(g:ℝ)*s := by exact_mod_cast hds.symm
  have ht : 0<(s.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hs
  have hsb : 1 ≤ (s:ℝ)^(1/16:ℝ) := Real.one_le_rpow (by exact_mod_cast hs) (by norm_num)
  have hl := Real.log_natCast_le_rpow_div s (show (0:ℝ)<1/16 by norm_num)
  have hh : (s:ℝ)/s.totient ≤ 36*(s:ℝ)^(1/16:ℝ) := (totient_ratio hs).trans (by linarith)
  have ham := ThetaReciprocalBlocks.harmonic_divisors hg hs
  rw [hds] at ham
  have he : (s:ℝ)^(1/16:ℝ)*(s:ℝ)^(19/16:ℝ)=(s:ℝ)^(5/4:ℝ) := by rw [←Real.rpow_add (by positivity)]; norm_num
  calc _ ≤ (3*(harmonic d:ℝ)*s.divisors.card/s.totient)/d :=
             div_le_div_of_nonneg_right (bound hm hd hmP hdP K) (Nat.cast_nonneg _)
       _ = (3/(g:ℝ))*(((harmonic d:ℝ)*s.divisors.card/(s:ℝ)^2)*((s:ℝ)/s.totient)) := by
             rw [hreal]; field_simp
       _ ≤ (3/(g:ℝ))*((10*(1+Real.log g)*((s:ℝ)^(5/4:ℝ))⁻¹)*(36*(s:ℝ)^(1/16:ℝ))) := by
             gcongr
       _ = _ := by
             change _ = 1080*((1+Real.log g)/g)*((s:ℝ)^(19/16:ℝ))⁻¹
             rw [←he]; field_simp
             <;> ring

/-- The finite tail is bounded uniformly in its upper cutoff. -/
theorem tail {Q : ℕ} (hQ : 0<Q) (s : Finset ℕ) (hs : ∀ n∈s,Q≤n) :
    ∑ n∈s,tailWeight n ≤ (∑' j : ℕ,((j:ℝ)^(9/8:ℝ))⁻¹)/(Q:ℝ)^(1/16:ℝ) := by
  have h (n : ℕ) (hn : n∈s) : tailWeight n ≤ ((n:ℝ)^(9/8:ℝ))⁻¹/(Q:ℝ)^(1/16:ℝ) := by
    have hp : 0<(n:ℝ) := by exact_mod_cast hQ.trans_le (hs n hn)
    have he : (n:ℝ)^(19/16:ℝ)=(n:ℝ)^(9/8:ℝ)*(n:ℝ)^(1/16:ℝ) := by rw [←Real.rpow_add hp]; norm_num
    unfold tailWeight
    rw [he,mul_inv,←div_eq_mul_inv]
    gcongr
    exact_mod_cast hs n hn
  apply (sum_le_sum h).trans
  rw [←sum_div]
  exact div_le_div_of_nonneg_right ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<9/8)).sum_le_tsum _ (by intros; positivity)) (by positivity)
#print axioms envelope
#print axioms tail
end
end Arxiv.«2501.03234».ThetaSmoothRows
