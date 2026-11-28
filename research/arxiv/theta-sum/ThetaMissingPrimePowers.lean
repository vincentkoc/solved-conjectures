import ThetaTotientTail
import Mathlib.NumberTheory.Chebyshev

/-! Missing prime powers in the least common multiple of the first Y integers. -/
namespace Arxiv.«2501.03234».ThetaMissingPrimePowers
open Finset Filter
noncomputable section

private def w (q : ℕ) : ℝ := 1/((q:ℝ)*q.totient)
private lemma w_mul {d k : ℕ} (hd : 0<d) (hk : 0<k) : w (d*k)≤w d*w k := by
  have hf : (d.totient:ℝ)*k.totient≤(d*k).totient := by exact_mod_cast Nat.totient_super_multiplicative d k
  have h₁ : 0<(d:ℝ)*d.totient := mul_pos (Nat.cast_pos.mpr hd) (Nat.cast_pos.mpr (Nat.totient_pos.mpr hd))
  have h₂ : 0<(k:ℝ)*k.totient := mul_pos (Nat.cast_pos.mpr hk) (Nat.cast_pos.mpr (Nat.totient_pos.mpr hk))
  unfold w; rw [one_div_mul_one_div,Nat.cast_mul]
  apply one_div_le_one_div_of_le (mul_pos h₁ h₂)
  nlinarith only [mul_le_mul_of_nonneg_left hf (show 0≤(d:ℝ)*k by positivity)]

private lemma multiple_mass {d : ℕ} (hd : 0<d) (s : Finset ℕ) (hs : ∀ q∈s,0<q ∧ d∣q) :
    ∑ q∈s,w q≤6*w d := by
  let t := s.image (·/d)
  have ht (k) (hk : k∈t) : 1≤k := by
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hk
    exact Nat.div_pos (Nat.le_of_dvd (hs q hq).1 (hs q hq).2) hd
  have hinj : Set.InjOn (·/d) ↑s := by
    intro x hx y hy he
    change x/d=y/d at he
    rw [←Nat.div_mul_cancel (hs x hx).2,←Nat.div_mul_cancel (hs y hy).2,he]
  calc
    _ ≤ ∑ q∈s,w d*w (q/d) := by
      apply sum_le_sum; intro q hq
      have he : d*(q/d)=q := Nat.mul_div_cancel' (hs q hq).2
      conv_lhs => rw [←he]
      exact w_mul hd (ht _ (mem_image_of_mem _ hq))
    _ = w d*∑ k∈t,w k := by rw [mul_sum,sum_image hinj]
    _ ≤ _ := by
      have H : ∑ k∈t,w k ≤ 6 := by simpa [w] using ThetaTotientTail.bound 1 (by decide) t ht
      exact (mul_le_mul_of_nonneg_left H (show 0≤w d by unfold w; positivity)).trans_eq (mul_comm ..)

def firstMissingPower (Y p : ℕ) := p^(p.log Y+1)
theorem missing_large {Y p : ℕ} (hp : p.Prime) : Y<firstMissingPower Y p :=
  Nat.lt_pow_succ_log_self hp.one_lt _
theorem missing_prime_le {Y p : ℕ} : p≤firstMissingPower Y p :=
  Nat.le_self_pow (by omega : p.log Y+1≠0) p
private lemma missing_weight {Y p : ℕ} (hp : p.Prime) : w (firstMissingPower Y p)≤2/(firstMissingPower Y p:ℝ)^2 := by
  have hd : 0<firstMissingPower Y p := pow_pos hp.pos _
  have hφ : 0<(firstMissingPower Y p).totient := Nat.totient_pos.mpr hd
  have hhalf : firstMissingPower Y p≤2*(firstMissingPower Y p).totient := by
    unfold firstMissingPower
    rw [Nat.totient_prime_pow_succ hp,pow_succ]
    have hh : p≤2*(p-1) := by have := hp.two_le; omega
    nlinarith only [Nat.mul_le_mul_left (p^p.log Y) hh]
  unfold w; rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have he : (firstMissingPower Y p:ℝ)≤2*(firstMissingPower Y p).totient := by exact_mod_cast hhalf
  nlinarith only [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (firstMissingPower Y p))]

private lemma witness {Y q : ℕ} (hq : 0<q) (h : ¬q∣Nat.lcmUpto Y) :
    ∃ p∈q.primeFactors,firstMissingPower Y p∣q := by
  by_contra! hh
  apply h
  rw [←Nat.factorization_prime_le_iff_dvd hq.ne' (Nat.lcmUpto_ne_zero _)]
  intro p hp
  rw [Nat.factorization_lcmUpto Y hp]
  by_contra! he
  have hdiv : firstMissingPower Y p∣q := (hp.pow_dvd_iff_le_factorization hq.ne').mpr he
  have hpq : p∣q := (dvd_pow_self p (by omega : p.log Y+1≠0)).trans hdiv
  exact hh p (Nat.mem_primeFactors.mpr ⟨hp,hpq,hq.ne'⟩) hdiv

/-- Every firstMissingPower conductor is charged to a first omitted power of a prime.
The sum is finite even when the set of conductors is arbitrary. -/
theorem missing_mass (Y : ℕ) (s : Finset ℕ)
    (hs : ∀ q∈s,0<q ∧ ¬q∣Nat.lcmUpto Y) :
    ∑ q∈s,1/((q:ℝ)*q.totient)≤12*∑ p∈s.biUnion Nat.primeFactors,1/(firstMissingPower Y p:ℝ)^2 := by
  classical
  let P := s.biUnion Nat.primeFactors
  have hp {p : ℕ} (h : p∈P) : p.Prime := by
    obtain ⟨_,_,hd⟩ := mem_biUnion.mp h; exact Nat.prime_of_mem_primeFactors hd
  let f (p q : ℕ) := if firstMissingPower Y p∣q then w q else 0
  have hrow (q) (hq : q∈s) : w q≤∑ p∈P,f p q := by
    obtain ⟨p,hpq,hdiv⟩ := witness (hs q hq).1 (hs q hq).2
    have h := single_le_sum (f:=fun p => f p q) (fun r _ => by dsimp [f,w]; split_ifs <;> positivity)
      (mem_biUnion.mpr ⟨q,hq,hpq⟩ : p∈P)
    simpa [f,hdiv] using h
  calc
    _ ≤ ∑ q∈s,∑ p∈P,f p q := sum_le_sum hrow
    _ = ∑ p∈P,∑ q∈s,f p q := sum_comm
    _ ≤ ∑ p∈P,12*(1/(firstMissingPower Y p:ℝ)^2) := by
      apply sum_le_sum; intro p hp'
      let t := s.filter (fun q => firstMissingPower Y p∣q)
      have H := multiple_mass (d:=firstMissingPower Y p) (pow_pos (hp hp').pos _) t
        (fun q hq => ⟨(hs q (mem_filter.mp hq).1).1,(mem_filter.mp hq).2⟩)
      change (∑ q∈s,if firstMissingPower Y p∣q then w q else 0)≤_
      rw [←sum_filter]; exact H.trans ((mul_le_mul_of_nonneg_left (missing_weight (Y:=Y) (hp hp')) (by norm_num : (0:ℝ)≤6)).trans_eq (by ring))
    _ = _ := (mul_sum ..).symm

end
end Arxiv.«2501.03234».ThetaMissingPrimePowers
#print axioms Arxiv.«2501.03234».ThetaMissingPrimePowers.missing_mass
