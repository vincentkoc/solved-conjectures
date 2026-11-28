import Erdos722SixDirections
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Choosing group sizes for a truncated transversal design

For fixed width, a bounded CRT adjustment of the quotient gives a full
group size coprime to the width factorial. Small primes dividing the last
group occur to high multiplicity.
-/

namespace Erdos722.PairDesign
open Erdos722.Quartet

private def primesTo (s : ℕ) := (Finset.range (s+1)).filter Nat.Prime

private theorem in_primesTo {s p : ℕ} : p ∈ primesTo s ↔ p.Prime ∧ p ≤ s := by
  simp only [primesTo,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  exact and_comm

private def period (s k : ℕ) := ∏ p ∈ primesTo s, p^k

private theorem period_pos (s k : ℕ) : 0 < period s k :=
  Finset.prod_pos fun _ hp => pow_pos (in_primesTo.mp hp).1.pos _

private theorem offset {s k v : ℕ} (hk : 0 < k) (a : ℕ) :
    ∃ t, a < t ∧ t ≤ a+2*period s k ∧
      ∀ p, p.Prime → p ≤ s → ¬p ∣ t ∧ (¬p ∣ v → p^k ∣ t+v) := by
  classical
  let M := period s k
  have hM : 0 < M := period_pos s k
  let b (p : ℕ) := if p ∣ v then 1 else (v+1)*p^k-v
  have hn : ∀ p ∈ primesTo s, p^k ≠ 0 :=
    fun p hp => pow_ne_zero _ (in_primesTo.mp hp).1.ne_zero
  have hc : Set.Pairwise (primesTo s : Set ℕ) (Function.onFun Nat.Coprime (·^k)) :=
    fun _ hp _ hq h => Nat.coprime_pow_primes _ _ (in_primesTo.mp hp).1 (in_primesTo.mp hq).1 h
  let z := Nat.chineseRemainderOfFinset b (·^k) (primesTo s) hn hc
  have hz : z.val < M := Nat.chineseRemainderOfFinset_lt_prod b _ hn hc
  let t := (a/M+1)*M + z.val
  have ha := Nat.mod_add_div a M
  have hr := Nat.mod_lt a hM
  refine ⟨t,?_,?_,?_⟩
  · dsimp [t]; rw [Nat.add_mul,one_mul,Nat.mul_comm (a/M) M]; omega
  · change (a/M+1)*M+z.val ≤ a+2*M
    rw [Nat.add_mul,one_mul,Nat.mul_comm (a/M) M]; omega
  intro p hp hps
  have hm : p^k ∣ M := Finset.dvd_prod_of_mem _ (in_primesTo.mpr ⟨hp,hps⟩)
  have hpow : p ∣ p^k := dvd_pow_self p hk.ne'
  have ht : t ≡ b p [MOD p^k] := by
    have hzero := (hm.trans (dvd_mul_left M (a/M+1))).modEq_zero_nat
    simpa [t] using hzero.add (z.property p (in_primesTo.mpr ⟨hp,hps⟩))
  by_cases hd : p ∣ v
  · rw [show b p=1 by simp [b,hd]] at ht
    exact ⟨fun h => hp.not_dvd_one ((ht.dvd_iff hpow).mp h),fun h => (h hd).elim⟩
  · have hv : v ≤ (v+1)*p^k := by
      have := Nat.mul_le_mul_left (v+1) (show 1 ≤ p^k from pow_pos hp.pos _)
      omega
    have hb : b p+v=(v+1)*p^k := by simp [b,hd,Nat.sub_add_cancel hv]
    have htv : p^k ∣ t+v := by
      have he := ht.add_right v
      rw [hb] at he
      exact (he.dvd_iff (dvd_refl _)).mpr (dvd_mul_left _ _)
    exact ⟨fun h => hd ((Nat.dvd_add_right h).mp (hpow.trans htv)),fun _ => htv⟩

private theorem sized {s k v : ℕ} (hk : 0 < k) (hs : k ≤ s)
    (hd : k.factorial^k ∣ s+1)
    (hv : (s+1)*(2*s*period s k+2) ≤ v) :
    ∃ t r, v=s*t+r ∧ 0<r ∧ r≤t ∧ s.factorial.Coprime t ∧
      ∀ p, p.Prime → p ≤ k → p ∣ r → p^k ∣ r := by
  let a := v/(s+1)
  let e := v%(s+1)
  have ha : 2*s*period s k+2 ≤ a := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [Nat.mul_comm] using hv)
  have he : e ≤ s := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  have hv' : e+(s+1)*a=v := Nat.mod_add_div _ _
  obtain ⟨t,ht,ht',hpr⟩ := offset (v:=v) hk a (s:=s)
  obtain ⟨d,hd'⟩ := Nat.exists_eq_add_of_le ht.le
  have hdl : 1 ≤ d := by omega
  have hdu : d ≤ 2*period s k := by omega
  have hsd := Nat.mul_le_mul_left s hdu
  have hsd' := Nat.mul_le_mul_left s hdl
  have hlt : s*t < v := by rw [hd']; nlinarith only [ha,hv',hsd,Nat.zero_le e]
  let r := v-s*t
  have hr : s*t+r=v := by dsimp [r]; omega
  have hrt : r≤t := by rw [hd'] at hr ⊢; nlinarith only [hr,hv',he,hsd',Nat.zero_le d]
  refine ⟨t,r,hr.symm,by dsimp [r]; omega,hrt,?_,?_⟩
  · by_contra h
    obtain ⟨p,hp,hpf,hpt⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    exact (hpr p hp (hp.dvd_factorial.mp hpf)).1 hpt
  · intro p hp hpk hpr'
    have hpow : p ∣ p^k := dvd_pow_self p hk.ne'
    have hps : p^k ∣ s+1 := (pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hpk) k).trans hd
    have hst : p^k ∣ (s+1)*t := dvd_mul_of_dvd_left hps _
    have hsum : (s+1)*t+r=t+v := by nlinarith only [hr]
    obtain ⟨hpt,hpv⟩ := hpr p hp (le_trans hpk hs)
    have hn : ¬p ∣ v := by
      intro h
      have h' := Nat.dvd_add (hpow.trans hst) hpr'
      rw [hsum,Nat.add_comm] at h'
      exact hpt ((Nat.dvd_add_right h).mp h')
    have h' := hpv hn
    rw [← hsum] at h'
    exact (Nat.dvd_add_right hst).mp h'

/-- Every sufficiently large order splits into full and truncated groups,
each admitting the required unit-difference coordinates. -/
theorem array_group_sizes {k s : ℕ} (hk : 0 < k) (hs : k ≤ s)
    (hd : k.factorial^k ∣ s+1) :
    ∃ N, ∀ v ≥ N, ∃ t r, v=s*t+r ∧ r ≤ t ∧
      Nonempty (Directions s t) ∧ Nonempty (Directions k r) := by
  refine ⟨(s+1)*(2*s*period s k+2),fun v hv => ?_⟩
  obtain ⟨t,r,he,hr,hrt,hc,hpr⟩ := sized hk hs hd hv
  refine ⟨t,r,he,hrt,⟨Six.modular (by omega) hc⟩,Six.factorized hr ?_⟩
  intro p hm
  have hp := Nat.prime_of_mem_primeFactors hm
  have hn : r.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hm
  by_cases h : p ≤ k
  · have hf := (hp.pow_dvd_iff_le_factorization hr.ne').mp (hpr p hp h (Nat.dvd_of_mem_primeFactors hm))
    exact (Nat.lt_two_pow_self (n:=k)).le.trans ((Nat.pow_le_pow_left hp.two_le k).trans
      (Nat.pow_le_pow_right hp.pos hf))
  · exact (by omega : k ≤ p).trans (by
      simpa using (Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ r.factorization p)))

#print axioms array_group_sizes
end Erdos722.PairDesign
