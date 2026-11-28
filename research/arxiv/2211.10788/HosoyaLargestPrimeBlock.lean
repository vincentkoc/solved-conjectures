import HosoyaSmoothHarmonicBound
import HosoyaDivisibilityDensities

/-! Bound the total reciprocal joint periods of integers with a prescribed
largest prime factor, following the divisor-fiber method of Sanna and Tron. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset

noncomputable def rankLcm (n : ℕ) := n.lcm (returnRank n)
noncomputable def lcmWeight (n : ℕ) : ℝ := (rankLcm n:ℝ)⁻¹

lemma rank_divides_iff {n : ℕ} (hn : 0 < n) (k : ℕ) : returnRank n∣k ↔ n∣Nat.fib k := by
  let : NeZero n := ⟨hn.ne'⟩
  simpa [returnRank,hn.ne'] using fibonacciStepRank_dvd_iff n 1 k

lemma rank_mono_dvd {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a ∣ b) :
    returnRank a ∣ returnRank b :=
  (rank_divides_iff ha _).mpr (h.trans ((rank_divides_iff hb _).mp dvd_rfl))

lemma rankLcm_mono_dvd {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a ∣ b) : rankLcm a ∣ rankLcm b :=
  Nat.lcm_dvd (h.trans (Nat.dvd_lcm_left ..)) ((rank_mono_dvd ha hb h).trans (Nat.dvd_lcm_right ..))

private lemma smooth_fiber_bound {p r g : ℕ} (pr : p.Coprime r) (rp : 0 < r) (S : Finset ℕ)
    (hs : ∀ n∈S, p∣n ∧ n.gcd r=g ∧ n∈(p+1).smoothNumbers) :
    ∑ n ∈ S, (n.lcm r:ℝ)⁻¹ ≤ ((p:ℝ)*r)⁻¹*smoothEuler p := by
  let v (n : ℕ) := n/(p*g)
  have data {n : ℕ} (hn : n∈S) : p*g∣n ∧ p*g*v n=n ∧ n.lcm r=p*r*v n := by
    obtain ⟨pn,eq,_⟩ := hs n hn
    have gr : g∣r := eq ▸ Nat.gcd_dvd_right n r
    have gn : g∣n := eq ▸ Nat.gcd_dvd_left n r
    have d := (Nat.Coprime.of_dvd_right gr pr).mul_dvd_of_dvd_of_dvd pn gn
    have en : p*g*v n=n := Nat.mul_div_cancel' d
    refine ⟨d,en,?_⟩
    have gp : 0 < g := eq ▸ Nat.gcd_pos_of_pos_right n rp
    apply Nat.eq_of_mul_eq_mul_left gp
    calc g*(n.lcm r) = n*r := eq ▸ Nat.gcd_mul_lcm n r
         _ = (p*g*v n)*r := congrArg (·*r) en.symm
         _ = g*(p*r*v n) := by ring
  let V := S.image v
  have inj : Set.InjOn v S := by
    intro a ha b hb id
    calc a = p*g*v a := (data ha).2.1.symm
         _ = p*g*v b := by rw [id]
         _ = _ := (data hb).2.1
  have sub : ∀ k∈V, k∈(p+1).smoothNumbers := by
    intro k hk
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    exact Nat.mem_smoothNumbers_of_dvd (hs n hn).2.2 (Nat.div_dvd_of_dvd (data hn).1)
  calc _ = ∑ n ∈ S, ((p:ℝ)*r)⁻¹*((v n:ℕ):ℝ)⁻¹ := by
            apply sum_congr rfl
            intro n hn
            rw [(data hn).2.2]
            push_cast
            simp [mul_inv_rev,mul_comm]
       _ = ((p:ℝ)*r)⁻¹*(∑ k ∈ V, (k:ℝ)⁻¹) := by rw [←mul_sum,show V=S.image v from rfl,sum_image inj]
       _ ≤ _ := mul_le_mul_of_nonneg_left (smooth_harmonic_bound p V sub) (by positivity)

/-- Each gcd with the return rank gives a separate smooth cofactor sum. -/
theorem largest_prime_block {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) (S : Finset ℕ)
    (hs : ∀ n∈S, p∣n ∧ n∈(p+1).smoothNumbers) :
    ∑ n ∈ S, lcmWeight n ≤ ((returnRank p).divisors.card:ℝ)*rankWeight p*smoothEuler p := by
  let r := returnRank p
  have rp : 0 < r := (returnRank_spec hp).1
  let : Fact p.Prime := ⟨hp⟩
  have pr : p.Coprime r := hp.coprime_iff_not_dvd.mpr (by
    simpa [r,returnRank,hp.ne_zero] using (rank_tame (p:=p) h5))
  have le : ∑ n ∈ S, lcmWeight n ≤ ∑ n ∈ S, (n.lcm r:ℝ)⁻¹ := by
    apply sum_le_sum
    intro n hn
    obtain ⟨pn,sm⟩ := hs n hn
    have np := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers sm)
    have lp : 0 < rankLcm n := Nat.lcm_pos np (rank_pos_all np)
    have dvd : n.lcm r ∣ rankLcm n := Nat.lcm_dvd (Nat.dvd_lcm_left ..)
      ((rank_mono_dvd hp.pos np pn).trans (Nat.dvd_lcm_right ..))
    apply inv_anti₀ (by exact_mod_cast Nat.lcm_pos np rp)
    exact_mod_cast Nat.le_of_dvd lp dvd
  apply le.trans
  rw [←sum_fiberwise_of_maps_to (s:=S) (t:=r.divisors) (g:=fun n => n.gcd r)
    (fun n _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n r,rp.ne'⟩) (fun n => (n.lcm r:ℝ)⁻¹)]
  calc _ ≤ ∑ _g ∈ r.divisors, ((p:ℝ)*r)⁻¹*smoothEuler p := by
            apply sum_le_sum
            intro g _
            apply smooth_fiber_bound pr rp
            intro n hn
            obtain ⟨mem,eq⟩ := mem_filter.mp hn
            exact ⟨(hs n mem).1,eq,(hs n mem).2⟩
       _ = _ := by simp [nsmul_eq_mul,r,rankWeight,one_div,mul_assoc]

#print axioms rankLcm_mono_dvd
#print axioms largest_prime_block

end Arxiv.«2211.10788».IndexDivisors
