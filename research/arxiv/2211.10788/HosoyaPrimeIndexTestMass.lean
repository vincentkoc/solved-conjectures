import LucasFibonacciPrimeIndexClosure
import CunninghamPrimeDirichletMass

/-! How small the mass of prime-index modular hits can be, including
at candidates that pass every individual test. -/

namespace Arxiv.«2211.10788».AlmostPrimeClosure
open CongruenceClosure ProgressionClosure Finset Filter Topology CunninghamChain.PrimeMass
open scoped ArithmeticFunction.Omega

def primeIndexHits (r d M : ℕ) (y : ℤ) : Set ℕ := {n | n.Prime ∧ Hit d r M y n}

private lemma unit_of_one_factor_budget {w : ℤ} (nz : w≠0) (small : Ω w.natAbs<1) : w=1 ∨ w= -1 := by
  have eq := ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp (show Ω w.natAbs=0 by omega)
  omega

/-- A single test can confine successful prime parameters to arbitrarily
little normalized prime mass. The test may omit any prescribed finite
collection of prime divisors of its modulus. -/
theorem arbitrarily_small_hit_mass {r d E : ℕ} (hd : 0<d) (he : 0<E) (y : ℤ) {ε : ℝ} (ep : 0<ε) :
    ∃ M : ℕ, 0<M ∧ M.Coprime E ∧ ∀ᶠ s : ℝ in 𝓝[>] 1, (s-1)*mass (primeIndexHits r d M y) s<ε := by
  classical
  obtain ⟨K : ℕ,hK⟩ := exists_nat_gt (4/ε+2)
  obtain ⟨q,hq,prime⟩ := Nat.exists_infinite_primes (K+2)
  let : NeZero q := ⟨prime.ne_zero⟩
  obtain ⟨M,mp,unit,cover⟩ := confining_modulus (k:=1) (r:=r) hd he prime.pos y
  let P := primeIndexHits r d M y
  let A := {n : ℕ | (n:ZMod q)=1}
  let B := {n : ℕ | (n:ZMod q)= -1}
  let S := Set.Iic (y.natAbs+r+2)
  have aLimit := mass_progression (1:ZMod q) isUnit_one
  have bLimit := mass_progression (-1:ZMod q) isUnit_one.neg
  have sLimit := finite_mass_tendsto (Set.finite_Iic (y.natAbs+r+2))
  have tot : (q.totient:ℝ)=(q:ℝ)-1 := by rw [Nat.totient_prime prime,Nat.cast_sub prime.one_le]; norm_num
  have den : 0<(q:ℝ)-1 := sub_pos.mpr (by exact_mod_cast prime.one_lt)
  have ratio : (q.totient:ℝ)⁻¹+(q.totient:ℝ)⁻¹+0 < ε := by
    rw [tot,←one_div,←add_div,add_zero,div_lt_iff₀ den]
    have qK : (K:ℝ)+2≤q := by exact_mod_cast hq
    have sm := (div_lt_iff₀ ep).mp (show 4/ε<(q:ℝ)-1 by linarith)
    linarith
  have top := ((aLimit.add bLimit).add sLimit).eventually_lt_const ratio
  refine ⟨M,mp,unit,?_⟩
  filter_upwards [top,self_mem_nhdsWithin] with s bounded hs
  change 1<s at hs
  have cmp := mass_le_cover {()} (fun _ => A) P B S (by
    intro n hit pr
    by_cases big : y.natAbs+r+2<n
    · obtain ⟨w,cl,nz,small,_⟩ := cover n big pr.isAlmostPrime_one hit.2
      rcases unit_of_one_factor_budget nz small with rfl|rfl
      · exact Or.inl ⟨(),mem_singleton_self _,by simpa [A] using (ZMod.intCast_eq_intCast_iff ..).mpr cl⟩
      · exact Or.inr (Or.inl (by simpa [B] using (ZMod.intCast_eq_intCast_iff ..).mpr cl))
    · exact Or.inr (Or.inr (show n≤y.natAbs+r+2 by omega))) hs
  simp only [sum_singleton] at cmp
  have bound := mul_le_mul_of_nonneg_left cmp (sub_nonneg.mpr hs.le)
  change (s-1)*mass A s+(s-1)*mass B s+(s-1)*mass S s<ε at bounded
  exact lt_of_le_of_lt (by simpa only [mul_add] using bound) bounded

/-- At the two limiting parameters, every individual modular test
still contains an entire reduced prime progression. -/
theorem positive_hit_mass_at_unit {r d M : ℕ} (hm : 0<M) (w : ℤ) (unit : w=1 ∨ w= -1) :
    ∃ η : ℝ, 0<η ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      η≤(s-1)*mass (primeIndexHits r d M (signed (r+d*w))) s := by
  classical
  let : NeZero M := ⟨hm.ne'⟩
  obtain ⟨T,tp,period⟩ := signed_forward_period M ((r:ℤ)+d*w)
  let : NeZero T := ⟨tp.ne'⟩
  let A := {n : ℕ | (n:ZMod T)=(w:ZMod T)}
  let P := primeIndexHits r d M (signed (r+d*w))
  have un : IsUnit (w:ZMod T) := by rcases unit with rfl|rfl <;> simp
  have lim := mass_progression (w:ZMod T) un
  have tot : 0<(T.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr tp
  have pos := inv_pos.mpr tot
  refine ⟨(T.totient:ℝ)⁻¹/2,half_pos pos,?_⟩
  filter_upwards [lim.eventually_const_lt (half_lt_self pos),self_mem_nhdsWithin] with s lower hs
  change 1<s at hs
  have inc (n : ℕ) (member : n∈A) (pr : n.Prime) : n∈P := by
    have cl : (n:ℤ) ≡ w [ZMOD T] := (ZMod.intCast_eq_intCast_iff ..).mp (by simpa [A] using member)
    have big : w≤n := by rcases unit with rfl|rfl <;> have := pr.two_le <;> omega
    have v := period ((r:ℤ)+d*n) (by gcongr) ((cl.mul_left (d:ℤ)).add_left (r:ℤ))
    rw [show (r:ℤ)+d*n=((r+d*n:ℕ):ℤ) by push_cast; rfl,signed_nat] at v
    exact ⟨pr,(ZMod.intCast_eq_intCast_iff ..).mp (by simpa using v)⟩
  have count : mass A s ≤ mass P s := by
    apply (summable_weight A hs).tsum_le_tsum _ (summable_weight P hs)
    intro n
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    by_cases h : n.Prime ∧ n∈A
    · rw [weight,if_pos h,weight,if_pos ⟨h.1,inc n h.2 h.1⟩]
    · simpa only [weight,if_neg h] using weight_nonneg P n
  exact lower.le.trans (mul_le_mul_of_nonneg_left count (sub_nonneg.mpr hs.le))

#print axioms positive_hit_mass_at_unit

#print axioms arbitrarily_small_hit_mass

end Arxiv.«2211.10788».AlmostPrimeClosure
