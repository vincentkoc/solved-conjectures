import Mathlib
import FormalConjectures.Wikipedia.ElliottHalberstamConjecture
import CunninghamSingularSeriesGrowth

/-! Distribution of prime seeds in the residue classes of the Cunningham sieve. -/

namespace CunninghamChain.PrimeSeedSieve

open Finset Filter Real ElliottHalberstamConjecture

/-- The level-of-distribution input from the pinned Bombieri–Vinogradov variant. -/
def BombieriVinogradov : Prop :=
  ∀ θ : ℝ, θ < 1 / 2 → ∀ A : ℝ, 0 < A →
    ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

private lemma ap_count_le (x q : ℕ) (a : ZMod q) :
    x.primeCountingMod q a ≤ x/q+1 := by
  classical
  unfold Nat.primeCountingMod
  rw [← card_range (x/q+1)]
  apply card_le_card_of_injOn (fun n : ℕ => n/q)
  · intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right
      (Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hn).1))))
  · intro m hm n hn he
    have hc := (mem_filter.mp hm).2.2.trans (mem_filter.mp hn).2.2.symm
    have hr := (ZMod.natCast_eq_natCast_iff m n q).mp hc
    change m % q = n % q at hr
    change m/q = n/q at he
    calc
      m = m%q + q*(m/q) := (Nat.mod_add_div m q).symm
      _ = n := by rw [hr, he, Nat.mod_add_div]

lemma E_nonneg (x q : ℕ) (hq : 0 < q) : 0 ≤ E x q := by
  let : NeZero q := ⟨hq.ne'⟩
  unfold E
  exact (abs_nonneg _).trans (le_ciSup_of_le (Finite.bddAbove_range _) (1 : (ZMod q)ˣ) le_rfl)

private lemma E_trivial {x q : ℕ} (hq : 0 < q) (hx : q ≤ x) :
    E x q ≤ 2*(x:ℝ)/q.totient := by
  let : NeZero q := ⟨hq.ne'⟩
  have hp : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hn : (0:ℝ) < q := by exact_mod_cast hq
  have hφ : (q.totient:ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hπ : x.primeCounting ≤ x+1 := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact (card_le_card (show x.primesLE ⊆ range (x+1) from
      fun _ h => mem_range.mpr (Nat.lt_succ_of_le (Nat.mem_primesLE.mp h).1))).trans_eq (card_range _)
  unfold E
  refine ciSup_le fun a => abs_le.mpr ⟨?_, ?_⟩
  · have hπ' : (x.primeCounting:ℝ) ≤ 2*x := by
      have := (show (x.primeCounting:ℝ) ≤ (x:ℝ)+1 by exact_mod_cast hπ)
      have : (1:ℝ) ≤ x := by exact_mod_cast hq.trans_le hx
      linarith
    linarith [div_le_div_of_nonneg_right hπ' hp.le,
      Nat.cast_nonneg (α := ℝ) (x.primeCountingMod q a)]
  · have hc : (x.primeCountingMod q a:ℝ) ≤ (x/q:ℕ)+1 := by exact_mod_cast ap_count_le x q a
    have hd : ((x/q:ℕ):ℝ)*q ≤ x := by exact_mod_cast Nat.div_mul_le_self x q
    have hqx : (q:ℝ) ≤ x := by exact_mod_cast hx
    have hu : ((x/q:ℕ):ℝ)+1 ≤ 2*(x:ℝ)/q := (le_div_iff₀ hn).mpr (by nlinarith)
    have := (hc.trans hu).trans (div_le_div_of_nonneg_left (by positivity) hp hφ)
    linarith [div_nonneg (Nat.cast_nonneg (α := ℝ) x.primeCounting) hp.le]

private lemma totient_prod_primes (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) :
    (∏ q ∈ T, q).totient = ∏ q ∈ T, q.totient := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | @insert p T hnot ih =>
    have hp := hT p (mem_insert_self _ _)
    have hs (q : ℕ) (hq : q ∈ T) := hT q (mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ T, q) := Nat.coprime_prod_right_iff.mpr fun q hq =>
      (Nat.coprime_primes hp (hs q hq)).mpr (fun h => hnot (h ▸ hq))
    rw [prod_insert hnot, prod_insert hnot, Nat.totient_mul hc, ih hs]

private lemma euler_moment (x k : ℕ) (S : Finset (Finset ℕ))
    (hS : S ⊆ x.primesLE.powerset) :
    (∑ T ∈ S, ((k:ℝ)^T.card)^2 / (∏ q ∈ T, q).totient) ≤
      (∏ q ∈ x.primesLE, (1-1/(q:ℝ))⁻¹)^(k^2) := by
  classical
  let f (q : ℕ) := (k:ℝ)^2 / q.totient
  have he (T : Finset ℕ) (hT : T ∈ S) :
      ((k:ℝ)^T.card)^2 / (∏ q ∈ T, q).totient = ∏ q ∈ T, f q := by
    have hp (q : ℕ) (hq : q ∈ T) : q.Prime := Nat.prime_of_mem_primesLE ((mem_powerset.mp (hS hT)) hq)
    rw [totient_prod_primes T hp, Nat.cast_prod]
    simp only [f, prod_div_distrib, prod_const, ← pow_mul, Nat.mul_comm T.card 2]
  rw [sum_congr rfl he]
  calc
    _ ≤ ∑ T ∈ x.primesLE.powerset, ∏ q ∈ T, f q :=
      sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => prod_nonneg (fun _ _ => by dsimp [f]; positivity))
    _ = ∏ q ∈ x.primesLE, (1+f q) := (prod_one_add _).symm
    _ ≤ ∏ q ∈ x.primesLE, ((1-1/(q:ℝ))⁻¹)^(k^2) := by
      apply prod_le_prod (fun _ _ => by dsimp [f]; positivity)
      intro q hq
      have hp := Nat.prime_of_mem_primesLE hq
      have hq' : (1:ℝ) < q := by exact_mod_cast hp.one_lt
      have ht : (q.totient:ℝ) = (q:ℝ)-1 := by rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]; simp
      have hid : (1-1/(q:ℝ))⁻¹ = 1+1/((q:ℝ)-1) := by
        have h0 : (q:ℝ) ≠ 0 := by positivity
        have h1 : (q:ℝ)-1 ≠ 0 := by linarith
        rw [show (1-1/(q:ℝ)) = ((q:ℝ)-1)/q by field_simp]
        rw [inv_div, one_add_div h1]; ring_nf
      rw [hid]
      dsimp only [f]
      rw [ht]
      have hb := one_add_mul_le_pow (show -(2:ℝ) ≤ 1/((q:ℝ)-1) by linarith [one_div_pos.mpr (by linarith : 0 < (q:ℝ)-1)]) (k^2)
      simpa only [Nat.cast_pow, div_eq_mul_inv, one_mul] using hb
    _ = _ := by rw [prod_pow]

/-- Squared discrepancy for a family of squarefree moduli, with up to k forbidden
reduced classes per prime. Each product W·∏q is charged once to the unweighted sum. -/
theorem weighted_discrepancy_sq (x W D k : ℕ) (hW : 0 < W) (hD : D ≤ x)
    (S : Finset (Finset ℕ)) (hS : S ⊆ x.primesLE.powerset)
    (hlevel : ∀ T ∈ S, W*(∏ q ∈ T, q) ≤ D) :
    (∑ T ∈ S, (k:ℝ)^T.card * E x (W*(∏ q ∈ T, q)))^2 ≤
      (∑ q ∈ Icc 1 D, E x q) * (2*x*(∏ q ∈ x.primesLE, (1-1/(q:ℝ))⁻¹)^(k^2)) := by
  classical
  let m (T : Finset ℕ) := ∏ q ∈ T, q
  let d (T : Finset ℕ) := W * m T
  have hp {T : Finset ℕ} (hT : T ∈ S) {q} (hq : q ∈ T) : q.Prime :=
    Nat.prime_of_mem_primesLE ((mem_powerset.mp (hS hT)) hq)
  have hpos {T} (hT : T ∈ S) : 0 < d T := Nat.mul_pos hW (prod_pos fun _ hq => (hp hT hq).pos)
  have hE {T} (hT : T ∈ S) : 0 ≤ E x (d T) := E_nonneg _ _ (hpos hT)
  have hinj : Set.InjOn d (S : Set (Finset ℕ)) := by
    intro T hT U hU he
    have ht : (m T).primeFactors = T := Nat.primeFactors_prod fun _ hq => hp hT hq
    have hu : (m U).primeFactors = U := Nat.primeFactors_prod fun _ hq => hp hU hq
    exact ht.symm.trans ((congrArg Nat.primeFactors (Nat.eq_of_mul_eq_mul_left hW he)).trans hu)
  have hmass : (∑ T ∈ S, E x (d T)) ≤ ∑ q ∈ Icc 1 D, E x q := by
    rw [← sum_image hinj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨T, hT, rfl⟩ := mem_image.mp hq
      exact mem_Icc.mpr ⟨hpos hT, hlevel T hT⟩
    · exact fun q hq _ => E_nonneg _ _ (mem_Icc.mp hq).1
  have hsecond : (∑ T ∈ S, ((k:ℝ)^T.card)^2 * E x (d T)) ≤
      2*x*(∏ q ∈ x.primesLE, (1-1/(q:ℝ))⁻¹)^(k^2) := by
    calc
      _ ≤ ∑ T ∈ S, (2*x)*(((k:ℝ)^T.card)^2 / (m T).totient) := by
        apply sum_le_sum
        intro T hT
        have hφ := Nat.le_of_dvd (Nat.totient_pos.mpr (hpos hT))
          (Nat.totient_dvd_of_dvd (dvd_mul_left (m T) W))
        have hm : 0 < m T := prod_pos (fun _ hq => (hp hT hq).pos)
        have he := (E_trivial (hpos hT) ((hlevel _ hT).trans hD)).trans
          (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast Nat.totient_pos.mpr hm)
            (by exact_mod_cast hφ) : 2*(x:ℝ)/(d T).totient ≤ 2*x/(m T).totient)
        calc
          _ ≤ ((k:ℝ)^T.card)^2 * (2*x/(m T).totient) := mul_le_mul_of_nonneg_left he (sq_nonneg _)
          _ = _ := by ring
      _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (euler_moment x k S hS) (by positivity)
  change (∑ T ∈ S, (k:ℝ)^T.card * E x (d T)) ^ 2 ≤ _
  calc
    _ ≤ (∑ T ∈ S, E x (d T)) * (∑ T ∈ S, ((k:ℝ)^T.card)^2 * E x (d T)) :=
      sum_sq_le_sum_mul_sum_of_sq_le_mul S (fun _ hT => hE hT)
        (fun _ hT => mul_nonneg (sq_nonneg _) (hE hT)) (fun _ _ => by ring_nf; rfl)
    _ ≤ _ := mul_le_mul hmass hsecond (sum_nonneg fun _ hT => mul_nonneg (sq_nonneg _) (hE hT))
      (sum_nonneg fun _ hq => E_nonneg _ _ (mem_Icc.mp hq).1)

#print axioms weighted_discrepancy_sq

/-- Bombieri–Vinogradov absorbs all squarefree residue multiplicities at level x^(1/4),
with an arbitrary integral logarithmic saving, uniformly in the initial modulus W. -/
theorem weighted_bombieri_vinogradov (hBV : BombieriVinogradov) (k L : ℕ) (hL : 0 < L) :
    ∃ C > (0:ℝ), ∀ᶠ x : ℕ in atTop, ∀ W : ℕ, 0 < W →
      ∀ S : Finset (Finset ℕ), S ⊆ x.primesLE.powerset →
      (∀ T ∈ S, (W*(∏ q ∈ T, q))^4 ≤ x) →
      (∑ T ∈ S, (k:ℝ)^T.card * E x (W*(∏ q ∈ T, q))) ≤ C*x/(log x)^L := by
  let A := 2*L+k^2
  have hA : 0 < A := by dsimp [A]; omega
  obtain ⟨c, hc, hBV'⟩ := hBV (1/4) (by norm_num) A (by exact_mod_cast hA)
  let C := Real.sqrt (2*c*(2*exp 4)^(k^2))
  have hC : 0 < C := Real.sqrt_pos.mpr (by positivity)
  refine ⟨C,hC, ?_⟩
  filter_upwards [CunninghamChain.prime_euler_product_log_bounds, eventually_ge_atTop 3] with x he hx
  intro W hW S hS hlevel
  let D := ⌊(x:ℝ)^(1/4:ℝ)⌋₊
  have hx' : 1 < (x:ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hl := log_pos hx'
  have hD : D ≤ x := by
    apply Nat.floor_le_of_le
    simpa using (Real.rpow_le_rpow_of_exponent_le hx'.le (by norm_num : (1/4:ℝ) ≤ 1))
  have hlev (T : Finset ℕ) (hT : T ∈ S) : W*(∏ q ∈ T, q) ≤ D := by
    apply Nat.le_floor
    let m := W*(∏ q ∈ T, q)
    have hh : (m:ℝ)^4 ≤ x := by exact_mod_cast hlevel T hT
    have h := Real.rpow_le_rpow (by positivity) hh (by norm_num : (0:ℝ) ≤ 1/4)
    rwa [← Real.rpow_natCast_mul (by positivity : 0 ≤ (m:ℝ)) 4, show ((4:ℕ):ℝ)*(1/4)=1 by norm_num,
      Real.rpow_one] at h
  have h := weighted_discrepancy_sq x W D k hW hD S hS hlev
  have hd := hBV' x (by omega)
  rw [Real.rpow_natCast] at hd
  have hprod : 0 ≤ ∏ q ∈ x.primesLE, (1-1/(q:ℝ))⁻¹ := by
    apply prod_nonneg
    intro q hq
    have hq' : (1:ℝ) < q := by exact_mod_cast (Nat.prime_of_mem_primesLE hq).one_lt
    exact inv_nonneg.mpr (sub_nonneg.mpr ((one_div_le_one_div_of_le (by norm_num) hq'.le).trans_eq (by norm_num)))
  have hπ := pow_le_pow_left₀ hprod he.2 (k^2)
  have hright : (∑ q ∈ Icc 1 D, E x q) * (2*x*(∏ q ∈ x.primesLE, (1-1/(q:ℝ))⁻¹)^(k^2)) ≤
      (c*x/log x^A) * (2*x*((2*exp 4)*log x)^(k^2)) := by
    apply mul_le_mul hd (mul_le_mul_of_nonneg_left hπ (by positivity)) _ (by positivity)
    exact mul_nonneg (by positivity) (pow_nonneg hprod _)
  have heq : (c*x/log x^A) * (2*x*((2*exp 4)*log x)^(k^2)) = (C*x/log x^L)^2 := by
    have hc2 : C^2 = 2*c*(2*exp 4)^(k^2) := Real.sq_sqrt (by positivity)
    dsimp only [A]
    rw [pow_add, mul_comm 2 L, pow_mul, mul_pow ((2:ℝ)*exp 4) (log x), div_pow, mul_pow C (x:ℝ), hc2]
    field_simp
  rw [heq] at hright
  exact le_of_sq_le_sq (h.trans hright) (by positivity)

#print axioms weighted_bombieri_vinogradov

private lemma residue_sum_error (x M : ℕ) [NeZero M] (B : Finset (ZMod M))
    (hB : ∀ a ∈ B, IsUnit a) :
    |(((x.primesLE.filter fun n : ℕ => (n : ZMod M) ∈ B).card : ℝ)) -
      (B.card:ℝ)*((x.primeCounting:ℝ)/M.totient)| ≤ B.card*E x M := by
  classical
  have hc (a : ZMod M) : (x.primesLE.filter fun n : ℕ => (n : ZMod M) = a).card =
      x.primeCountingMod M a := by
    unfold Nat.primeCountingMod
    congr 1
    ext n
    simp only [mem_filter, Nat.mem_primesLE, mem_range, Nat.lt_succ_iff, and_assoc]
  rw [← sum_card_fiberwise_eq_card_filter x.primesLE B (fun n : ℕ => (n : ZMod M)), Nat.cast_sum]
  simp_rw [hc]
  rw [← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs ..).trans ?_
  calc
    _ ≤ ∑ _a ∈ B, E x M := by
      apply sum_le_sum
      intro a ha
      obtain ⟨a,rfl⟩ := hB a ha
      unfold E
      exact le_ciSup_of_le (Finite.bddAbove_range _) a le_rfl
    _ = _ := by simp

/-- Simultaneous reduced residue restrictions on prime seeds have one error E(x,M)
per CRT class, with M the squarefree product of the moduli. -/
theorem prime_residue_intersection (x : ℕ) (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime)
    (B : (q : ℕ) → Finset (ZMod q)) (hB : ∀ q ∈ T, ∀ a ∈ B q, IsUnit a) :
    |(((x.primesLE.filter fun n : ℕ => ∀ q ∈ T, (n : ZMod q) ∈ B q).card : ℝ)) -
      x.primeCounting * (∏ q ∈ T, ((B q).card : ℝ)/q.totient)| ≤
      (∏ q ∈ T, ((B q).card : ℝ))*E x (∏ q ∈ T, q) := by
  classical
  let M := ∏ q : T, (q : ℕ)
  have hm : 0 < M := Finset.prod_pos (fun q _ => (hT _ q.2).pos)
  let : NeZero M := ⟨hm.ne'⟩
  let e := ZMod.prodEquivPi (fun q : T => (q : ℕ)) (fun a b hab =>
    (Nat.coprime_primes (hT _ a.2) (hT _ b.2)).2 fun he => hab (Subtype.ext he))
  let C : Finset (ZMod M) := (Fintype.piFinset (fun q : T => B q)).map e.symm.toEquiv.toEmbedding
  have hC : C.card = ∏ q ∈ T, (B q).card := by
    change (Finset.map _ _).card = _
    rw [Finset.card_map, Fintype.card_piFinset, Finset.prod_coe_sort T (fun i => (B i).card)]
  have hmem (n : ℕ) : (n : ZMod M) ∈ C ↔ ∀ q ∈ T, (n : ZMod q) ∈ B q := by
    change (n : ZMod M) ∈ (Fintype.piFinset _).map e.symm.toEquiv.toEmbedding ↔ _
    rw [Finset.mem_map_equiv]
    change e (n : ZMod M) ∈ Fintype.piFinset _ ↔ _
    rw [Fintype.mem_piFinset, map_natCast]
    exact Subtype.forall
  have hu (a : ZMod M) (ha : a ∈ C) : IsUnit a := by
    obtain ⟨v,hv,rfl⟩ := mem_map.mp ha
    have hvu : IsUnit v := Pi.isUnit_iff.mpr (fun q : T => hB q q.2 _ (Fintype.mem_piFinset.mp hv q))
    exact hvu.map e.symm
  have h := residue_sum_error x M C hu
  simp_rw [hmem] at h
  rw [hC, show M = ∏ q ∈ T, q from Finset.prod_coe_sort T id, totient_prod_primes T hT] at h
  rw [prod_div_distrib]
  simpa only [Nat.cast_prod, div_eq_mul_inv, mul_left_comm, mul_assoc, mul_comm] using h

#print axioms prime_residue_intersection

/-- Convert the real-endpoint prime-counting formulation to the natural-endpoint
DeepMind variant. The real count uses sets and the exponent starts at one. -/
theorem of_real_prime_counting (h : ∀ θ < (1/2:ℝ), ∀ A ≥ (1:ℝ), ∃ c > (0:ℝ), ∀ x ≥ (3:ℝ),
    ∑ q ∈ Icc (1:ℕ) ⌊x^θ⌋₊, ⨆ a : (ZMod q)ˣ,
      |(({p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ (p:ℝ) ≤ x}.ncard:ℝ) -
        (⌊x⌋₊.primeCounting:ℝ)/q.totient)| ≤ c*x/Real.log x^A) : BombieriVinogradov := by
  intro θ hθ A hA
  obtain ⟨c,hc,hc'⟩ := h θ hθ (max 1 A) (le_max_left ..)
  refine ⟨c,hc,fun x hx => ?_⟩
  have h3 : (3:ℝ) ≤ x := by exact_mod_cast hx
  have hlog : 1 ≤ Real.log (x:ℝ) := (Real.le_log_iff_exp_le (by positivity)).mpr
    (by linarith [Real.exp_one_lt_d9])
  have he (q : ℕ) (a : (ZMod q)ˣ) :
      {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ (p:ℝ) ≤ x}.ncard = x.primeCountingMod q a := by
    classical
    have hh : {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ (p:ℝ) ≤ x} =
        ↑((range (x+1)).filter fun p : ℕ => p.Prime ∧ (p : ZMod q) = a) := by
      ext p
      simp only [Set.mem_ofPred_eq,mem_coe,mem_filter,mem_range,Nat.lt_succ_iff,Nat.cast_le]
      tauto
    rw [hh,Set.ncard_coe_finset]
    rfl
  have hi := hc' x h3
  simp only [he,Nat.floor_natCast] at hi
  refine hi.trans (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hlog (le_max_right ..)))

#print axioms of_real_prime_counting

end CunninghamChain.PrimeSeedSieve
