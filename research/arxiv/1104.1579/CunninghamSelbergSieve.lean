import Mathlib
import research.arxiv.«1104.1579».CunninghamBatemanHorn

/-!
# A quadratic sieve for Cunningham chains

For either sign and fixed positive `k`, prime prefixes and exact chains have
count `O(x / (log x)^k)`. Distinct local zero-mean factors are orthogonal over
a full CRT period. Their truncated sum takes a fixed value on every sifted seed,
so its second moment bounds the count on a finite interval.
-/

namespace CunninghamChain

open Finset

/-- A factorial counts at least `z / q` copies of each prime `q ≤ z`.
Taking logarithms bounds the expected log modulus in the sieve. -/
lemma sieve_sum_log_div_prime_le (z : ℕ) (hz : 0 < z) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ z) :
    ∑ q ∈ Q, Real.log q / q ≤ 2 * Real.log z := by
  classical
  have hsubset : Q ⊆ z.factorial.primeFactors := by
    intro q hq
    obtain ⟨hp, hle⟩ := hQ q hq
    exact Nat.mem_primeFactors.mpr ⟨hp, Nat.dvd_factorial hp.pos hle, Nat.factorial_ne_zero _⟩
  have hm (q : ℕ) (hq : q ∈ Q) : (z : ℝ) * (Real.log q / q) ≤
      2 * ((z.factorial.factorization q : ℕ) : ℝ) * Real.log q := by
    obtain ⟨hp, hle⟩ := hQ q hq
    have hdiv : z/q ≤ z.factorial.factorization q := by
      rw [Nat.factorization_factorial hp (b := Nat.log q z + 2) (by omega)]
      have hh := Finset.single_le_sum (f := fun i => z / q^i) (s := Ico 1 (Nat.log q z+2))
        (fun i _ => Nat.zero_le _) (a := 1) (by simp)
      simpa using hh
    have hfloor : z ≤ 2*(z/q)*q := by
      have hpos := Nat.div_pos hle hp.pos
      have h := Nat.lt_div_mul_add (a := z) hp.pos
      nlinarith [Nat.mul_le_mul_right q hpos]
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
    have hh : (z : ℝ)/q ≤ 2*(z.factorial.factorization q : ℝ) := by
      apply (div_le_iff₀ hq0).mpr
      exact_mod_cast hfloor.trans (Nat.mul_le_mul_right q (Nat.mul_le_mul_left 2 hdiv))
    have hl := mul_le_mul_of_nonneg_right hh (Real.log_natCast_nonneg q)
    simpa [div_mul_eq_mul_div, mul_div_assoc, mul_comm, mul_left_comm] using hl
  have hfac : (∑ q ∈ Q, (z.factorial.factorization q : ℝ)*Real.log q) ≤
      Real.log (z.factorial : ℝ) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    exact sum_le_sum_of_subset_of_nonneg hsubset fun q _ _ =>
      mul_nonneg (by positivity) (Real.log_natCast_nonneg _)
  have hh := (Finset.sum_le_sum hm)
  rw [← mul_sum] at hh
  have heq : ∑ q ∈ Q, 2 * (z.factorial.factorization q : ℝ) * Real.log q =
      2 * ∑ q ∈ Q, (z.factorial.factorization q : ℝ) * Real.log q := by
    simp [mul_sum, mul_assoc]
  rw [heq] at hh
  have hf := Real.log_le_log (by exact_mod_cast Nat.factorial_pos z)
    (by exact_mod_cast z.factorial_le_pow : (z.factorial : ℝ) ≤ ((z^z : ℕ) : ℝ))
  rw [Nat.cast_pow, Real.log_pow] at hf
  apply le_of_mul_le_mul_left (a := (z : ℝ))
  · nlinarith
  · exact_mod_cast hz

private lemma weighted_log_moment {α : Type*} (s : Finset α) (h L : α → ℝ)
    (hn : ∀ i ∈ s, 0 ≤ h i) :
    (∑ t ∈ s.powerset, (∏ i ∈ t, h i) * ∑ i ∈ t, L i) =
      (∏ i ∈ s, (1+h i)) * ∑ i ∈ s, (h i/(1+h i))*L i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hne : 1+h a ≠ 0 := by linarith [hn a (mem_insert_self ..)]
    have old := ih (fun i hi => hn i (mem_insert_of_mem hi))
    rw [sum_powerset_insert ha, prod_insert ha, sum_insert ha]
    have expand (t : Finset α) (ht : t ∈ s.powerset) :
        (∏ i ∈ insert a t, h i) * (∑ i ∈ insert a t, L i) =
        (h a * L a) * (∏ i ∈ t, h i) + h a * ((∏ i ∈ t, h i) * ∑ i ∈ t, L i) := by
      have hat := notMem_mono (mem_powerset.mp ht) ha
      rw [prod_insert hat, sum_insert hat]
      ring
    rw [sum_congr rfl expand, sum_add_distrib, ← mul_sum, ← mul_sum, ← prod_one_add, old]
    field_simp
    ring

private def smallSubsets (Q : Finset ℕ) (y : ℕ) : Finset (Finset ℕ) :=
  Q.powerset.filter fun t => (∏ q ∈ t, q) ≤ y

/-- Truncation at `y` keeps at least half of the Euler product if its
weighted mean log modulus is at most half of `log y`. -/
private lemma half_mass (Q : Finset ℕ) (h : ℕ → ℝ) (y : ℕ) (hy : 1 < y)
    (hq : ∀ q ∈ Q, 0 < q) (hh : ∀ q ∈ Q, 0 ≤ h q)
    (hm : 2 * (∑ q ∈ Q, h q / (1+h q) * Real.log q) ≤ Real.log y) :
    (∏ q ∈ Q, (1+h q)) ≤ 2 * ∑ T ∈ smallSubsets Q y, ∏ q ∈ T, h q := by
  classical
  let W (T : Finset ℕ) := ∏ q ∈ T, h q
  let M (T : Finset ℕ) := ∏ q ∈ T, q
  let L (T : Finset ℕ) := ∑ q ∈ T, Real.log q
  let E := ∏ q ∈ Q, (1+h q)
  let good := Q.powerset.filter fun T => M T ≤ y
  let bad := Q.powerset.filter fun T => ¬M T ≤ y
  have posW {T : Finset ℕ} (ht : T ∈ Q.powerset) : 0 ≤ W T :=
    prod_nonneg fun q hqt => hh q (mem_powerset.mp ht hqt)
  have hlog {T : Finset ℕ} (ht : T ∈ Q.powerset) : Real.log (M T) = L T := by
    simp only [M, L, Nat.cast_prod]
    exact Real.log_prod fun q hqt => by exact_mod_cast (hq q (mem_powerset.mp ht hqt)).ne'
  have hs : (∑ T ∈ good, W T) + (∑ T ∈ bad, W T) = E := by
    dsimp only [good, bad, E]
    rw [Finset.sum_filter_add_sum_filter_not, Finset.prod_one_add]
  have he : 0 ≤ E := prod_nonneg fun q hq => by linarith [hh q hq]
  have hbad : (∑ T ∈ bad, W T) * Real.log y ≤ E * (∑ q ∈ Q, h q/(1+h q)*Real.log q) := by
    rw [sum_mul]
    calc
      _ ≤ ∑ T ∈ bad, W T * L T := by
        apply sum_le_sum
        intro T ht
        obtain ⟨hT, hbig⟩ := mem_filter.mp ht
        rw [← hlog hT]
        apply mul_le_mul_of_nonneg_left _ (posW hT)
        exact Real.log_le_log (by positivity) (by exact_mod_cast (lt_of_not_ge hbig).le)
      _ ≤ ∑ T ∈ Q.powerset, W T * L T := by
        exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun T ht _ =>
          mul_nonneg (posW ht) (sum_nonneg fun q _ => Real.log_natCast_nonneg q)
      _ = _ := weighted_log_moment Q h _ hh
  have hb : 2*(∑ T ∈ bad, W T) ≤ E := by
    apply le_of_mul_le_mul_right (a := Real.log y)
    · nlinarith [mul_le_mul_of_nonneg_left hm he]
    · exact Real.log_pos (by exact_mod_cast hy)
  change E ≤ 2 * ∑ T ∈ good, W T
  linarith

private lemma truncated_euler_mass (k z : ℕ) (hk : 0 < k) (hz : 1 < z) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ k < q ∧ q ≤ z) :
    let h (q : ℕ) := (k : ℝ) / ((q : ℝ)-k)
    (∏ q ∈ Q, (1+h q)) ≤ 2 * ∑ T ∈ smallSubsets Q (z^(4*k)), ∏ q ∈ T, h q := by
  dsimp only
  apply half_mass _ _ _ (one_lt_pow₀ hz (by omega)) (fun q hq => (hQ q hq).1.pos)
  · intro q hq
    exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast (hQ q hq).2.1.le))
  · have hfac (q : ℕ) (hq : q ∈ Q) : (k : ℝ)/((q : ℝ)-k) / (1+k/((q : ℝ)-k)) = (k : ℝ)/q := by
      have hq' : (k : ℝ) < q := by exact_mod_cast (hQ q hq).2.1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (hQ q hq).1.pos
      have hden := (sub_pos.mpr hq').ne'
      have he : 1+(k:ℝ)/((q:ℝ)-k) = q/((q:ℝ)-k) := by field_simp [hden]; ring
      rw [he]
      field_simp [hden, hq0.ne']
    have hm := sieve_sum_log_div_prime_le z (by omega) Q (fun q hq => ⟨(hQ q hq).1, (hQ q hq).2.2⟩)
    have he : (∑ q ∈ Q, (k : ℝ)/((q : ℝ)-k) / (1+k/((q : ℝ)-k)) * Real.log q) =
        k * ∑ q ∈ Q, Real.log q / q := by
      rw [mul_sum]
      exact sum_congr rfl fun q hq => by rw [hfac q hq]; ring
    rw [he, Nat.cast_pow, Real.log_pow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) k)]

private noncomputable def residueMean (q : ℕ) (f : ZMod q → ℝ) : ℝ :=
  (∑ n ∈ range q, f (n : ZMod q)) / q

private lemma full_period_sum {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    (∑ n ∈ range q, f (n : ZMod q)) = ∑ a : ZMod q, f a := by
  classical
  apply sum_bij' (fun (n : ℕ) _ => (n : ZMod q)) (fun (a : ZMod q) _ => a.val)
  · simp
  · exact fun a _ => mem_range.mpr a.val_lt
  · intro n hn
    simpa using Nat.mod_eq_of_lt (mem_range.mp hn : n < q)
  · simp
  · simp

private lemma periodic_error (N M : ℕ) [NeZero M] (f : ZMod M → ℝ) (hf : ∀ a, |f a| ≤ 1) :
    |(∑ n ∈ range N, f (n : ZMod M)) - (N : ℝ)*residueMean M f| ≤ 2*M := by
  let s (j : ℕ) := ∑ n ∈ range j, f (n : ZMod M)
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  have hshift (a b : ℕ) : s (M*a+b) = s (M*a) + s b := by
    unfold s
    rw [sum_range_add]
    simp
  have hblocks (a : ℕ) : s (M*a) = a * s M := by
    induction a with
    | zero => simp [s]
    | succ a ih => rw [Nat.mul_succ, hshift, ih]; push_cast; ring
  have hbound (a : ℕ) : |s a| ≤ a := by
    refine (abs_sum_le_sum_abs ..).trans ?_
    simpa using (sum_le_sum (s := range a) fun i _ => hf (i : ZMod M))
  have hm : |residueMean M f| ≤ 1 := by
    rw [residueMean, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) M), div_le_one (by exact_mod_cast hM)]
    exact hbound M
  have he : (∑ n ∈ range N, f (n : ZMod M)) - (N : ℝ)*residueMean M f =
      s (N%M) - (N%M : ℕ)*residueMean M f := by
    change s N - _ = _
    conv_lhs => rw [← Nat.div_add_mod N M]
    rw [hshift, hblocks]
    change _ - _ * (s M / M) = _ - _ * (s M / M)
    push_cast
    field_simp
    ring
  rw [he]
  have hrem : ((N%M : ℕ) : ℝ) ≤ M := by exact_mod_cast (Nat.mod_lt N hM).le
  calc
    _ ≤ |s (N%M)| + |(N%M : ℕ)*residueMean M f| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (N%M))]
      nlinarith [hbound (N%M), mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) (N%M))]

private lemma crt_mean_error (N : ℕ) (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime)
    (v : (q : ℕ) → ZMod q → ℝ) (hv : ∀ q ∈ T, ∀ a, |v q a| ≤ 1) :
    |(∑ n ∈ range N, ∏ q ∈ T, v q n) - (N : ℝ)* ∏ q ∈ T, residueMean q (v q)| ≤
      2*(∏ q ∈ T, q : ℕ) := by
  classical
  let M := ∏ q : T, (q : ℕ)
  have hM : 0 < M := prod_pos fun q _ => (hT q q.2).pos
  let : NeZero M := ⟨hM.ne'⟩
  let (q : T) : NeZero (q : ℕ) := ⟨(hT q q.2).ne_zero⟩
  let e := ZMod.prodEquivPi (fun q : T => (q : ℕ)) (fun a b hab =>
    (Nat.coprime_primes (hT a a.2) (hT b b.2)).2 fun he => hab (Subtype.ext he))
  let V (a : ZMod M) := ∏ q : T, v q (e a q)
  have hb (a : ZMod M) : |V a| ≤ 1 := by
    dsimp [V]
    rw [Finset.abs_prod]
    exact prod_le_one (fun _ _ => abs_nonneg _) (fun q _ => hv q q.2 _)
  have hnat (n : ℕ) : V (n : ZMod M) = ∏ q ∈ T, v q n := by
    dsimp only [V]
    rw [map_natCast]
    exact prod_coe_sort T (fun q => v q n)
  have hs : (∑ a : ZMod M, V a) = ∏ q : T, ∑ a : ZMod (q : ℕ), v q a := by
    calc
      _ = ∑ x : ((q : T) → ZMod (q : ℕ)), ∏ q : T, v q (x q) := e.toEquiv.sum_comp _
      _ = _ := by simpa using (prod_univ_sum (fun q : T => (univ : Finset (ZMod (q : ℕ))))
        (fun (q : T) a => v q a)).symm
  have hd : residueMean M V = ∏ q ∈ T, residueMean q (v q) := by
    rw [residueMean, full_period_sum, hs, ← prod_coe_sort T (fun q => residueMean q (v q))]
    simp only [residueMean, full_period_sum, prod_div_distrib]
    simp [M]
  have H := periodic_error N M V hb
  simp_rw [hnat] at H
  rw [hd] at H
  simpa only [M, prod_coe_sort T (fun i => i)] using H

private noncomputable def twoLevel {q : ℕ} (B : Finset (ZMod q)) (c d : ℝ) (a : ZMod q) : ℝ :=
  if a ∈ B then c else d

private lemma mean_twoLevel {q : ℕ} [NeZero q] (B : Finset (ZMod q)) (c d : ℝ) :
    residueMean q (twoLevel B c d) = (B.card*c + (q-B.card : ℝ)*d) / q := by
  classical
  rw [residueMean, full_period_sum]
  unfold twoLevel
  rw [sum_ite]
  have h₁ : (univ.filter (· ∈ B)) = B := by ext; simp
  have h₂ : (univ.filter (fun a => a ∉ B)) = Bᶜ := by ext; simp
  have hle : B.card ≤ q := by simpa [ZMod.card] using B.card_le_univ
  simp [h₁, h₂, Finset.card_compl, Nat.cast_sub hle, ZMod.card]

private lemma centered_local {q k : ℕ} [NeZero q] (B : Finset (ZMod q)) (hb : B.card = k)
    (hq : 2*k < q) :
    let h := (k : ℝ)/((q : ℝ)-k)
    let v := twoLevel B (-1) h
    (∀ a, |v a| ≤ 1) ∧ residueMean q v = 0 ∧ residueMean q (fun a => v a*v a) = h := by
  dsimp only
  have hkq : (k : ℝ) < q := by exact_mod_cast (by omega : k < q)
  have hkq' : (2 : ℝ)*k ≤ q := by exact_mod_cast hq.le
  have hden := sub_pos.mpr hkq
  have hn := (Nat.cast_nonneg (α := ℝ) k)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  constructor
  · intro a
    unfold twoLevel
    split
    · norm_num
    · rw [abs_of_nonneg (div_nonneg hn hden.le)]
      exact (div_le_one hden).mpr (by linarith)
  constructor
  · rw [mean_twoLevel, hb]
    field_simp [hden.ne', hq0]
    ring
  · have he (a : ZMod q) : twoLevel B (-1) ((k:ℝ)/(q-k)) a * twoLevel B (-1) ((k:ℝ)/(q-k)) a =
        twoLevel B 1 (((k:ℝ)/(q-k))^2) a := by unfold twoLevel; split <;> ring
    simp_rw [he]
    rw [mean_twoLevel, hb]
    field_simp [hden.ne', hq0]
    ring

private def component (T : Finset ℕ) (v : (q : ℕ) → ZMod q → ℝ) (n : ℕ) : ℝ :=
  ∏ q ∈ T, v q n

/-- Only equal subsets contribute to the full-period mean of the quadratic form. -/
private lemma pair_mean_error (N : ℕ) (T U : Finset ℕ) (hQ : ∀ q ∈ T ∪ U, q.Prime)
    (v : (q : ℕ) → ZMod q → ℝ) (h : ℕ → ℝ)
    (hv : ∀ q ∈ T ∪ U, (∀ a, |v q a| ≤ 1) ∧ residueMean q (v q) = 0 ∧
      residueMean q (fun a => v q a * v q a) = h q) :
    |(∑ n ∈ range N, component T v n * component U v n) -
      (N : ℝ) * (if T = U then ∏ q ∈ T, h q else 0)| ≤ 2 * (∏ q ∈ T ∪ U, q : ℕ) := by
  classical
  let w (q : ℕ) (a : ZMod q) := (if q ∈ T then v q a else 1) * (if q ∈ U then v q a else 1)
  have hw (q : ℕ) (hq : q ∈ T ∪ U) (a : ZMod q) : |w q a| ≤ 1 := by
    dsimp [w]
    rw [abs_mul]
    have hv' := (hv q hq).1 a
    apply mul_le_one₀
    · split <;> simp only [hv', abs_one, le_refl]
    · exact abs_nonneg _
    · split <;> simp only [hv', abs_one, le_refl]
  have hcomp (n : ℕ) : (∏ q ∈ T ∪ U, w q n) = component T v n * component U v n := by
    have hprod (S : Finset ℕ) (hs : S ⊆ T ∪ U) :
        (∏ q ∈ T ∪ U, if q ∈ S then v q n else 1) = ∏ q ∈ S, v q n := by
      calc
        _ = ∏ q ∈ S, (if q ∈ S then v q n else 1) :=
          (prod_subset hs (fun q _ hq => if_neg hq)).symm
        _ = _ := prod_congr rfl fun q hq => if_pos hq
    dsimp only [w, component]
    rw [prod_mul_distrib, hprod T subset_union_left, hprod U subset_union_right]
  have hmean : (∏ q ∈ T ∪ U, residueMean q (w q)) = if T = U then ∏ q ∈ T, h q else 0 := by
    split_ifs with he
    · subst U
      rw [union_self]
      refine prod_congr rfl fun q hq => ?_
      have hq' : q ∈ T ∪ T := mem_union_left _ hq
      simpa [w, hq] using (hv q hq').2.2
    · obtain ⟨q, hq⟩ : ∃ q, ¬(q ∈ T ↔ q ∈ U) := by
        by_contra! h
        exact he (Finset.ext h)
      by_cases ht : q ∈ T
      · have hu : q ∉ U := fun hu => hq (iff_of_true ht hu)
        have hqu := mem_union_left U ht
        exact prod_eq_zero hqu (by simpa [w, ht, hu] using (hv q hqu).2.1)
      · have hu : q ∈ U := by tauto
        have hqu := mem_union_right T hu
        exact prod_eq_zero hqu (by simpa [w, ht, hu] using (hv q hqu).2.1)
  simpa only [hcomp, hmean] using crt_mean_error N (T ∪ U) hQ w hw

private lemma small_card {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (y : ℕ) :
    (smallSubsets Q y).card ≤ y := by
  let m (T : Finset ℕ) := ∏ q ∈ T, q
  have hc (T : Finset ℕ) (hT : T ∈ smallSubsets Q y) :
      (m T).primeFactors = T := Nat.primeFactors_prod (fun q hq => hQ q
        ((mem_powerset.mp (mem_filter.mp hT).1) hq))
  have H := card_le_card_of_injOn m (s := smallSubsets Q y) (t := Icc 1 y)
    (fun T hT => mem_Icc.mpr ⟨prod_pos (fun q hq => (hQ q ((mem_powerset.mp
      (mem_filter.mp hT).1) hq)).pos), (mem_filter.mp hT).2⟩)
    (fun T hT U hU he => (hc T hT).symm.trans ((congrArg Nat.primeFactors he).trans (hc U hU)))
  simpa using H

/-- On every seed in `A` the truncated sum equals `G`. Its interval second moment is
at most the diagonal contribution `N*G` plus the sum of the periodic errors. -/
private lemma selberg_bound (N y : ℕ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (v : (q : ℕ) → ZMod q → ℝ) (h : ℕ → ℝ)
    (hv : ∀ q ∈ Q, (∀ a, |v q a| ≤ 1) ∧ residueMean q (v q) = 0 ∧
      residueMean q (fun a => v q a * v q a) = h q)
    (A : Finset ℕ) (hA : A ⊆ range N) (hsafe : ∀ n ∈ A, ∀ q ∈ Q, v q n = h q) :
    let G := ∑ T ∈ smallSubsets Q y, ∏ q ∈ T, h q
    (A.card : ℝ)*G^2 ≤ N*G + 2*(y:ℝ)^4 := by
  classical
  let D := smallSubsets Q y
  let W (n : ℕ) := ∑ T ∈ D, component T v n
  let G := ∑ T ∈ D, ∏ q ∈ T, h q
  have sub {T : Finset ℕ} (hT : T ∈ D) : T ⊆ Q := mem_powerset.mp (mem_filter.mp hT).1
  have hval (n : ℕ) (hn : n ∈ A) : W n = G := sum_congr rfl fun T hT =>
    prod_congr rfl fun q hq => hsafe n hn q (sub hT hq)
  have hle : A.card*G^2 ≤ ∑ n ∈ range N, (W n)^2 := by
    calc
      _ = ∑ _ ∈ A, G^2 := by simp
      _ = ∑ n ∈ A, (W n)^2 := sum_congr rfl fun n hn => by rw [hval n hn]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hA fun n _ _ => sq_nonneg _
  have hcorr (T : Finset ℕ) (hT : T ∈ D) (U : Finset ℕ) (hU : U ∈ D) :
      (∑ n ∈ range N, component T v n * component U v n) ≤
        N*(if T = U then ∏ q ∈ T, h q else 0) + 2*(y:ℝ)^2 := by
    have hu := union_subset (sub hT) (sub hU)
    have H := (abs_le.mp (pair_mean_error N T U (fun q hq => hQ q (hu hq)) v h
      (fun q hq => hv q (hu hq)))).2
    have hprod : ∏ q ∈ T ∪ U, q ≤ y^2 := by
      have hpos : 1 ≤ ∏ q ∈ T ∩ U, q := prod_pos fun q hq => (hQ q (sub hT (mem_inter.mp hq).1)).pos
      have hd := prod_union_inter (s₁ := T) (s₂ := U) (f := id)
      calc
        _ ≤ (∏ q ∈ T ∪ U, q) * (∏ q ∈ T ∩ U, q) := Nat.le_mul_of_pos_right _ hpos
        _ = _ := hd
        _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul (mem_filter.mp hT).2 (mem_filter.mp hU).2
    linarith [show ((∏ q ∈ T ∪ U, q : ℕ) : ℝ) ≤ (y:ℝ)^2 by exact_mod_cast hprod]
  have hexpand : ∑ n ∈ range N, (W n)^2 =
      ∑ T ∈ D, ∑ U ∈ D, ∑ n ∈ range N, component T v n * component U v n := by
    simp only [W, sq, sum_mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun T _ => sum_comm
  rw [hexpand] at hle
  refine hle.trans ((sum_le_sum fun T hT => sum_le_sum fun U hU => hcorr T hT U hU).trans ?_)
  have hdiag (T : Finset ℕ) (ht : T ∈ D) :
      (∑ U ∈ D, (N : ℝ)*(if T = U then ∏ q ∈ T, h q else 0)) =
        N * ∏ q ∈ T, h q := by rw [← mul_sum]; simp [ht]
  have hcard : (D.card : ℝ) ≤ y := by exact_mod_cast small_card hQ y
  simp_rw [sum_add_distrib]
  rw [sum_congr rfl hdiag, ← mul_sum]
  simp only [sum_const, nsmul_eq_mul]
  change (N:ℝ)*G + _ ≤ (N:ℝ)*G + _
  refine add_le_add (le_refl _) ?_
  calc
    _ ≤ (y : ℝ) * (y*(2*y^2)) := by gcongr
    _ = _ := by ring

private noncomputable def localShift (b : Bool) (q : ℕ) : ZMod q := if b then 1 else -1

private noncomputable def chainRoots (b : Bool) (I : Finset ℕ) (q : ℕ) : Finset (ZMod q) := by
  classical exact I.image fun i => localShift b q * (((2 : ZMod q)^i)⁻¹ - 1)

private lemma chainRoots_card (b : Bool) {I : Finset ℕ} {q : ℕ} (hq : q.Prime)
    (hinj : Set.InjOn (fun i : ℕ => (2 : ZMod q)^i) I) :
    (chainRoots b I q).card = I.card := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  unfold chainRoots
  apply card_image_of_injOn
  intro i hi j hj h
  have hs : localShift b q ≠ 0 := by cases b <;> simp [localShift]
  exact hinj hi hj (inv_injective (sub_left_inj.mp (mul_left_cancel₀ hs h)))

private lemma powers_injective_in_range {k q : ℕ} (hlt : 2^k < q) :
    Set.InjOn (fun i : ℕ => (2 : ZMod q)^i) (range k) := by
  intro i hi j hj he
  have hc : ((2^i : ℕ) : ZMod q) = ((2^j : ℕ) : ZMod q) := by simpa using he
  have hm := (ZMod.natCast_eq_natCast_iff ..).mp hc
  have hi' : 2^i < q := (Nat.pow_le_pow_right (by decide : 0 < 2) (mem_range.mp hi).le).trans_lt hlt
  have hj' : 2^j < q := (Nat.pow_le_pow_right (by decide : 0 < 2) (mem_range.mp hj).le).trans_lt hlt
  change 2^i % q = 2^j % q at hm
  rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hm
  exact Nat.pow_right_injective (by decide : 1 < 2) hm

private def chainTerm (b : Bool) : ℕ → ℕ → ℕ := if b then firstKindTerm else secondKindTerm

private lemma seed_le_term (b : Bool) {p : ℕ} (_hp : 0 < p) (i : ℕ) : p ≤ chainTerm b p i := by
  cases b <;> induction i with
  | zero => rfl
  | succ i ih =>
    first
    | change p ≤ 2*secondKindTerm p i - 1
      change p ≤ secondKindTerm p i at ih
      omega
    | change p ≤ 2*firstKindTerm p i + 1
      change p ≤ firstKindTerm p i at ih
      omega

private lemma term_eq_mod (b : Bool) (q p i : ℕ) (hp : 0 < p) :
    (chainTerm b p i : ZMod q) = 2^i * ((p : ZMod q)+localShift b q) - localShift b q := by
  cases b
  · induction i with
    | zero => simp [chainTerm, secondKindTerm]
    | succ i ih =>
      change ((2*secondKindTerm p i-1 : ℕ) : ZMod q) = _
      have h := seed_le_term false hp i
      change p ≤ secondKindTerm p i at h
      rw [Nat.cast_sub (by omega : 1 ≤ 2*secondKindTerm p i)]
      push_cast
      change ((secondKindTerm p i : ℕ) : ZMod q) = _ at ih
      rw [ih]
      simp [localShift, pow_succ]
      ring
  · induction i with
    | zero => simp [chainTerm, firstKindTerm]
    | succ i ih =>
      change ((2*firstKindTerm p i+1 : ℕ) : ZMod q) = _
      push_cast
      change ((firstKindTerm p i : ℕ) : ZMod q) = _ at ih
      rw [ih]
      simp [localShift, pow_succ]
      ring

private lemma avoids_chainRoots (b : Bool) {I : Finset ℕ} {p q : ℕ} (hq : q.Prime) (hq2 : 2 < q) (hp : q < p)
    (h : ∀ i ∈ I, (chainTerm b p i).Prime) : (p : ZMod q) ∉ chainRoots b I q := by
  let : Fact q.Prime := ⟨hq⟩
  have hp0 : 0 < p := by omega
  have h2 : (2 : ZMod q) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq2)
  intro hmem
  obtain ⟨i, hi, he⟩ := mem_image.mp hmem
  have hd : (chainTerm b p i : ZMod q) = 0 := by
    rw [term_eq_mod b q p i hp0, ← he]
    field_simp
    ring
  have heq := (Nat.prime_dvd_prime_iff_eq hq (h i hi)).mp
    ((ZMod.natCast_eq_zero_iff ..).mp hd)
  exact (hp.trans_le (seed_le_term b hp0 i)).ne heq

private noncomputable def eulerFactor (q : ℕ) : ℝ := (1 - (q : ℝ)⁻¹)⁻¹

private lemma eulerFactor_pos {q : ℕ} (hq : q.Prime) : 0 < eulerFactor q :=
  inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.one_lt)))

private lemma log_le_euler (z : ℕ) : Real.log ((z : ℝ)+1) ≤ ∏ q ∈ z.primesLE, eulerFactor q := by
  classical
  let f : ℕ →* ℝ :=
    { toFun := fun n : ℕ => (n : ℝ)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by simp [mul_comm] }
  have hlocal {q : ℕ} (hq : q.Prime) : ‖f q‖ < 1 := by
    change ‖(q : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.one_lt)
  let I := Icc 1 z
  let e : I ↪ (z+1).smoothNumbers :=
    ⟨fun i => ⟨(i : ℕ), Nat.mem_smoothNumbers_of_lt (mem_Icc.mp i.2).1
      (Nat.lt_succ_of_le (mem_Icc.mp i.2).2)⟩,
      fun _ _ ha => Subtype.ext (congrArg (fun i : (z+1).smoothNumbers => (i : ℕ)) ha)⟩
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := f) hlocal (z+1)).2
  have hs := sum_le_hasSum (univ.map e) (fun _ _ => (by dsimp [f]; positivity)) h
  rw [sum_map] at hs
  change (∑ i : I, ((i : ℕ) : ℝ)⁻¹) ≤ _ at hs
  rw [sum_coe_sort I (fun i => (i : ℝ)⁻¹)] at hs
  have hl := log_add_one_le_harmonic z
  rw [harmonic_eq_sum_Icc] at hl
  push_cast at hl
  exact hl.trans hs

private lemma local_majorant {k q : ℕ} (hq : q.Prime) (hkq : k < q) :
    (eulerFactor q)^k ≤ 1 + (k : ℝ)/((q : ℝ)-k) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hkq' : (k : ℝ) < q := by exact_mod_cast hkq
  have ha : 0 < 1 - (q : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.one_lt))
  have hber := one_add_le_pow_of_two_add_nonneg (a := -((q : ℝ)⁻¹)) (by linarith) k
  have hb : (q-k : ℝ)/q ≤ (1 - (q : ℝ)⁻¹)^k := by
    have he : (q-k : ℝ)/q = 1 + k * -((q:ℝ)⁻¹) := by field_simp [hq0.ne']; ring
    rw [he, sub_eq_add_neg]
    exact hber
  have hc := (inv_le_inv₀ (pow_pos ha k) (div_pos (sub_pos.mpr hkq') hq0)).mpr hb
  change ((1-(q:ℝ)⁻¹)⁻¹)^k ≤ _
  rw [inv_pow]
  refine hc.trans_eq ?_
  field_simp [sub_ne_zero.mpr hkq'.ne', hq0.ne']
  ring

private lemma sieve_mass_lower (k z : ℕ) (E : Finset ℕ) (hk : 0 < k) (hz' : 1 < z)
    (hs : E ⊆ z.primesLE) (hr : ∀ q ∈ z.primesLE \ E, k < q) :
    let Q := z.primesLE \ E
    let h (q : ℕ) := (k : ℝ)/((q : ℝ)-k)
    let G := ∑ T ∈ smallSubsets Q (z^(4*k)), ∏ q ∈ T, h q
    (Real.log ((z : ℝ)+1))^k ≤ 2*(∏ q ∈ E, eulerFactor q)^k * G := by
  let Q := z.primesLE \ E
  have hQ {q : ℕ} (hq : q ∈ Q) : q.Prime ∧ k < q ∧ q ≤ z :=
    ⟨Nat.prime_of_mem_primesLE (mem_sdiff.mp hq).1, hr q hq, Nat.le_of_mem_primesLE (mem_sdiff.mp hq).1⟩
  have hsmall := prod_pos (f := eulerFactor) (fun q (hq : q ∈ E) =>
    eulerFactor_pos (Nat.prime_of_mem_primesLE (hs hq)))
  have hprod : (∏ q ∈ z.primesLE, eulerFactor q) =
      (∏ q ∈ Q, eulerFactor q) * ∏ q ∈ E, eulerFactor q := (prod_sdiff hs).symm
  have hl := pow_le_pow_left₀ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) z]))
    (log_le_euler z) k
  rw [hprod, mul_pow, ← prod_pow] at hl
  have hab := prod_le_prod (s := Q) (fun q hq => pow_nonneg (eulerFactor_pos (hQ hq).1).le k)
    (fun q hq => local_majorant (hQ hq).1 (hQ hq).2.1)
  have hm := truncated_euler_mass k z hk hz' Q (fun _ hq => hQ hq)
  have hbound := mul_le_mul_of_nonneg_right (hab.trans hm) (pow_nonneg hsmall.le k)
  exact hl.trans (hbound.trans_eq (by ring))

private def cutoff (k : ℕ) := 2^k + 2*k + 2

private noncomputable def sieveConstant (k : ℕ) : ℝ :=
  6*(∏ q ∈ (cutoff k).primesLE, eulerFactor q)^k

/-- A finite sieve for arbitrary forbidden residue classes, uniform in their locations. -/
theorem finite_residue_sieve_bound (E : Finset ℕ) (R : (q : ℕ) → Finset (ZMod q))
    (A : Finset ℕ) {k z N : ℕ} (hk : 0 < k) (hz : 1 < z) (hE : E ⊆ z.primesLE)
    (hreg : ∀ q ∈ z.primesLE \ E, 2*k < q ∧ (R q).card=k)
    (hA : A ⊆ range N) (hsafe : ∀ n ∈ A, ∀ q ∈ z.primesLE \ E, (n:ZMod q) ∉ R q)
    (hy : (z^(4*k))^4 ≤ N) :
    (A.card : ℝ)*(Real.log ((z:ℝ)+1))^k ≤ 6*(∏ q ∈ E, (1-1/(q:ℝ))⁻¹)^k*N := by
  classical
  let Q := z.primesLE \ E
  let h (q : ℕ) := (k : ℝ)/((q:ℝ)-k)
  let y := z^(4*k)
  let D := smallSubsets Q y
  let G := ∑ T ∈ D, ∏ q ∈ T, h q
  let v (q : ℕ) := twoLevel (R q) (-1) (h q)
  have hQ {q : ℕ} (hq : q ∈ Q) : q.Prime ∧ 2*k < q ∧ q ≤ z :=
    ⟨Nat.prime_of_mem_primesLE (mem_sdiff.mp hq).1, (hreg q hq).1, Nat.le_of_mem_primesLE (mem_sdiff.mp hq).1⟩
  have hv (q : ℕ) (hq : q ∈ Q) := by
    have ⟨hp, hc, _⟩ := hQ hq
    let : NeZero q := ⟨hp.ne_zero⟩
    exact centered_local (R q) (hreg q hq).2 hc
  have hs := selberg_bound N y Q (fun q hq => (hQ hq).1) v h hv A hA
    (fun n hn q hq => if_neg (hsafe n hn q hq))
  have hmass := sieve_mass_lower k z E hk hz hE (fun q hq => by have := (hreg q hq).1; omega)
  have hpos (q : ℕ) (hq : q ∈ Q) : 0 ≤ h q := by
    have hc := (hQ hq).2.1
    exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast (by omega : k ≤ q)))
  have hG : 1 ≤ G := by
    have hz0 : 1 ≤ y := Nat.one_le_pow _ _ (by omega)
    have he : ∅ ∈ D := by simp [D, smallSubsets, hz0]
    simpa only [prod_empty] using (single_le_sum (s := D) (f := fun T => ∏ q ∈ T, h q)
      (fun T hT => prod_nonneg fun q hq => hpos q ((mem_powerset.mp (mem_filter.mp hT).1) hq)) he)
  change A.card*G^2 ≤ (N:ℝ)*G + 2*(y:ℝ)^4 at hs
  have hy' : (y:ℝ)^4 ≤ N := by exact_mod_cast hy
  have hAG : (A.card : ℝ)*G ≤ 3*N := by
    apply le_of_mul_le_mul_right (a := G)
    · nlinarith [mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg (α := ℝ) N)]
    · linarith
  let F := (∏ q ∈ E, eulerFactor q)^k
  have hF : 0 ≤ F := pow_nonneg (prod_nonneg fun q hq => (eulerFactor_pos (Nat.prime_of_mem_primesLE (hE hq))).le) _
  change (Real.log ((z:ℝ)+1))^k ≤ 2*F*G at hmass
  simp only [one_div]
  change (A.card : ℝ)*_ ≤ 6*F*N
  nlinarith only [mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg (α := ℝ) A.card),
    mul_le_mul_of_nonneg_right hAG (show 0 ≤ 2*F by positivity)]

/-- Sieve a finite selection of iterate indices. Distinct powers modulo each
retained prime give the required number of distinct forbidden seed residues. -/
theorem finite_iterate_sieve_bound (b : Bool) (I E : Finset ℕ) {k z N : ℕ}
    (hI : I.card = k) (hk : 0 < k) (hz : 1 < z) (hE : E ⊆ z.primesLE)
    (hreg : ∀ q ∈ z.primesLE \ E,
      2*k < q ∧ Set.InjOn (fun i : ℕ => (2 : ZMod q)^i) I)
    (hy : (z^(4*k))^4 ≤ N) :
    (((range N).filter fun p => z < p ∧
      ∀ i ∈ I, ((if b then firstKindTerm else secondKindTerm) p i).Prime).card : ℝ) *
      (Real.log ((z : ℝ)+1))^k ≤ 6*(∏ q ∈ E, (1-1/(q:ℝ))⁻¹)^k*N := by
  classical
  apply finite_residue_sieve_bound E (chainRoots b I) _ hk hz hE _ (filter_subset ..) _ hy
  · intro q hq
    have hp := Nat.prime_of_mem_primesLE (mem_sdiff.mp hq).1
    exact ⟨(hreg q hq).1,(chainRoots_card b hp (hreg q hq).2).trans hI⟩
  · intro n hn q hq
    obtain ⟨_,hnz,hprime⟩ := mem_filter.mp hn
    have hp := Nat.prime_of_mem_primesLE (mem_sdiff.mp hq).1
    have hc := (hreg q hq).1
    have hle := Nat.le_of_mem_primesLE (mem_sdiff.mp hq).1
    exact avoids_chainRoots b hp (by omega) (hle.trans_lt hnz) hprime

#print axioms finite_residue_sieve_bound

private lemma finite_chain_bound (b : Bool) {k z N : ℕ} (hk : 0 < k) (hz : cutoff k ≤ z)
    (hy : (z^(4*k))^4 ≤ N) :
    (((range N).filter fun p => z < p ∧ ∀ i < k, (chainTerm b p i).Prime).card : ℝ) *
      (Real.log ((z : ℝ)+1))^k ≤ sieveConstant k * N := by
  let C := cutoff k
  have hc : 2^k ≤ C ∧ 2*k ≤ C ∧ 2 ≤ C := by
    dsimp [C,cutoff]
    exact ⟨(Nat.le_add_right ..).trans (Nat.le_add_right _ 2),
      (Nat.le_add_left ..).trans (Nat.le_add_right _ 2),Nat.le_add_left ..⟩
  have hE : C.primesLE ⊆ z.primesLE := fun _ hq => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE hq).trans hz,Nat.prime_of_mem_primesLE hq⟩
  have hreg (q : ℕ) (hq : q ∈ z.primesLE \ C.primesLE) : 2*k < q ∧
      Set.InjOn (fun i : ℕ => (2 : ZMod q)^i) (range k) := by
    obtain ⟨hqz,hqc⟩ := mem_sdiff.mp hq
    have hlt : C < q := by
      by_contra! h
      exact hqc (Nat.mem_primesLE.mpr ⟨h,Nat.prime_of_mem_primesLE hqz⟩)
    exact ⟨by omega,powers_injective_in_range (by omega)⟩
  have h := finite_iterate_sieve_bound b (range k) C.primesLE (card_range k) hk (by omega) hE hreg hy
  convert h using 2
  · congr 2
    apply Finset.filter_congr
    intro p _
    simp only [mem_range,chainTerm]
  · simp [sieveConstant,eulerFactor,C,one_div]

#print axioms finite_iterate_sieve_bound

open Filter Asymptotics
open scoped Topology

/-- Number of seeds at most ⌊x⌋ in ℕ with a prime prefix of length k.
The flag selects the first kind when true and the second kind when false. -/
noncomputable def primePrefixSeedCount (b : Bool) (k : ℕ) (x : ℝ) : ℕ := by
  classical exact ((range (⌊x⌋₊+1)).filter fun p =>
    ∀ i < k, ((if b then firstKindTerm else secondKindTerm) p i).Prime).card

private lemma prefix_split (b : Bool) (k z : ℕ) (x : ℝ) :
    primePrefixSeedCount b k x ≤ z+1 +
      ((range (⌊x⌋₊+1)).filter fun p => z < p ∧ ∀ i < k, (chainTerm b p i).Prime).card := by
  classical
  let big := (range (⌊x⌋₊+1)).filter fun p => z < p ∧ ∀ i < k, (chainTerm b p i).Prime
  let allSeeds := (range (⌊x⌋₊+1)).filter fun p => ∀ i < k, (chainTerm b p i).Prime
  have hs : allSeeds ⊆ range (z+1) ∪ big := by
    intro p hp
    obtain ⟨hr, hc⟩ := mem_filter.mp hp
    exact mem_union.mpr ((le_or_gt p z).imp (fun h => mem_range.mpr (by omega))
      (fun h => mem_filter.mpr ⟨hr, h, hc⟩))
  exact (card_le_card hs).trans (by simpa only [card_range] using card_union_le (range (z+1)) big)

/-- Unconditional upper-bound sieve for either Cunningham recurrence, for each fixed k > 0. -/
theorem primePrefixSeedCount_isBigO (b : Bool) {k : ℕ} (hk : 0 < k) :
    (fun x : ℝ => (primePrefixSeedCount b k x : ℝ)) =O[atTop]
      (fun x : ℝ => x / (Real.log x)^k) := by
  classical
  let d : ℝ := 16 * k
  let a : ℝ := 1/d
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < d := by dsimp [d]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a ≤ (1:ℝ)/2 := by dsimp [a]; rw [div_le_div_iff₀ hd (by norm_num)]; dsimp [d]; linarith
  have hs₀ : 0 ≤ sieveConstant k := by
    unfold sieveConstant
    exact mul_nonneg (by norm_num) (pow_nonneg (prod_nonneg fun q hq =>
      (eulerFactor_pos (Nat.prime_of_mem_primesLE hq)).le) _)
  apply IsBigO.of_bound (2 + 2*d^k*sieveConstant k)
  have hcut := (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop ha)).eventually_ge_atTop (cutoff k)
  have hlog := (isLittleO_log_rpow_rpow_atTop (k : ℝ)
    (by norm_num : (0:ℝ) < 1/2)).bound (by norm_num : (0:ℝ) < 1)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hcut, hlog] with x hx hz hlog
  let z := ⌊x^a⌋₊
  let N := ⌊x⌋₊+1
  let B := ((range N).filter fun p => z < p ∧ ∀ i < k, (chainTerm b p i).Prime).card
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hl := Real.log_pos hx
  have hz₁ : (z:ℝ) ≤ x^a := Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hz₂ : x^a < (z:ℝ)+1 := Nat.lt_floor_add_one _
  have hN₁ : x < (N:ℝ) := by simpa [N] using Nat.lt_floor_add_one x
  have hN₂ : (N:ℝ) ≤ 2*x := by dsimp [N]; push_cast; linarith [Nat.floor_le hx0.le]
  have hzN : (z^(4*k))^4 ≤ N := by
    have he : a * ((4*k*4 : ℕ) : ℝ) = 1 := by
      push_cast; dsimp [a, d]; field_simp; ring
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) z) hz₁ (4*k*4)
    rw [← Real.rpow_mul_natCast hx0.le, he, Real.rpow_one, pow_mul] at h
    exact_mod_cast (h.trans hN₁.le)
  have hbig := finite_chain_bound b hk hz hzN
  change (B:ℝ) * _ ≤ _ at hbig
  have hlogz : Real.log x ≤ d * Real.log ((z:ℝ)+1) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hx0 a) hz₂.le
    rw [Real.log_rpow hx0] at h
    calc Real.log x = d * (a * Real.log x) := by dsimp [a]; field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left h hd.le
  have hbig' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le hlogz k)
    (Nat.cast_nonneg (α := ℝ) B)
  rw [mul_pow] at hbig'
  have hlarge : (B:ℝ)*(Real.log x)^k ≤ d^k*sieveConstant k*(2*x) := calc
    _ ≤ d^k*((B:ℝ)*(Real.log ((z:ℝ)+1))^k) := by linarith only [hbig']
    _ ≤ d^k*(sieveConstant k*N) := mul_le_mul_of_nonneg_left hbig (pow_nonneg hd.le _)
    _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hN₂ (mul_nonneg (pow_nonneg hd.le _) hs₀)
  have hzsqrt : (z:ℝ) ≤ Real.sqrt x := hz₁.trans (by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx.le ha')
  have hlogsqrt : (Real.log x)^k ≤ Real.sqrt x := by
    simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hl.le k),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] using hlog
  have hsqrt : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx.le
  have hsmall : ((z:ℝ)+1)*(Real.log x)^k ≤ 2*x := calc
    _ ≤ (2*Real.sqrt x)*Real.sqrt x := mul_le_mul (by linarith) hlogsqrt (pow_nonneg hl.le _) (by positivity)
    _ = _ := by nlinarith [Real.sq_sqrt hx0.le]
  have hsplit : (primePrefixSeedCount b k x : ℝ) ≤ ((z:ℝ)+1) + B := by exact_mod_cast prefix_split b k z x
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
    abs_of_nonneg (div_nonneg hx0.le (pow_nonneg hl.le _))]
  rw [← mul_div_assoc, le_div_iff₀ (pow_pos hl _)]
  nlinarith only [mul_le_mul_of_nonneg_right hsplit (pow_nonneg hl.le k), hsmall, hlarge]

private lemma prefix_partition (b : Bool) {k : ℕ} (hk : 0 < k) (x : ℝ) :
    primePrefixSeedCount b (k+1) x +
      exactChainCount (if b then IsFirstKindChainOfLength else IsSecondKindChainOfLength) k x =
        primePrefixSeedCount b k x := by
  classical
  let S := (range (⌊x⌋₊+1)).filter fun p => ∀ i < k, (chainTerm b p i).Prime
  have split := S.card_filter_add_card_filter_not (fun p => (chainTerm b p k).Prime)
  have hnext (p : ℕ) : (∀ i < k+1, (chainTerm b p i).Prime) ↔
      (∀ i < k, (chainTerm b p i).Prime) ∧ (chainTerm b p k).Prime := by
    constructor
    · intro h
      exact ⟨fun i hi => h i (by omega), h k (by omega)⟩
    · rintro ⟨h, hlast⟩ i hi
      rcases (by omega : i < k ∨ i = k) with hi' | rfl
      · exact h i hi'
      · exact hlast
  have he p : (if b then IsFirstKindChainOfLength else IsSecondKindChainOfLength) p k ↔
      (∀ i < k, (chainTerm b p i).Prime) ∧ ¬(chainTerm b p k).Prime := by
    cases b <;> simp [chainTerm, IsFirstKindChainOfLength, IsSecondKindChainOfLength, hk]
  change ((range _).filter fun p => ∀ i < k+1, (chainTerm b p i).Prime).card + _ = S.card
  simpa only [S, exactChainCount, filter_filter, hnext, he]
    using split

/-- The sieve bound applies to Jones's two exact-length predicates, including termination. -/
theorem exactChainCount_isBigO (b : Bool) {k : ℕ} (hk : 0 < k) :
    (fun x : ℝ => (exactChainCount
      (if b then IsFirstKindChainOfLength else IsSecondKindChainOfLength) k x : ℝ)) =O[atTop]
      (fun x : ℝ => x / (Real.log x)^k) := by
  refine (isBigO_of_le (g := fun x : ℝ => (primePrefixSeedCount b k x : ℝ)) atTop ?_).trans
    (primePrefixSeedCount_isBigO b hk)
  intro x
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  have h := prefix_partition b hk x
  exact_mod_cast (by omega : exactChainCount
    (if b then IsFirstKindChainOfLength else IsSecondKindChainOfLength) k x ≤ primePrefixSeedCount b k x)

private lemma next_scale_negligible {k : ℕ} {C : ℝ} (hC : 0 < C) :
    (fun x : ℝ => x/(Real.log x)^(k+1)) =o[atTop] (fun x => C*x/(Real.log x)^k) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx' : 0 < x := by linarith
    have hl := Real.log_pos hx
    exact fun h => False.elim ((by positivity : 0 < C*x/(Real.log x)^k).ne' h)
  · refine ((tendsto_const_nhds (x := 1/C)).div_atTop Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx' : x ≠ 0 := by linarith
    have hl := (Real.log_pos hx).ne'
    rw [pow_succ]
    field_simp

/-- At a single fixed length a positive leading asymptotic for prime prefixes is equivalent
to the same asymptotic for exact chains, without any hypothesis at the next length. -/
theorem primePrefixSeedCount_asymptotic_iff_exact (b : Bool) {k : ℕ} (hk : 0 < k)
    {C : ℝ} (hC : 0 < C) :
    ((fun x : ℝ => (primePrefixSeedCount b k x : ℝ)) ~[atTop] (fun x => C*x/(Real.log x)^k)) ↔
      ((fun x : ℝ => (exactChainCount
        (if b then IsFirstKindChainOfLength else IsSecondKindChainOfLength) k x : ℝ)) ~[atTop]
          (fun x => C*x/(Real.log x)^k)) := by
  have hnext := (primePrefixSeedCount_isBigO b (Nat.zero_lt_succ k)).trans_isLittleO (next_scale_negligible hC)
  have he (x : ℝ) : (primePrefixSeedCount b (k+1) x : ℝ) +
      exactChainCount (if b then IsFirstKindChainOfLength else IsSecondKindChainOfLength) k x =
      primePrefixSeedCount b k x := by exact_mod_cast prefix_partition b hk x
  constructor
  · intro h
    exact (h.sub_isLittleO hnext).congr_left (Eventually.of_forall fun x => by dsimp; linarith [he x])
  · intro h
    exact (hnext.add_isEquivalent h).congr_left (Eventually.of_forall he)

/-- Almost every prime starts an exact length-one chain of each kind, counted up to x. -/
theorem exactChainCount_one_asymptotic_primeCounting (b : Bool) :
    (fun x : ℝ => (exactChainCount
      (if b then IsFirstKindChainOfLength else IsSecondKindChainOfLength) 1 x : ℝ)) ~[atTop]
        (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) := by
  have hone (x : ℝ) : primePrefixSeedCount b 1 x = Nat.primeCounting ⌊x⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    cases b <;> simp [primePrefixSeedCount, Nat.primesLE, Nat.primesBelow, firstKindTerm, secondKindTerm]
  have hpi : (fun x : ℝ => 1*x/(Real.log x)^1) =O[atTop]
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) := by
    apply IsBigO.of_bound 4
    filter_upwards [eventually_ge_atTop (16 : ℝ),
      Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ) < 1/8)] with x hx hlog
    have hx' : 1 < x := by linarith
    have hl := Real.log_pos hx'
    have hsmall : Real.log x ≤ 1/8*x := by
      simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hl.le, abs_of_nonneg (by linarith : 0 ≤ x)] using hlog
    have h := (div_le_iff₀ hl).mp (Chebyshev.pi_ge' hx')
    have hl₂ : Real.log (x+2) ≤ Real.log 2 + Real.log x := by
      rw [← Real.log_mul (by norm_num) (by linarith : x ≠ 0)]
      exact Real.log_le_log (by linarith) (by linarith)
    have hc : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    simp only [one_mul, pow_one, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith : 0 ≤ x) hl.le),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
    rw [div_le_iff₀ hl]
    nlinarith only [mul_le_mul_of_nonneg_left hc (by linarith : 0 ≤ x-2), hl₂, h, hsmall, hx]
  have hs := ((primePrefixSeedCount_isBigO b (by decide : 0 < 1+1)).trans_isLittleO
    (next_scale_negligible (k := 1) (C := 1) (by norm_num))).trans_isBigO hpi
  have href := IsEquivalent.refl (u := fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) (l := atTop)
  refine (href.sub_isLittleO hs).congr_left ?_
  apply Eventually.of_forall
  intro x
  have h := prefix_partition b (by decide : 0 < 1) x
  rw [hone] at h
  dsimp
  apply sub_eq_iff_eq_add.mpr
  exact_mod_cast (h.symm.trans (Nat.add_comm _ _))

#print axioms primePrefixSeedCount_isBigO
#print axioms exactChainCount_isBigO
#print axioms primePrefixSeedCount_asymptotic_iff_exact
#print axioms exactChainCount_one_asymptotic_primeCounting

#print axioms sieve_sum_log_div_prime_le

end CunninghamChain
