import research.arxiv.«1104.1579».CunninghamSingularSeriesGrowth

/-! Prime-free segments of both Cunningham orbits and unrestricted prime ancestry. -/

namespace CunninghamChain.OrbitIsolation

open Finset Real

private noncomputable abbrev period (q : ℕ) := orderOf (2 : ZMod q)

private lemma period_pos {q : ℕ} (hp : q.Prime) (hq : 2 < q) : 0 < period q := by
  let : Fact q.Prime := ⟨hp⟩
  have hz : (2 : ZMod q) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq)
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨q-1, by omega, ZMod.pow_card_sub_one_eq_one hz⟩)

/-- The primes of exact order j are distinct factors of the single integer 2^j−1. -/
private lemma period_fiber_bound (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (j : ℕ) : (Q.filter fun q => period q = j).card ≤ j := by
  classical
  let S := Q.filter fun q => period q = j
  by_cases hj : j = 0
  · subst j
    have he : S = ∅ := eq_empty_iff_forall_notMem.mpr fun q hq => by
      obtain ⟨hqQ,hord⟩ := mem_filter.mp hq
      have := period_pos (hQ q hqQ).1 (hQ q hqQ).2
      omega
    change S.card ≤ 0
    simp [he]
  let M := 2^j-1
  have hM : 0 < M := Nat.sub_pos_of_lt (one_lt_pow₀ (by decide) hj)
  have hsub : S ⊆ M.primeFactors := by
    intro q hq
    obtain ⟨hqQ,heq⟩ := mem_filter.mp hq
    have he : 2^j ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff ..).mp (by
      push_cast
      rw [← heq]
      exact pow_orderOf_eq_one _)
    exact Nat.mem_primeFactors.mpr ⟨(hQ q hqQ).1,
      (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp he.symm,hM.ne'⟩
  have bound : 2^S.card ≤ 2^j := calc
    2^S.card = ∏ _q ∈ S, 2 := by simp
    _ ≤ ∏ q ∈ S, q := prod_le_prod' fun q hq => (Nat.prime_of_mem_primeFactors (hsub hq)).two_le
    _ ≤ ∏ q ∈ M.primeFactors, q := prod_le_prod_of_subset_of_one_le' hsub
      fun q hq _ => (Nat.prime_of_mem_primeFactors hq).one_le
    _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd _)
    _ ≤ 2^j := Nat.sub_le ..
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp bound

private lemma weight_regular {q j : ℕ} (hq : 0 < q) (hj : 0 < j) (h : q ≤ j^4) :
    (q:ℝ)^(-(7/8:ℝ)) / j ≤ (q:ℝ)^(-(9/8:ℝ)) := by
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hj' : (0:ℝ) < j := by exact_mod_cast hj
  have hx : (q:ℝ)^(1/4:ℝ) ≤ j := by
    calc (q:ℝ)^(1/4:ℝ) ≤ ((j:ℝ)^4)^(1/4:ℝ) :=
          Real.rpow_le_rpow hq'.le (by exact_mod_cast h) (by norm_num)
      _ = _ := by rw [← Real.rpow_natCast_mul hj'.le]; norm_num
  apply (div_le_iff₀ hj').mpr
  calc (q:ℝ)^(-(7/8:ℝ)) = (q:ℝ)^(-(9/8:ℝ)) * (q:ℝ)^(1/4:ℝ) := by
          rw [← Real.rpow_add hq']; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hq'.le _)

private lemma weight_exceptional {q j : ℕ} (hq : 1 ≤ q) (hj : 0 < j) (h : j^4 ≤ q) :
    (q:ℝ)^(-(7/8:ℝ)) ≤ (j:ℝ)^(-2:ℝ) := by
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hj' : (0:ℝ) < j := by exact_mod_cast hj
  calc (q:ℝ)^(-(7/8:ℝ)) ≤ (q:ℝ)^(-(1/2:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hq' (by norm_num)
    _ ≤ ((j:ℝ)^4)^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_nonpos (by positivity)
        (by exact_mod_cast h) (by norm_num)
    _ = _ := by rw [← Real.rpow_natCast_mul hj'.le]; norm_num

/-- A uniform majorant for the order-weighted prime sum in the averaged sieve loss. -/
theorem order_weight_bound : ∃ C : ℝ, ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ 2 < q) →
    (∑ q ∈ Q, (q:ℝ)^(-(7/8:ℝ)) / orderOf (2 : ZMod q)) ≤ C := by
  classical
  let f (q : ℕ) := (q:ℝ)^(-(7/8:ℝ)) / period q
  let u (n : ℕ) := (n:ℝ)^(-(9/8:ℝ))
  let v (n : ℕ) := (n:ℝ)^(-2:ℝ)
  have hu : Summable u := Real.summable_nat_rpow.mpr (by norm_num)
  have hv : Summable v := Real.summable_nat_rpow.mpr (by norm_num)
  refine ⟨(∑' n, u n) + ∑' j, v j, fun Q hQ => ?_⟩
  let R := Q.filter fun q => q ≤ (period q)^4
  let S := Q \ R
  have hsub : S ⊆ Q := sdiff_subset
  have hR : ∑ q ∈ R, f q ≤ ∑' n, u n := by
    refine (sum_le_sum fun q hq => ?_).trans (hu.sum_le_tsum R fun n _ =>
      Real.rpow_nonneg (Nat.cast_nonneg _) _)
    obtain ⟨hqQ,hr⟩ := mem_filter.mp hq
    have hp := hQ q hqQ
    exact weight_regular hp.1.pos (period_pos hp.1 hp.2) hr
  have hS : ∑ q ∈ S, f q ≤ ∑' j, v j := by
    let J := S.image period
    have maps : ∀ q ∈ S, period q ∈ J := fun q hq => mem_image_of_mem _ hq
    rw [← sum_fiberwise_of_maps_to maps f]
    refine (sum_le_sum fun j hj => ?_).trans (hv.sum_le_tsum J fun n _ =>
      Real.rpow_nonneg (Nat.cast_nonneg _) _)
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
    let j := period p
    have hpQ := hQ p (hsub hp)
    have hjpos : 0 < j := period_pos hpQ.1 hpQ.2
    have hj' : (0:ℝ) < j := by exact_mod_cast hjpos
    let T := S.filter fun q => period q = j
    change ∑ q ∈ T, f q ≤ v j
    have card := period_fiber_bound S (fun q hq => hQ q (hsub hq)) j
    have card' : (T.card:ℝ) ≤ j := by exact_mod_cast card
    have each (q : ℕ) (hq : q ∈ T) : f q ≤ v j / j := by
      obtain ⟨hqS,hj⟩ := mem_filter.mp hq
      obtain ⟨hqQ,hnR⟩ := mem_sdiff.mp hqS
      have hn : ¬q ≤ (period q)^4 := fun h => hnR (mem_filter.mpr ⟨hqQ,h⟩)
      unfold f
      rw [hj] at hn ⊢
      exact div_le_div_of_nonneg_right (weight_exceptional (hQ q hqQ).1.one_le hjpos
        (le_of_lt (lt_of_not_ge hn))) hj'.le
    calc ∑ q ∈ T, f q ≤ ∑ _q ∈ T, v j / j := sum_le_sum each
      _ = (T.card:ℝ) * (v j / j) := by simp
      _ ≤ (j:ℝ) * (v j / j) := mul_le_mul_of_nonneg_right card' (div_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) hj'.le)
      _ = v j := by field_simp
  change ∑ q ∈ Q, f q ≤ _
  rw [← sum_sdiff (filter_subset (fun q => q ≤ (period q)^4) Q) (f := f)]
  linarith only [hS,hR]

/-- Count collisions by the multiples of each period among the positive offsets. -/
lemma average_collisions (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q) (H : ℕ) :
    (∑ i ∈ range H, ∑ q ∈ Q.filter (fun q => period q ∣ i+1), (q:ℝ)^(-(7/8:ℝ))) ≤
      (H:ℝ) * ∑ q ∈ Q, (q:ℝ)^(-(7/8:ℝ)) / period q := by
  classical
  simp_rw [sum_filter]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro q hq
  let d := period q
  let w := (q:ℝ)^(-(7/8:ℝ))
  have hd := period_pos (hQ q hq).1 (hQ q hq).2
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  change (∑ i ∈ range H, if d ∣ i+1 then w else 0) ≤ H * (w / d)
  rw [← sum_filter, sum_const, Nat.card_multiples, nsmul_eq_mul]
  have hcount : ((H / d : ℕ):ℝ) ≤ (H:ℝ) / d :=
    (le_div_iff₀ hd').mpr (by exact_mod_cast Nat.div_mul_le_self H d)
  calc ((H / d : ℕ):ℝ) * w ≤ ((H:ℝ) / d) * w :=
        mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by ring

private noncomputable abbrev loss (q : ℕ) : ℝ := ((1 - 1/(q:ℝ))⁻¹)^2

private lemma loss_one_le {q : ℕ} (hp : q.Prime) : 1 ≤ loss q := by
  have hq : (1:ℝ) < q := by exact_mod_cast hp.one_lt
  have h : 0 < 1 - 1/(q:ℝ) := by rw [sub_pos,one_div]; exact inv_lt_one_of_one_lt₀ hq
  have h₁ : 1 ≤ (1 - 1/(q:ℝ))⁻¹ := (one_le_inv₀ h).mpr (by linarith [one_div_nonneg.mpr (Nat.cast_nonneg (α := ℝ) q)])
  exact one_le_pow₀ h₁

private lemma loss_sub_one_bound {q : ℕ} (hp : q.Prime) : loss q - 1 ≤ 8/(q:ℝ) := by
  have hq : (2:ℝ) ≤ q := by exact_mod_cast hp.two_le
  have hpos : 0 < (q:ℝ)-1 := by linarith
  have he : (1 - 1/(q:ℝ))⁻¹ = q/((q:ℝ)-1) := by
    have h : 1 - 1/(q:ℝ) = ((q:ℝ)-1)/q := by field_simp
    rw [h, inv_div]
  rw [loss,he,div_pow]
  field_simp
  nlinarith [mul_nonneg (show 0 ≤ (q:ℝ)-2 by linarith) (show 0 ≤ 6*(q:ℝ)-3 by linarith)]

private lemma euler_power_bound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 1 ≤ p →
    ∏ q ∈ p.primesLE, loss q ≤ C*(p:ℝ)^(1/8:ℝ) := by
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp CunninghamChain.prime_euler_product_log_bounds
  let B := ∏ q ∈ K.primesLE, loss q
  let A := (32*Real.exp 4)^2
  have hB : 0 ≤ B := prod_nonneg fun q hq => (loss_one_le (Nat.prime_of_mem_primesLE hq)).trans' zero_le_one
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A+B, by linarith, fun p hp => ?_⟩
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hpow := Real.one_le_rpow hp' (by norm_num : (0:ℝ) ≤ 1/8)
  by_cases h : K ≤ p
  · have hlog := Real.log_le_rpow_div (Nat.cast_nonneg (α := ℝ) p) (by norm_num : (0:ℝ) < 1/16)
    have h₁ : (∏ q ∈ p.primesLE, (1-1/(q:ℝ))⁻¹) ≤ 32 * exp 4 * (p:ℝ)^(1/16:ℝ) :=
      ((hK p h).2.trans (mul_le_mul_of_nonneg_left hlog (by positivity))).trans_eq (by ring)
    have hnon : 0 ≤ ∏ q ∈ p.primesLE, (1-1/(q:ℝ))⁻¹ := by
      refine prod_nonneg fun q hq => inv_nonneg.mpr (sub_nonneg.mpr ?_)
      rw [one_div]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.prime_of_mem_primesLE hq).one_le)
    simp only [loss,prod_pow]
    calc _ ≤ (32*exp 4*(p:ℝ)^(1/16:ℝ))^2 := pow_le_pow_left₀ hnon h₁ _
      _ = A*(p:ℝ)^(1/8:ℝ) := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg (α := ℝ) p)]
        norm_num [A]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hsub : p.primesLE ⊆ K.primesLE := fun q hq => Nat.mem_primesLE.mpr
        ⟨(Nat.le_of_mem_primesLE hq).trans (by omega),Nat.prime_of_mem_primesLE hq⟩
    have h₁ : (∏ q ∈ p.primesLE, loss q) ≤ B := prod_le_prod_of_subset_of_one_le hsub
      (fun _ hq => (loss_one_le (Nat.prime_of_mem_primesLE hq)).trans' zero_le_one)
      (fun _ hq _ => loss_one_le (Nat.prime_of_mem_primesLE hq))
    exact h₁.trans <| (show B ≤ A+B by linarith).trans (le_mul_of_one_le_right (by linarith) hpow)

/-- Insert the largest prime last so its incremental cost sees only smaller primes. -/
lemma product_loss_bound : ∃ C : ℝ, 0 < C ∧ ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    (∏ q ∈ S, loss q) ≤ 1 + C * ∑ q ∈ S, (q:ℝ)^(-(7/8:ℝ)) := by
  obtain ⟨A,hA,ha⟩ := euler_power_bound
  refine ⟨8*A, by positivity, fun S => ?_⟩
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert p S hlt ih =>
    intro hpr
    have hp := hpr p (mem_insert_self ..)
    have hp₀ : 0 < (p:ℝ) := by exact_mod_cast hp.pos
    have hpS : p ∉ S := fun h => (hlt _ h).false
    have hS : ∀ q ∈ S, q.Prime := fun q hq => hpr q (mem_insert_of_mem hq)
    have sub : S ⊆ p.primesLE := fun q hq => Nat.mem_primesLE.mpr ⟨(hlt q hq).le,hS q hq⟩
    have hprod := (prod_le_prod_of_subset_of_one_le sub
      (fun q hq => (loss_one_le (hS q hq)).trans' zero_le_one)
      (fun q hq _ => loss_one_le (Nat.prime_of_mem_primesLE hq))).trans (ha p hp.one_le)
    have step := mul_le_mul (loss_sub_one_bound hp) hprod
      (prod_nonneg fun q hq => (loss_one_le (hS q hq)).trans' zero_le_one) (by positivity)
    have he : 8/(p:ℝ) * (A*(p:ℝ)^(1/8:ℝ)) = 8*A*(p:ℝ)^(-(7/8:ℝ)) := by
      rw [show -(7/8:ℝ) = 1/8 - 1 by norm_num, Real.rpow_sub hp₀, Real.rpow_one]; ring
    rw [he] at step
    rw [prod_insert hpS,sum_insert hpS]
    linarith only [step,ih hS]

/-- The square of the Euler factor lost at colliding residues has bounded average,
uniformly in the sieving primes and in the number of positive offsets. -/
theorem mean_collision_loss : ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset ℕ) (H : ℕ),
    (∀ q ∈ Q, q.Prime ∧ 2 < q) →
    (∑ i ∈ range H, ∏ q ∈ Q.filter (fun q => orderOf (2 : ZMod q) ∣ i+1),
      ((1 - 1/(q:ℝ))⁻¹)^2) ≤ C*H := by
  obtain ⟨A,hA,hprod⟩ := product_loss_bound
  obtain ⟨B,hB⟩ := order_weight_bound
  have hB₀ : 0 ≤ B := by simpa using hB ∅ (by simp)
  refine ⟨1+A*B, by positivity, fun Q H hQ => ?_⟩
  let S (i : ℕ) := Q.filter fun q => period q ∣ i+1
  have hstep (i : ℕ) (_hi : i ∈ range H) := hprod (S i) fun q hq => (hQ q (mem_filter.mp hq).1).1
  have h := sum_le_sum hstep
  rw [sum_add_distrib, ← mul_sum] at h
  simp only [sum_const,card_range,nsmul_eq_mul,mul_one] at h
  have hs := (average_collisions Q hQ H).trans (mul_le_mul_of_nonneg_left (hB Q hQ) (Nat.cast_nonneg _))
  change (∑ i ∈ range H, ∏ q ∈ S i, loss q) ≤ _
  change (∑ i ∈ range H, ∑ q ∈ S i, _) ≤ _ at hs
  linarith only [h,mul_le_mul_of_nonneg_left hs hA.le]

#print axioms mean_collision_loss

private abbrev term (b : Bool) := if b then firstKindTerm else secondKindTerm

private lemma term_zero (b : Bool) (p : ℕ) : term b p 0 = p := by cases b <;> rfl

private def pairSeeds (b : Bool) (j N : ℕ) : Finset ℕ :=
  (range N).filter fun p => p.Prime ∧ (term b p j).Prime

private def largeSeeds (b : Bool) (j N z : ℕ) : Finset ℕ :=
  (pairSeeds b j N).filter (z < ·)

private lemma two_indices {j q : ℕ} (hj : 0 < j) (hn : ¬period q ∣ j) :
    Set.InjOn (fun i : ℕ => (2 : ZMod q)^i) ({0,j} : Finset ℕ) := by
  have hne : (2 : ZMod q)^j ≠ 1 := fun h => hn (orderOf_dvd_of_pow_eq_one h)
  intro a ha b hb he
  simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

private lemma offset_sieve (b : Bool) (j : ℕ) (hj : 0 < j) {N z : ℕ} (hz : 4 ≤ z)
    (hy : (z^8)^4 ≤ N) :
    ((largeSeeds b j N z).card:ℝ) * (log ((z:ℝ)+1))^2 ≤
      6 * (∏ q ∈ (4:ℕ).primesLE, loss q) *
      (∏ q ∈ (z.primesLE \ (4:ℕ).primesLE).filter (fun q => period q ∣ j), loss q) * N := by
  classical
  let P := (4:ℕ).primesLE
  let Q := z.primesLE \ P
  let D := Q.filter fun q => period q ∣ j
  let E := P ∪ D
  let I : Finset ℕ := {0,j}
  have hi : I.card = 2 := by simp [I,Ne.symm hj.ne']
  have hP : P ⊆ z.primesLE := fun q hq => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE hq).trans hz, Nat.prime_of_mem_primesLE hq⟩
  have hE : E ⊆ z.primesLE := union_subset hP (subset_trans (filter_subset ..) sdiff_subset)
  have hreg (q : ℕ) (hq : q ∈ z.primesLE \ E) : 2*2 < q ∧
      Set.InjOn (fun i : ℕ => (2 : ZMod q)^i) I := by
    obtain ⟨hqp,hn⟩ := mem_sdiff.mp hq
    have hnp : q ∉ P := fun h => hn (mem_union_left _ h)
    have hq₄ : 4 < q := by
      by_contra! h
      exact hnp (Nat.mem_primesLE.mpr ⟨h,Nat.prime_of_mem_primesLE hqp⟩)
    refine ⟨hq₄,two_indices hj (fun h => hn (mem_union_right _ ?_))⟩
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hqp,hnp⟩,h⟩
  have h := finite_iterate_sieve_bound b I E hi (by decide) (by omega) hE hreg hy
  have hseeds : ((range N).filter fun p => z < p ∧ ∀ i ∈ I, (term b p i).Prime) =
      largeSeeds b j N z := by
    ext p
    simp only [largeSeeds,pairSeeds,mem_filter,mem_range,I,mem_insert,mem_singleton]
    simp [term_zero,and_comm,and_left_comm]
  have hdis : Disjoint P D := disjoint_left.mpr fun q hp hd => (mem_sdiff.mp (mem_filter.mp hd).1).2 hp
  change ((largeSeeds b j N z).card:ℝ) * _ ≤ 6*(∏ q ∈ P, loss q)*(∏ q ∈ D, loss q)*N
  change (((range N).filter fun p => z < p ∧ ∀ i ∈ I, (term b p i).Prime).card:ℝ) * _ ≤ _ at h
  rw [hseeds, ← prod_pow] at h
  change _ ≤ 6*(∏ q ∈ P ∪ D, loss q)*N at h
  simpa only [prod_union hdis,mul_assoc] using h

private lemma all_offset_counts : ∃ C : ℝ, 0 < C ∧ ∀ (b : Bool) (N z H : ℕ), 4 ≤ z →
    (z^8)^4 ≤ N →
    (∑ i ∈ range H, ((pairSeeds b (i+1) N).card:ℝ))*(log ((z:ℝ)+1))^2 ≤
      (H:ℝ)*((z+1)*(log ((z:ℝ)+1))^2 + C*N) := by
  classical
  obtain ⟨A,hA,ha⟩ := mean_collision_loss
  let D := 6*(∏ q ∈ (4:ℕ).primesLE, loss q)
  have hD : 0 < D := mul_pos (by norm_num) (prod_pos fun q hq =>
    lt_of_lt_of_le zero_lt_one (loss_one_le (Nat.prime_of_mem_primesLE hq)))
  refine ⟨D*A, mul_pos hD hA, fun b N z H hz hy => ?_⟩
  let Q := z.primesLE \ (4:ℕ).primesLE
  let F (i : ℕ) := ∏ q ∈ Q.filter (fun q => period q ∣ i+1), loss q
  let L := (log ((z:ℝ)+1))^2
  have hQ (q : ℕ) (hq : q ∈ Q) : q.Prime ∧ 2 < q := by
    obtain ⟨hqp,hn⟩ := mem_sdiff.mp hq
    have hp := Nat.prime_of_mem_primesLE hqp
    exact ⟨hp,by by_contra! h; exact hn (Nat.mem_primesLE.mpr ⟨by omega,hp⟩)⟩
  have hF : ∑ i ∈ range H, F i ≤ A*H := ha Q H hQ
  have hsum (i : ℕ) (_hi : i ∈ range H) :
      ((pairSeeds b (i+1) N).card:ℝ)*L ≤ ((z:ℝ)+1)*L + D*N*F i := by
    let P := pairSeeds b (i+1) N
    have hs : P ⊆ range (z+1) ∪ largeSeeds b (i+1) N z := by
      intro p hp
      exact mem_union.mpr ((le_or_gt p z).imp (fun h => mem_range.mpr (by omega))
        (fun h => mem_filter.mpr ⟨hp,h⟩))
    have hc := (card_le_card hs).trans (card_union_le ..)
    simp only [card_range] at hc
    have hc' : (P.card:ℝ) ≤ ((z:ℝ)+1) + (largeSeeds b (i+1) N z).card := by exact_mod_cast hc
    have hw : ((largeSeeds b (i+1) N z).card:ℝ)*L ≤ D*F i*N := offset_sieve b _ (by omega) hz hy
    change (P.card:ℝ)*L ≤ _
    linarith only [mul_le_mul_of_nonneg_right hc' (show 0 ≤ L from sq_nonneg _),hw]
  have hs := sum_le_sum hsum
  rw [← sum_mul,sum_add_distrib,sum_const,card_range,nsmul_eq_mul,← mul_sum] at hs
  change _ * L ≤ (H:ℝ)*(((z:ℝ)+1)*L+D*A*N)
  linarith only [hs,mul_le_mul_of_nonneg_left hF (show 0 ≤ D*N by positivity)]

open Filter
open scoped Topology

/-- An edge joins a smaller prime seed to a prime positive iterate. The
intervening terms may be composite. The two orientations allow either endpoint
to be the prime under study. -/
def HasPrimeNeighbor (p H : ℕ) : Prop :=
  ∃ (b : Bool) (j : ℕ), 0 < j ∧ j ≤ H ∧
    (((if b then firstKindTerm else secondKindTerm) p j).Prime ∨
     ∃ r : ℕ, r.Prime ∧ (if b then firstKindTerm else secondKindTerm) r j = p)

noncomputable def exceptionalPrimes (N H : ℕ) : Finset ℕ := by
  classical exact N.primesLE.filter fun p => HasPrimeNeighbor p H

private lemma term_ge (b : Bool) {p : ℕ} (_hp : 0 < p) (j : ℕ) : p ≤ term b p j := by
  cases b <;> induction j with
  | zero => rfl
  | succ j ih =>
    first
    | change p ≤ 2 * secondKindTerm p j - 1
      change p ≤ secondKindTerm p j at ih
      omega
    | change p ≤ 2 * firstKindTerm p j + 1
      change p ≤ firstKindTerm p j at ih
      omega

private lemma exceptional_count (N H : ℕ) :
    (exceptionalPrimes N H).card ≤ 2 * ∑ i ∈ range H,
      ((pairSeeds true (i+1) (N+1)).card + (pairSeeds false (i+1) (N+1)).card) := by
  classical
  let P (b : Bool) (i : ℕ) := pairSeeds b (i+1) (N+1)
  let E (b : Bool) (i : ℕ) := P b i ∪ (P b i).image (fun r => term b r (i+1))
  have incl : exceptionalPrimes N H ⊆ (range H).biUnion (fun i => E true i ∪ E false i) := by
    intro p hp
    obtain ⟨hpN, b, j, hj, hjH, hor⟩ := mem_filter.mp hp
    have ⟨hpN,hppr⟩ := Nat.mem_primesLE.mp hpN
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have he : p ∈ E b i := by
      rcases hor with hf | ⟨r,hr,he⟩
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr (by omega),hppr,hf⟩)
      · have her : term b r (i+1) = p := he
        have hrN := (term_ge b hr.pos (i+1)).trans (her ▸ hpN)
        exact mem_union_right _ (mem_image.mpr ⟨r,mem_filter.mpr
          ⟨mem_range.mpr (by omega),hr,her ▸ hppr⟩,her⟩)
    exact mem_biUnion.mpr ⟨i,mem_range.mpr (by omega),by cases b <;> simp_all [mem_union]⟩
  have hE (b : Bool) (i : ℕ) : (E b i).card ≤ 2*(P b i).card :=
    (card_union_le ..).trans (by have := card_image_le (s := P b i) (f := fun r => term b r (i+1)); omega)
  refine (card_le_card incl).trans (card_biUnion_le.trans ?_)
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  exact (card_union_le ..).trans (by have := hE true i; have := hE false i; dsimp [P] at *; omega)

/-- A uniform choice of the dimension-two sieve cutoff and both error controls. -/
theorem pair_sieve_cutoff : ∀ᶠ N : ℕ in atTop, ∃ z : ℕ, 4≤z ∧ (z^8)^4≤N ∧
    log (N:ℝ)≤32*log ((z:ℝ)+1) ∧ ((z:ℝ)+1)*(log ((z:ℝ)+1))^2≤2*N := by
  have hcut := (tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/32)).comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 4
  filter_upwards [hcut,eventually_ge_atTop 2] with N hz hN
  let z := ⌊(N:ℝ)^(1/32:ℝ)⌋₊
  change 4 ≤ z at hz
  have hN' : (1:ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hz' : (1:ℝ) ≤ z := by exact_mod_cast (by omega : 1 ≤ z)
  have hN₀ := zero_lt_one.trans hN'
  have hv : ((N:ℝ)^(1/32:ℝ))^32 = N := by
    rw [← Real.rpow_mul_natCast hN₀.le]; norm_num
  have hpow : (z:ℝ)^32 ≤ N := (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le
    (Real.rpow_nonneg hN₀.le _)) 32).trans_eq hv
  have hnat : (z^8)^4 ≤ N := by
    rw [←pow_mul]
    exact_mod_cast hpow
  let L := log ((z:ℝ)+1)
  have hL : 0 ≤ L := log_nonneg (by linarith)
  have hlog : log (N:ℝ) ≤ 32*L := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hN₀ _) (Nat.lt_floor_add_one ((N:ℝ)^(1/32:ℝ))).le
    rw [Real.log_rpow hN₀] at hh
    dsimp [L,z]; linarith
  have hsmall : ((z:ℝ)+1)*L^2 ≤ 2*N := by
    have hlz : L ≤ z := by dsimp [L]; linarith [Real.log_le_sub_one_of_pos (show 0 < (z:ℝ)+1 by positivity)]
    have h3 : (z:ℝ)^3 ≤ (z:ℝ)^32 := pow_le_pow_right₀ hz' (by decide)
    calc ((z:ℝ)+1)*L^2 ≤ (2*(z:ℝ))*(z:ℝ)^2 :=
          mul_le_mul (by linarith) (pow_le_pow_left₀ hL hlz _) (sq_nonneg _) (by positivity)
      _ = 2*(z:ℝ)^3 := by ring
      _ ≤ 2*N := by linarith
  exact ⟨z,hz,hnat,hlog,hsmall⟩

private lemma pair_count_scale : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ (b : Bool) (H : ℕ),
    (∑ i ∈ range H, ((pairSeeds b (i+1) (N+1)).card:ℝ))*(log (N:ℝ))^2 ≤ C*H*N := by
  obtain ⟨A,hA,ha⟩ := all_offset_counts
  refine ⟨(32:ℝ)^2 * (2+2*A),by positivity,?_⟩
  filter_upwards [pair_sieve_cutoff,eventually_ge_atTop 2] with N data hN
  intro b H
  obtain ⟨z,hz,hnat,hlog,hsmall⟩ := data
  have h := ha b (N+1) z H hz (hnat.trans (Nat.le_succ _))
  let S := ∑ i ∈ range H, ((pairSeeds b (i+1) (N+1)).card:ℝ)
  let L := log ((z:ℝ)+1)
  have hN' : (1:ℝ) < N := by exact_mod_cast (by omega : 1<N)
  have hL : 0≤L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) z])
  change S*L^2 ≤ (H:ℝ)*(((z:ℝ)+1)*L^2 + A*((N+1:ℕ):ℝ)) at h
  push_cast at h
  have hSN : S*L^2 ≤ (H:ℝ)*((2+2*A)*N) := h.trans (mul_le_mul_of_nonneg_left (by
    nlinarith only [hsmall,mul_nonneg hA.le (sub_nonneg.mpr hN'.le)]) (Nat.cast_nonneg _))
  have hS : 0 ≤ S := sum_nonneg fun _ _ => Nat.cast_nonneg _
  change S*(log (N:ℝ))^2 ≤ _
  calc _ ≤ S*(32*L)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (log_nonneg hN'.le) hlog _) hS
    _ = 32^2*(S*L^2) := by ring
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hSN (show 0 ≤ (32:ℝ)^2 by positivity)]

/-- For either recurrence and either direction together, the number of
exceptional primes up to N is at most an absolute constant times H N / log² N. -/
theorem exceptional_primes_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ H : ℕ,
    ((exceptionalPrimes N H).card:ℝ)*(log (N:ℝ))^2 ≤ C*H*N := by
  obtain ⟨A,hA,ha⟩ := pair_count_scale
  refine ⟨4*A,by positivity,?_⟩
  filter_upwards [ha] with N hN
  intro H
  have hc : ((exceptionalPrimes N H).card:ℝ) ≤ 2*∑ i ∈ range H,
      (((pairSeeds true (i+1) (N+1)).card:ℝ) + ((pairSeeds false (i+1) (N+1)).card:ℝ)) := by
    exact_mod_cast exceptional_count N H
  rw [sum_add_distrib] at hc
  nlinarith only [mul_le_mul_of_nonneg_right hc (sq_nonneg (log (N:ℝ))),hN true H,hN false H]

#print axioms exceptional_primes_bound

private lemma chebyshev_lower : ∀ᶠ N : ℕ in atTop, 0 < log (N:ℝ) ∧
    0 < (N.primeCounting:ℝ) ∧ (N:ℝ) ≤ 4*(N.primeCounting:ℝ)*log N := by
  have hl := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ) < 1/8))
  filter_upwards [hl,eventually_ge_atTop 16] with N hlog hsize
  have hN' : (16:ℝ) ≤ N := by exact_mod_cast hsize
  have hp : 0 < (N:ℝ) := by linarith
  have hL : 0 < log (N:ℝ) := log_pos (by linarith)
  have hsmall : log (N:ℝ) ≤ 1/8*(N:ℝ) := by
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hL.le, abs_of_nonneg hp.le] using hlog
  have hlog₂ : log ((N:ℝ)+1) ≤ log 2 + log N := by
    rw [← Real.log_mul (by norm_num) hp.ne']
    exact log_le_log (by positivity) (by linarith)
  have hπ := (div_le_iff₀ hL).mp (Chebyshev.pi_ge N)
  have hπ' : (N:ℝ) ≤ 4*(N.primeCounting:ℝ)*log N := by
    have : (1:ℝ)/2 ≤ log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith only [hπ,hlog₂,hsmall,hN',mul_le_mul_of_nonneg_right this
      (show 0 ≤ (N:ℝ)-1 by linarith)]
  have hπ₀ : 0 < (N.primeCounting:ℝ) := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h hL.le]
  exact ⟨hL,hπ₀,hπ'⟩

/-- Divide the uniform pair count by the number of primes. The constant
is independent of the search radius. -/
theorem exceptional_prime_proportion : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ H : ℕ,
    ((exceptionalPrimes N H).card:ℝ) / N.primeCounting ≤ C*((H:ℝ)/log N) := by
  obtain ⟨A,hA,ha⟩ := exceptional_primes_bound
  refine ⟨4*A,by positivity,?_⟩
  filter_upwards [ha,chebyshev_lower] with N hN hc
  intro H
  obtain ⟨hL,hπ₀,hπ'⟩ := hc
  have hmul := (hN H).trans (mul_le_mul_of_nonneg_left hπ' (by positivity))
  have hcancel : ((exceptionalPrimes N H).card:ℝ)*log N ≤ 4*A*H*N.primeCounting := by
    apply le_of_mul_le_mul_right (a := log (N:ℝ)) _ hL
    linarith only [hmul]
  rw [div_le_iff₀ hπ₀]
  field_simp
  linarith only [hcancel]

private lemma max_radius {H : ℕ → ℕ} (h : Tendsto (fun n => (H n:ℝ)/log n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (((range (N+1)).sup H : ℕ):ℝ)/log N) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := eventually_atTop.mp (h.eventually_lt_const hε)
  let B := (range (max K 2+1)).sup H
  have hB := (tendsto_const_nhds (x := (B:ℝ))).div_atTop
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [eventually_ge_atTop 2,hB.eventually_lt_const hε] with N hN hsmall
  have hLN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hLN.le)]
  obtain ⟨j,hj,he⟩ := exists_mem_eq_sup (range (N+1)) (by simp) H
  rw [he]
  by_cases hjK : j ≤ max K 2
  · have : H j ≤ B := le_sup (f := H) (mem_range.mpr (by omega))
    exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr this) hLN.le).trans_lt hsmall
  · have hLj : 0 < log (j:ℝ) := log_pos (by exact_mod_cast (by omega : 1 < j))
    have hjN := mem_range.mp hj
    have hle : log (j:ℝ) ≤ log N := log_le_log (by exact_mod_cast (by omega : 0 < j)) (by exact_mod_cast (by omega : j ≤ N))
    exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hLj hle).trans_lt (hK j (by omega))

/-- For each sublogarithmic radius, almost every prime has no other prime
within that many forward or backward steps in either of Jones's recurrences. -/
theorem prime_orbit_isolation {H : ℕ → ℕ} (h : Tendsto (fun n => (H n:ℝ)/log n) atTop (𝓝 0)) :
    letI := Classical.propDecidable
    Tendsto (fun N : ℕ => (((N.primesLE.filter fun p => HasPrimeNeighbor p (H p)).card:ℝ) /
      N.primeCounting)) atTop (𝓝 0) := by
  classical
  obtain ⟨C,_,hC⟩ := exceptional_prime_proportion
  let M (N : ℕ) := (range (N+1)).sup H
  have hm : Tendsto (fun N => C*((M N:ℝ)/log N)) atTop (𝓝 0) := by simpa using (max_radius h).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hm
  filter_upwards [hC] with N hN
  refine le_trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) (hN (M N))
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hpN,b,j,hj,hH,ht⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpN,b,j,hj,hH.trans (le_sup (f := H)
    (mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primesLE hpN)))),ht⟩

#print axioms exceptional_prime_proportion
#print axioms prime_orbit_isolation

/-- The prime r generates p after at least one step. Intervening values are unrestricted. -/
def HasPrimeAncestor (p : ℕ) : Prop := ∃ (b : Bool) (r j : ℕ), r.Prime ∧
  0 < j ∧ (if b then firstKindTerm else secondKindTerm) r j = p

noncomputable def primesWithAncestor (N : ℕ) : Finset ℕ := by
  classical exact N.primesLE.filter HasPrimeAncestor

private lemma term_doubles (b : Bool) {r : ℕ} (hr : 2 ≤ r) (j : ℕ) :
    2^j*(r-1)+1 ≤ term b r j := by
  induction j with
  | zero => simp only [pow_zero,one_mul,term_zero]; omega
  | succ j ih =>
    cases b
    · change _ ≤ 2*secondKindTerm r j - 1
      change _ ≤ secondKindTerm r j at ih
      rw [pow_succ,show 2^j*2*(r-1) = 2*(2^j*(r-1)) by ring]
      omega
    · change _ ≤ 2*firstKindTerm r j + 1
      change _ ≤ firstKindTerm r j at ih
      rw [pow_succ]; nlinarith only [ih]

private lemma ancestor_count (N K : ℕ) (hK : ∀ j : ℕ, 2^j ≤ N → j ≤ K) :
    (primesWithAncestor N).card ≤ ∑ i ∈ range K,
      ((pairSeeds true (i+1) (N/2^i+K+1)).card + (pairSeeds false (i+1) (N/2^i+K+1)).card) := by
  classical
  let E (b : Bool) (i : ℕ) := (pairSeeds b (i+1) (N/2^i+K+1)).image fun r => term b r (i+1)
  have sub : primesWithAncestor N ⊆ (range K).biUnion fun i => E true i ∪ E false i := by
    intro p hp
    obtain ⟨hpp,b,r,j,hr,hj,he⟩ := mem_filter.mp hp
    obtain ⟨hpN,hppr⟩ := Nat.mem_primesLE.mp hpp
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hterm : term b r (i+1) = p := he
    have hg := (term_doubles b hr.two_le (i+1)).trans (hterm ▸ hpN)
    have hpow : 2^(i+1) ≤ N := by
      have h1 : 1 ≤ r-1 := by have := hr.two_le; omega
      nlinarith only [hg,Nat.mul_le_mul_left (2^(i+1)) h1]
    have hcard := hK (i+1) hpow
    have hrN : r ≤ N/2^i := by
      apply (Nat.le_div_iff_mul_le (by positivity)).mpr
      have hlow : r ≤ 2*(r-1) := by have := hr.two_le; omega
      rw [pow_succ] at hg
      nlinarith only [Nat.mul_le_mul_right (2^i) hlow,hg]
    have hE : p ∈ E b i := mem_image.mpr ⟨r,mem_filter.mpr
      ⟨mem_range.mpr (by omega),hr,hterm ▸ hppr⟩,hterm⟩
    exact mem_biUnion.mpr ⟨i,mem_range.mpr (by omega),by cases b <;> simp_all [mem_union]⟩
  refine (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum fun i _ => ?_))
  exact (card_union_le ..).trans (Nat.add_le_add card_image_le card_image_le)

private lemma weighted_geometric (K : ℕ) :
    ∑ i ∈ range K, ((i:ℝ)+1)/(2:ℝ)^i ≤ 4 := by
  have he : (∑ i ∈ range K, ((i:ℝ)+1)/(2:ℝ)^i) = 4-(2*K+4)/(2:ℝ)^K := by
    induction K with
    | zero => norm_num
    | succ K ih => rw [sum_range_succ,ih,pow_succ]; push_cast; ring
  rw [he]; linarith [show 0 ≤ (2*(K:ℝ)+4)/2^K by positivity]

private lemma ancestor_scales : ∀ᶠ N : ℕ in atTop,
    let K := ⌊(N:ℝ)^(1/4:ℝ)⌋₊+1
    (∀ j : ℕ, 2^j ≤ N → j ≤ K) ∧ log (N:ℝ) ≤ 4*log K ∧ (K:ℝ)^3 ≤ 8*N := by
  let k (N : ℕ) := ⌊(N:ℝ)^(1/4:ℝ)⌋₊+1
  have ht : Tendsto k atTop atTop := tendsto_add_atTop_nat 1 |>.comp
    (tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop))
  have hlog := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp ht).eventually
    (Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ)<1/8))
  filter_upwards [eventually_ge_atTop 2,ht.eventually_ge_atTop 2,hlog] with N hN hk hl
  let K := k N
  have hn' : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hk' : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ k N by omega)
  have hn₀ : 0 < (N:ℝ) := by linarith
  have hroot : (N:ℝ)^(1/4:ℝ) ≤ K := by
    dsimp [K,k]; push_cast; exact (Nat.lt_floor_add_one _).le
  have hlo := log_le_log (rpow_pos_of_pos hn₀ _) hroot
  rw [log_rpow hn₀] at hlo
  change ‖log (K:ℝ)‖ ≤ 1/8*‖(K:ℝ)‖ at hl
  have hl' : log (K:ℝ) ≤ (1/8)*(K:ℝ) := by
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hk'), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) K)] using hl
  refine ⟨?_,by change log (N:ℝ) ≤ 4*log (K:ℝ); linarith,?_⟩
  · intro j hj
    have hx : (2:ℝ)^j ≤ N := by exact_mod_cast hj
    have h := log_le_log (show 0 < (2:ℝ)^j by positivity) hx
    rw [log_pow] at h
    have h₂ : (1:ℝ)/2 ≤ log 2 := by linarith [log_two_gt_d9]
    change j ≤ K
    exact_mod_cast (show (j:ℝ) ≤ K by nlinarith only [h,hlo,hl',mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α:=ℝ) j)])
  · have hr : 1 ≤ (N:ℝ)^(1/4:ℝ) := one_le_rpow hn' (by norm_num)
    have hu : (K:ℝ) ≤ 2*(N:ℝ)^(1/4:ℝ) := by
      dsimp [K,k]; push_cast
      linarith [Nat.floor_le (rpow_nonneg hn₀.le (1/4:ℝ))]
    change (K:ℝ)^3 ≤ 8*N
    calc _ ≤ (2*(N:ℝ)^(1/4:ℝ))^3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hu _
      _ = 8*(N:ℝ)^(3/4:ℝ) := by rw [mul_pow,← rpow_mul_natCast hn₀.le]; norm_num
      _ ≤ 8*(N:ℝ)^1 := by gcongr; exact_mod_cast Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (3/4:ℝ) ≤ 1)
      _ = _ := by ring

/-- Prime ancestors are rare even when their distance from the endpoint is
unrestricted. An offset of i+1 forces an initial prime at most N/2^i. -/
theorem unbounded_ancestor_count : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    ((primesWithAncestor N).card:ℝ)*(log (N:ℝ))^2 ≤ C*N := by
  obtain ⟨A,hA,ha⟩ := pair_count_scale
  obtain ⟨T,hT⟩ := eventually_atTop.mp ha
  let k (N : ℕ) := ⌊(N:ℝ)^(1/4:ℝ)⌋₊+1
  have ht : Tendsto k atTop atTop := (tendsto_add_atTop_nat 1).comp
    (tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop))
  refine ⟨384*A,by positivity,?_⟩
  filter_upwards [ancestor_scales,ht.eventually_ge_atTop T,ht.eventually_ge_atTop 2,
    eventually_ge_atTop 2] with N hs hT₀ hk₂ hn₂
  let K := k N
  let M (i : ℕ) := N/2^i+K
  let S (b : Bool) (i : ℕ) := ((pairSeeds b (i+1) (M i+1)).card:ℝ)
  obtain ⟨hcut,hlog,hcube⟩ := hs
  change log (N:ℝ) ≤ 4*log (K:ℝ) at hlog
  change (K:ℝ)^3 ≤ 8*N at hcube
  have hK : 2 ≤ K := hk₂
  have hN' : 0 ≤ log (N:ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have heach (b : Bool) (i : ℕ) : S b i*(log (N:ℝ))^2 ≤ 16*A*(i+1)*M i := by
    have hKM : K ≤ M i := Nat.le_add_left ..
    have hbig := hT (M i) (le_trans hT₀ hKM) b (i+1)
    have hsingle : S b i ≤ ∑ t ∈ range (i+1), ((pairSeeds b (t+1) (M i+1)).card:ℝ) :=
      single_le_sum (f := fun t => ((pairSeeds b (t+1) (M i+1)).card:ℝ)) (fun _ _ => Nat.cast_nonneg _)
        (mem_range.mpr (Nat.lt_succ_self _))
    have haux := (mul_le_mul_of_nonneg_right hsingle (sq_nonneg _)).trans hbig
    have hlM : log (N:ℝ) ≤ 4*log (M i:ℝ) :=
      hlog.trans (mul_le_mul_of_nonneg_left (log_le_log (by exact_mod_cast (show 0 < K by omega))
        (Nat.cast_le.mpr hKM)) (by norm_num))
    push_cast at haux
    calc _ ≤ S b i*(4*log (M i:ℝ))^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN' hlM _) (Nat.cast_nonneg _)
      _ ≤ _ := by nlinarith only [haux]
  have hscale : (∑ i ∈ range K, ((i:ℝ)+1)*(M i:ℝ)) ≤ 12*N := by
    have hterm (i : ℕ) (hi : i ∈ range K) :
        ((i:ℝ)+1)*(M i:ℝ) ≤ N*(((i:ℝ)+1)/(2:ℝ)^i)+(K:ℝ)^2 := by
      have hfloor : ((N/2^i:ℕ):ℝ) ≤ N/(2:ℝ)^i := (le_div_iff₀ (by positivity)).mpr
        (by exact_mod_cast Nat.div_mul_le_self N (2^i))
      have hle : (i:ℝ)+1 ≤ K := by exact_mod_cast mem_range.mp hi
      dsimp [M]; push_cast
      calc _ ≤ ((i:ℝ)+1)*((N:ℝ)/2^i)+(K:ℝ)*K := by
            nlinarith only [mul_le_mul_of_nonneg_left hfloor (show 0 ≤ (i:ℝ)+1 by positivity),
              mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg (α:=ℝ) K)]
        _ = _ := by ring
    have hh := sum_le_sum hterm
    rw [sum_add_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul] at hh
    nlinarith only [hh,hcube,mul_le_mul_of_nonneg_left (weighted_geometric K) (Nat.cast_nonneg (α:=ℝ) N)]
  have hsum (b : Bool) : (∑ i ∈ range K, S b i)*(log (N:ℝ))^2 ≤ 192*A*N := by
    rw [sum_mul]
    calc _ ≤ ∑ i ∈ range K, 16*A*(((i:ℝ)+1)*(M i:ℝ)) :=
          sum_le_sum fun i _ => (heach b i).trans_eq (by ring)
      _ ≤ _ := by rw [← mul_sum]; nlinarith only [mul_le_mul_of_nonneg_left hscale (show 0 ≤ 16*A by positivity)]
  have hc : ((primesWithAncestor N).card:ℝ) ≤ ∑ i ∈ range K, (S true i + S false i) := by
    dsimp [S,M]; exact_mod_cast ancestor_count N K hcut
  rw [sum_add_distrib] at hc
  nlinarith only [mul_le_mul_of_nonneg_right hc (sq_nonneg (log (N:ℝ))),hsum true,hsum false]

#print axioms unbounded_ancestor_count

/-- No prime ancestor in either orbit and no prime iterate through H steps. -/
def CleanOrbit (p H : ℕ) : Prop := ¬HasPrimeAncestor p ∧
  ∀ (b : Bool) (j : ℕ), 0 < j → j ≤ H →
    ¬((if b then firstKindTerm else secondKindTerm) p j).Prime

noncomputable def cleanPrimes (N : ℕ) (H : ℕ → ℕ) : Finset ℕ := by
  classical exact N.primesLE.filter fun p => CleanOrbit p (H p)

/-- A density-one set of primes has no prime ancestor at any depth and no
prime descendant in a prescribed sublogarithmic window, simultaneously for
both signs. The radius is evaluated at the prime itself. -/
theorem density_one_clean_orbits {H : ℕ → ℕ} (h : Tendsto (fun n => (H n:ℝ)/log n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((cleanPrimes N H).card:ℝ) / N.primeCounting) atTop (𝓝 1) := by
  classical
  obtain ⟨A,hA,ha⟩ := unbounded_ancestor_count
  have hanc : Tendsto (fun N : ℕ => ((primesWithAncestor N).card:ℝ)/N.primeCounting) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds (x := 4*A)).div_atTop (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ ht
    filter_upwards [ha,chebyshev_lower] with N hn hc
    obtain ⟨hL,hpi,hscale⟩ := hc
    change ((primesWithAncestor N).card:ℝ)/N.primeCounting ≤ 4*A/log N
    rw [div_le_div_iff₀ hpi hL]
    apply le_of_mul_le_mul_right (a := log (N:ℝ)) _ hL
    nlinarith only [hn,mul_le_mul_of_nonneg_left hscale hA.le]
  let G (p : ℕ) := CleanOrbit p (H p)
  let B (N : ℕ) := N.primesLE.filter fun p => ¬G p
  have hbad : Tendsto (fun N : ℕ => ((B N).card:ℝ)/N.primeCounting) atTop (𝓝 0) := by
    have ht := hanc.add (prime_orbit_isolation h)
    rw [zero_add] at ht
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall fun N => ?_) ht
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have sub : B N ⊆ primesWithAncestor N ∪ (N.primesLE.filter fun p => HasPrimeNeighbor p (H p)) := by
      intro p hp
      obtain ⟨hpN,hbad⟩ := mem_filter.mp hp
      by_cases ha : HasPrimeAncestor p
      · exact mem_union_left _ (mem_filter.mpr ⟨hpN,ha⟩)
      · change ¬(¬HasPrimeAncestor p ∧ _) at hbad
        obtain ⟨b,j,hj,hjH,hp⟩ : ∃ (b : Bool) (j : ℕ), 0 < j ∧ j ≤ H p ∧
            ((if b then firstKindTerm else secondKindTerm) p j).Prime := by
          by_contra! hh
          exact hbad ⟨ha,hh⟩
        exact mem_union_right _ (mem_filter.mpr ⟨hpN,b,j,hj,hjH,Or.inl hp⟩)
    exact_mod_cast (card_le_card sub).trans (card_union_le ..)
  have ht := (tendsto_const_nhds (x := (1:ℝ))).sub hbad
  rw [sub_zero] at ht
  refine ht.congr' ?_
  filter_upwards [chebyshev_lower] with N hN
  have hπ := hN.2.1.ne'
  have hs : ((N.primesLE.filter G).card:ℝ)+(B N).card = N.primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := N.primesLE) (p := G)
  change 1 - ((B N).card:ℝ)/N.primeCounting = ((N.primesLE.filter G).card:ℝ)/N.primeCounting
  field_simp
  linarith only [hs]

#print axioms density_one_clean_orbits

#print axioms order_weight_bound

end CunninghamChain.OrbitIsolation
