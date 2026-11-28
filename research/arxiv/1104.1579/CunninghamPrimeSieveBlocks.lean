import CunninghamPrimeSieveDistribution
import CunninghamBrunLowerSieve

/-! Brun's lower sieve on primes in fixed reduced residue classes. -/

namespace CunninghamChain.PrimeSeedSieve

open Finset Filter Real ElliottHalberstamConjecture BrunBlocks

/-- Prime seeds satisfying prescribed residues at the fixed small primes. -/
noncomputable def primeSample (x : ℕ) (F : Finset ℕ) (a : (q : ℕ) → ZMod q) : Finset ℕ := by
  classical exact x.primesLE.filter fun n : ℕ => ∀ q ∈ F, (n : ZMod q) = a q

/-- Restricted intersections in the fixed sample have the unit-group densities
|B(q)| / φ(q), with one canonical discrepancy term for each joint residue. -/
theorem sample_intersection (x k : ℕ) (F T : Finset ℕ) (hd : Disjoint F T)
    (hp : ∀ q ∈ F ∪ T, q.Prime) (a : (q : ℕ) → ZMod q) (ha : ∀ q ∈ F, IsUnit (a q))
    (B : (q : ℕ) → Finset (ZMod q)) (hB : ∀ q ∈ T, ∀ b ∈ B q, IsUnit b)
    (hk : ∀ q ∈ T, (B q).card ≤ k) :
    |(∑ n ∈ primeSample x F a, intersection T B n) -
      ((x.primeCounting:ℝ) / (∏ q ∈ F, (q.totient:ℝ))) *
        ∏ q ∈ T, ((B q).card:ℝ)/q.totient| ≤
      (k:ℝ)^T.card * E x ((∏ q ∈ F,q)*(∏ q ∈ T,q)) := by
  classical
  let C (q : ℕ) : Finset (ZMod q) := if q ∈ F then {a q} else B q
  have hf (q : ℕ) (hq : q ∈ F) : C q = {a q} := if_pos hq
  have ht (q : ℕ) (hq : q ∈ T) : C q = B q := if_neg (fun h => disjoint_left.mp hd h hq)
  have h := prime_residue_intersection x (F ∪ T) hp C (by
    intro q hq c hc
    rcases mem_union.mp hq with hq | hq
    · rw [hf q hq, mem_singleton] at hc
      exact hc ▸ ha q hq
    · exact hB q hq c (ht q hq ▸ hc))
  have hc : (x.primesLE.filter fun n : ℕ => ∀ q ∈ F ∪ T, (n : ZMod q) ∈ C q) =
      (primeSample x F a).filter (fun n : ℕ => ∀ q ∈ T, (n : ZMod q) ∈ B q) := by
    ext n
    simp only [mem_filter, primeSample]
    constructor
    · rintro ⟨hn,hu⟩
      exact ⟨⟨hn,fun q hq => by simpa [hf q hq] using hu q (mem_union_left T hq)⟩,
        fun q hq => by simpa [ht q hq] using hu q (mem_union_right F hq)⟩
    · rintro ⟨⟨hn,hf'⟩,ht'⟩
      refine ⟨hn, fun q hq => ?_⟩
      rcases mem_union.mp hq with hq | hq
      · simpa [hf q hq] using hf' q hq
      · simpa [ht q hq] using ht' q hq
  have ef : (∏ q ∈ F, ((C q).card:ℝ)/q.totient) = 1 / ∏ q ∈ F, (q.totient:ℝ) := by
    rw [prod_div_distrib, prod_eq_one fun q hq => by simp [hf q hq]]
  have et : (∏ q ∈ T, ((C q).card:ℝ)/q.totient) = ∏ q ∈ T, ((B q).card:ℝ)/q.totient :=
    prod_congr rfl (fun q hq => by rw [ht q hq])
  have ecard : (∏ q ∈ F ∪ T, ((C q).card:ℝ)) = ∏ q ∈ T, ((B q).card:ℝ) := by
    rw [prod_union hd, prod_eq_one (s:=F) (fun q hq => by simp [hf q hq]), one_mul]
    exact prod_congr rfl (fun q hq => by rw [ht q hq])
  rw [hc, ecard, prod_union hd, ef, et, prod_union hd] at h
  simp only [intersection, sum_boole]
  convert! h.trans (mul_le_mul_of_nonneg_right (show (∏ q ∈ T, ((B q).card:ℝ)) ≤ (k:ℝ)^T.card by
    rw [← prod_const]; exact prod_le_prod (fun q _ => Nat.cast_nonneg _) (fun q hq => by exact_mod_cast hk q hq))
    (show 0 ≤ E x ((∏ q ∈ F,q)*(∏ q ∈ T,q)) by
      have hm : 0 < ∏ q ∈ F ∪ T, q := prod_pos (fun q hq => (hp q hq).pos)
      rw [prod_union hd] at hm
      exact E_nonneg _ _ hm)) using 2; ring

#print axioms sample_intersection

/-- The product expansion charges each tuple of block intersections to its union.
Disjoint prime bands make this assignment injective even when the truncation
degrees and the signs differ between bands. -/
theorem block_discrepancy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (M : ℝ) (Q : ι → Finset ℕ) (r : ι → ℕ) (o : ι → Bool)
    (B : (q : ℕ) → Finset (ZMod q)) (u : ℕ → ℝ) (err : Finset ℕ → ℝ)
    (hd : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hcount : ∀ T ⊆ univ.biUnion Q,
      |(∑ n ∈ P, intersection T B n) - M*(∏ q ∈ T, u q)| ≤ err T) :
    let G := Fintype.piFinset (fun i => selected (Q i) (r i) (o i))
    |(∑ n ∈ P, ∏ i, loc (Q i) (r i) (o i) (fun T => intersection T B n)) -
      M * (∏ i, loc (Q i) (r i) (o i) (fun T => ∏ q ∈ T, u q))| ≤
      ∑ T ∈ G.image (fun g => univ.biUnion g), err T := by
  classical
  let G := Fintype.piFinset (fun i => selected (Q i) (r i) (o i))
  let merge (g : ι → Finset ℕ) := univ.biUnion g
  have hs {g} (hg : g ∈ G) (i : ι) : g i ⊆ Q i := (selected_spec (Fintype.mem_piFinset.mp hg i)).1
  have hinj : Set.InjOn merge (G : Set (ι → Finset ℕ)) := by
    intro g hg h hh he
    have recover (f : ι → Finset ℕ) (hf : f ∈ G) (i : ι) : merge f ∩ Q i = f i := by
      ext q
      constructor
      · intro hq
        obtain ⟨j,_,hj⟩ := mem_biUnion.mp (mem_inter.mp hq).1
        by_cases hji : j=i
        · simpa [hji] using hj
        · exact (disjoint_left.mp (hd hji) (hs hf j hj) (mem_inter.mp hq).2).elim
      · exact fun hq => mem_inter.mpr ⟨mem_biUnion.mpr ⟨i,mem_univ _,hq⟩, hs hf i hq⟩
    funext i
    rw [← recover g hg i, he, recover h hh i]
  dsimp only
  rw [sum_image hinj]
  unfold loc
  simp_rw [prod_univ_sum]
  rw [sum_comm, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun g hg => ?_)
  have hdis : (↑(univ : Finset ι) : Set ι).PairwiseDisjoint g :=
    fun i _ j _ hij => (hd hij).mono (hs hg i) (hs hg j)
  have hw : |∏ i, BrunBlocks.sign (o i) (g i)| = 1 := by
    rw [Finset.abs_prod]
    apply prod_eq_one
    intro i _
    cases ho : o i <;> simp [BrunBlocks.sign,abs_pow]
  simp_rw [prod_mul_distrib, intersection_union]
  rw [← prod_biUnion hdis, ← mul_sum, mul_left_comm M, ← mul_sub, abs_mul, hw, one_mul]
  apply hcount
  intro q hq
  obtain ⟨i,hi,h⟩ := mem_biUnion.mp hq
  exact mem_biUnion.mpr ⟨i,hi,hs hg i h⟩

#print axioms block_discrepancy

private lemma large_subset_mass (Q : Finset ℕ) (u : ℕ → ℝ) (K : ℝ)
    (hu : ∀ q ∈ Q, 0 ≤ u q) (hs : ∑ q ∈ Q, u q ≤ K)
    (A : Finset (Finset ℕ)) (hA : A ⊆ Q.powerset) (m : ℕ) (hm : ∀ T ∈ A, m ≤ T.card) :
    (∑ T ∈ A, ∏ q ∈ T, u q) ≤ exp (2*K) / 2^m := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [sum_mul]
  calc
    _ ≤ ∑ T ∈ A, ∏ q ∈ T, 2*u q := by
      apply sum_le_sum
      intro T hT
      rw [prod_mul_distrib, prod_const, mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (hm T hT))
        (prod_nonneg (fun q hq => hu q ((mem_powerset.mp (hA hT)) hq)))
    _ ≤ ∑ T ∈ Q.powerset, ∏ q ∈ T, 2*u q := sum_le_sum_of_subset_of_nonneg hA
      (fun T hT _ => prod_nonneg fun q hq => mul_nonneg (by norm_num) (hu q ((mem_powerset.mp hT) hq)))
    _ = ∏ q ∈ Q, (1+2*u q) := (prod_one_add Q).symm
    _ ≤ ∏ q ∈ Q, exp (2*u q) := prod_le_prod
      (fun q hq => by linarith [hu q hq]) (fun q _ => by linarith [add_one_le_exp (2*u q)])
    _ ≤ _ := by rw [← Real.exp_sum, ← mul_sum]; exact Real.exp_le_exp.mpr (by linarith)

private lemma model_tail (Q : Finset ℕ) (r : ℕ) (u : ℕ → ℝ) (K : ℝ)
    (hu : ∀ q ∈ Q, 0 ≤ u q ∧ u q ≤ 1/2) (hs : ∑ q ∈ Q, u q ≤ K) :
    let U := loc Q r false (fun T => ∏ q ∈ T, u q)
    let O := loc Q r true (fun T => ∏ q ∈ T, u q)
    exp (-2*K) ≤ U+exp (2*K)/2^(2*r+1) ∧ O ≤ exp (2*K)/2^(2*r+1) := by
  classical
  dsimp only
  let A := selected Q r false
  let tail := Q.powerset \ A
  let w (T : Finset ℕ) := (-1:ℝ)^T.card * ∏ q ∈ T, u q
  have hA : A ⊆ Q.powerset := fun T hT => mem_powerset.mpr (selected_spec hT).1
  have hB : tail ⊆ Q.powerset := sdiff_subset
  have htail := large_subset_mass Q u K (fun q hq => (hu q hq).1) hs tail hB (2*r+1) (by
    intro T hT
    obtain ⟨hT,hnot⟩ := mem_sdiff.mp hT
    by_contra! h
    exact hnot (mem_biUnion.mpr ⟨T.card,mem_range.mpr h, mem_powersetCard.mpr ⟨mem_powerset.mp hT,rfl⟩⟩))
  have hsum : (∑ T ∈ tail, w T) + ∑ T ∈ A, w T = ∏ q ∈ Q, (1-u q) := by
    rw [sum_sdiff hA, show (∏ q ∈ Q, (1-u q)) = ∏ q ∈ Q, (1+(-1)*u q) by
      apply prod_congr rfl; intro q _; ring, prod_one_add]
    exact sum_congr rfl fun T _ => by simp only [w,prod_mul_distrib,prod_const]
  have hsmall : (∑ T ∈ tail, w T) ≤ ∑ T ∈ tail, ∏ q ∈ T, u q := by
    apply sum_le_sum
    intro T hT
    exact (mul_le_mul_of_nonneg_right (show (-1:ℝ)^T.card ≤ 1 by
      have := le_abs_self ((-1:ℝ)^T.card); simpa [abs_pow] using this)
      (prod_nonneg fun q hq => (hu q ((mem_powerset.mp (hB hT)) hq)).1)).trans_eq (one_mul _)
  have hmain : loc Q r false (fun T => ∏ q ∈ T, u q) = ∑ T ∈ A, w T := by simp [loc,A,w,BrunBlocks.sign]
  constructor
  · rw [hmain]
    linarith only [euler_lower Q u K hu hs, hsum, hsmall, htail]
  · have ho := large_subset_mass Q u K (fun q hq => (hu q hq).1) hs (Q.powersetCard (2*r+1))
      (fun T hT => mem_powerset.mpr (mem_powersetCard.mp hT).1) (2*r+1)
      (fun T hT => (mem_powersetCard.mp hT).2.ge)
    simpa [loc,selected,BrunBlocks.sign] using ho

private lemma prime_band_mass (H i k : ℕ) (hH : 1 < H) (hkH : 2*k ≤ H)
    (B : (q : ℕ) → Finset (ZMod q)) (hB : ∀ q, q.Prime → H < q → (B q).card ≤ k) :
    let Q := band H i
    let u (q : ℕ) := ((B q).card:ℝ)/q.totient
    (∀ q ∈ Q, 0 ≤ u q ∧ u q ≤ 1/2) ∧ (∑ q ∈ Q, u q) ≤ 8*k := by
  dsimp only
  have hq {q : ℕ} (hq : q ∈ band H i) : q.Prime ∧ H < q := by
    have hh := level_mono (H := H) (by omega) (Nat.zero_le i)
    exact ⟨(mem_band.mp hq).1, lt_of_le_of_lt (by simpa [level] using hh) (mem_band.mp hq).2.1⟩
  have ht {q : ℕ} (hq' : q ∈ band H i) : (q.totient:ℝ) = (q:ℝ)-1 := by
    rw [Nat.totient_prime (hq hq').1, Nat.cast_sub (hq hq').1.one_lt.le]; simp
  constructor
  · intro q hq'
    obtain ⟨hp,hh⟩ := hq hq'
    refine ⟨by positivity, ?_⟩
    rw [ht hq', div_le_iff₀ (by exact sub_pos.mpr (by exact_mod_cast hp.one_lt))]
    have hc : 2*(B q).card+1 ≤ q := by have := hB q hp hh; omega
    have hc' : 2*((B q).card:ℝ)+1 ≤ q := by exact_mod_cast hc
    linarith
  · have hs := (band_density H i k hH hkH B hB).2
    calc
      _ ≤ ∑ q ∈ band H i, 2*density B q := by
        apply sum_le_sum
        intro q hq'
        have h2 : (2:ℝ) ≤ q := by exact_mod_cast (hq hq').1.two_le
        dsimp [density]
        rw [ht hq', mul_div_assoc', div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith only [mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) (B q).card)]
      _ ≤ _ := by rw [← mul_sum]; linarith

/-- Even truncations retain at least 2^(-R-1) of the local mass, and the
first omitted odd truncation costs at most 2^(-j-2) of that even mean. -/
theorem prime_band_truncation (H i j k : ℕ) (hH : 1 < H) (hkH : 2*k ≤ H)
    (B : (q : ℕ) → Finset (ZMod q)) (hB : ∀ q, q.Prime → H < q → (B q).card ≤ k) :
    let R := 36*k
    let U (o : Bool) := loc (band H i) (R+j+2) o (fun T => ∏ q ∈ T, ((B q).card:ℝ)/q.totient)
    1/(2:ℝ)^(R+1) ≤ U false ∧ U true ≤ (1/(2:ℝ)^(j+2))*U false := by
  dsimp only
  let R := 36*k
  let u (q : ℕ) := ((B q).card:ℝ)/q.totient
  let U (o : Bool) := loc (band H i) (R+j+2) o (fun T => ∏ q ∈ T, u q)
  obtain ⟨hu,hs⟩ := prime_band_mass H i k hH hkH B hB
  obtain ⟨hmain,he⟩ := model_tail (band H i) (R+j+2) u (8*k) hu hs
  change exp (-2*(8*k)) ≤ U false + _ at hmain
  change U true ≤ _ at he
  have hR : exp (2*(8*k)) ≤ (2:ℝ)^R := (exp_le_exp.mpr
    (by linarith [Nat.cast_nonneg (α := ℝ) k] : 2*(8*(k:ℝ)) ≤ 24*k)).trans (sufficient_depth k)
  have hbase : 1/(2:ℝ)^R ≤ exp (-2*(8*k)) := by
    rw [show (-2:ℝ)*(8*k) = -(2*(8*k)) by ring, exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (exp_pos _) hR
  have htail : exp (2*(8*k))/2^(2*(R+j+2)+1) ≤
      1/(2:ℝ)^(j+2) * (1/2^(R+1)) := by
    rw [one_div_mul_one_div, ← pow_add, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc
      _ ≤ (2:ℝ)^R * 2^(j+2+(R+1)) := mul_le_mul_of_nonneg_right hR (by positivity)
      _ ≤ _ := by rw [← pow_add]; apply pow_le_pow_right₀ (by norm_num); omega
  have hh : 1/(2:ℝ)^(j+2) ≤ 1 := by
    rw [div_le_iff₀ (by positivity), one_mul]; exact one_le_pow₀ (by norm_num)
  have hpos := (htail.trans (mul_le_of_le_one_left (by positivity) hh))
  have hl : 1/(2:ℝ)^(R+1) ≤ U false := by
    have heq : 1/(2:ℝ)^R = 2*(1/2^(R+1)) := by rw [pow_succ]; field_simp
    linarith only [heq,hbase,hmain,hpos]
  exact ⟨hl,(he.trans htail).trans (mul_le_mul_of_nonneg_left hl (by positivity))⟩

#print axioms prime_band_truncation

end CunninghamChain.PrimeSeedSieve
