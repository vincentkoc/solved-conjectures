import CunninghamPrimeSieveBlocks

/-! Simultaneously sifting prime seeds through all Cunningham prime bands. -/

namespace CunninghamChain.PrimeSeedSieve

open Finset Filter Real ElliottHalberstamConjecture BrunBlocks

private def truncationLevel (k : ℕ) := 4*(8*(36*k)+29)

private lemma block_level_bound (H J k : ℕ) (hH : 1 < H) (o : Fin J → Bool)
    (g : Fin J → Finset ℕ)
    (hg : g ∈ Fintype.piFinset (fun i : Fin J => selected (band H i) (36*k+i.rev.val+2) (o i))) :
    (∏ q ∈ univ.biUnion g, q) ≤ (level H J)^(8*(36*k)+28) := by
  classical
  let R := 36*k
  let z (i : Fin J) := level H (i.val+1)
  let r (i : Fin J) := R+i.rev.val+2
  have hs (i : Fin J) := selected_spec (Fintype.mem_piFinset.mp hg i)
  have hd : (↑(univ : Finset (Fin J)) : Set (Fin J)).PairwiseDisjoint g :=
    fun i _ j _ hij => (band_disjoint (H := H) hH.le hij).mono (hs i).1 (hs j).1
  rw [prod_biUnion hd]
  have hcost : (∏ i : Fin J, (z i^(2*r i+1))^2) ≤ (level H J)^(8*R+28) := by
    exact_mod_cast band_cost H J R (by omega)
  refine le_trans (prod_le_prod' (fun i _ => ?_)) hcost
  have hz : 0 < z i := by dsimp [z,level]; positivity
  calc
    _ ≤ ∏ _q ∈ g i, z i := prod_le_prod' (fun q hq => (mem_band.mp ((hs i).1 hq)).2.2)
    _ = z i^(g i).card := prod_const _
    _ ≤ z i^(2*r i+1) := Nat.pow_le_pow_right hz (hs i).2
    _ ≤ _ := Nat.le_self_pow (by decide) _

private noncomputable def sifted (x H J : ℕ) (a : (q : ℕ) → ZMod q)
    (B : (q : ℕ) → Finset (ZMod q)) : Finset ℕ := by
  classical exact (primeSample x H.primesLE a).filter fun n =>
    ∀ i : Fin J, (hits (band H i) B n).card = 0

/-- Finite count after all blocks. The level condition is polynomial in the last
sieving prime, with exponent depending only on the number of forbidden residues. -/
private theorem sieve_count (x H J k : ℕ) (hH : 1 < H) (hkH : 2*k ≤ H)
    (a : (q : ℕ) → ZMod q) (ha : ∀ q ∈ H.primesLE, IsUnit (a q))
    (B : (q : ℕ) → Finset (ZMod q))
    (hB : ∀ q, q.Prime → H < q → (B q).card ≤ k)
    (hu : ∀ q, q.Prime → H < q → ∀ b ∈ B q, IsUnit b)
    (hW : (∏ q ∈ H.primesLE, q) ≤ level H J)
    (hx : (level H J)^(truncationLevel k) ≤ x)
    (D : ℝ) (herr : ∀ W : ℕ, 0 < W → ∀ S : Finset (Finset ℕ), S ⊆ x.primesLE.powerset →
      (∀ T ∈ S, (W*(∏ q ∈ T, q))^4 ≤ x) →
      (∑ T ∈ S, (k:ℝ)^T.card * E x (W*(∏ q ∈ T, q))) ≤ D) :
    (x.primeCounting:ℝ) / (∏ q ∈ H.primesLE, (q.totient:ℝ)) *
      (1/2 * (1/((2:ℝ)^J)^(36*k+1))) ≤
        ((sifted x H J a B).card:ℝ) + (J+1)*D := by
  classical
  let R := 36*k
  let Z := level H J
  let F := H.primesLE
  let Q (i : Fin J) := band H i
  let r (i : Fin J) := R+i.rev.val+2
  let u (q : ℕ) := ((B q).card:ℝ)/q.totient
  let U (i : Fin J) (o : Bool) := loc (Q i) (r i) o (fun T => ∏ q ∈ T, u q)
  let ε (i : Fin J) := (1:ℝ)/2^(i.rev.val+2)
  let W := ∏ q ∈ F, q
  let M := (x.primeCounting:ℝ) / (∏ q ∈ F, (q.totient:ℝ))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hWp : 0 < W := prod_pos (fun q hq => (Nat.prime_of_mem_primesLE hq).pos)
  have hPro (i : Fin J) := prime_band_truncation H i i.rev.val k hH hkH B hB
  have hl (i : Fin J) : 1/(2:ℝ)^(R+1) ≤ U i false := (hPro i).1
  have hU (i : Fin J) : 0 ≤ U i false := (by positivity : (0:ℝ) ≤ 1/2^(R+1)).trans (hl i)
  have hZ : 0 < Z := by dsimp [Z,level]; positivity
  have hZx : Z ≤ x := (Nat.le_self_pow (by dsimp [truncationLevel]; omega) Z).trans hx
  have hprime {q : ℕ} (hq : q ∈ univ.biUnion Q) : q.Prime ∧ H < q ∧ q ≤ x := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
    obtain ⟨hp,hl',hh'⟩ := mem_band.mp hi
    have hmono := level_mono (H := H) hH.le
    exact ⟨hp,lt_of_le_of_lt (by simpa [level] using hmono (Nat.zero_le i.val)) hl',
      hh'.trans ((hmono i.isLt).trans hZx)⟩
  have hd := band_disjoint (J := J) (H := H) hH.le
  have hmodel (o : Fin J → Bool) :
      |(∑ n ∈ primeSample x F a, ∏ i, loc (Q i) (r i) (o i) (fun T => intersection T B n)) -
        M*(∏ i, U i (o i))| ≤ D := by
    let G := Fintype.piFinset (fun i => selected (Q i) (r i) (o i))
    let err (T : Finset ℕ) := (k:ℝ)^T.card * E x (W*(∏ q ∈ T,q))
    have hc (T : Finset ℕ) (hT : T ⊆ univ.biUnion Q) :
        |(∑ n ∈ primeSample x F a, intersection T B n) - M*(∏ q ∈ T,u q)| ≤ err T := by
      have hdis : Disjoint F T := disjoint_left.mpr (fun {_} hF h => (hprime (hT h)).2.1.not_ge (Nat.mem_primesLE.mp hF).1)
      apply sample_intersection x k F T hdis _ a ha B (fun q hq => hu q (hprime (hT hq)).1 (hprime (hT hq)).2.1)
        (fun q hq => hB q (hprime (hT hq)).1 (hprime (hT hq)).2.1)
      intro q hq
      exact (mem_union.mp hq).elim Nat.prime_of_mem_primesLE (fun h => (hprime (hT h)).1)
    apply (block_discrepancy (primeSample x F a) M Q r o B u err hd hc).trans
    apply herr W hWp
    · intro T hT
      obtain ⟨g,hg,rfl⟩ := mem_image.mp hT
      apply mem_powerset.mpr
      intro q hq
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
      have h := (selected_spec (Fintype.mem_piFinset.mp hg i)).1 hi
      have hp := hprime (mem_biUnion.mpr ⟨i,mem_univ _,h⟩)
      exact Nat.mem_primesLE.mpr ⟨hp.2.2,hp.1⟩
    · intro T hT
      obtain ⟨g,hg,rfl⟩ := mem_image.mp hT
      have hb := Nat.mul_le_mul hW (block_level_bound H J k hH o g hg)
      have he : (Z*Z^(8*R+28))^4 = Z^(truncationLevel k) := by
        rw [← pow_succ', ← pow_mul]; congr 1; dsimp [truncationLevel,R]; ring
      exact (Nat.pow_le_pow_left hb 4).trans (he ▸ hx)
  have hs := finite_block_lower (primeSample x F a) M D hM Q r B U ε hU (fun i => (hPro i).2) hmodel
  have hmass : 1/((2:ℝ)^J)^(R+1) ≤ ∏ i, U i false := by
    have h := prod_le_prod (s := (univ : Finset (Fin J))) (fun _ _ => (by positivity : (0:ℝ) ≤ 1/2^(R+1))) (fun i _ => hl i)
    simpa only [prod_const,card_univ,Fintype.card_fin,one_div,inv_pow,← pow_mul,Nat.mul_comm J (R+1)] using h
  have hlower := mul_le_mul (show (1:ℝ)/2 ≤ 1-∑ i, ε i by linarith only [geometric_errors J])
    hmass (by positivity) (by have := geometric_errors J; change 0 ≤ 1-∑ i : Fin J, (1:ℝ)/2^(i.rev.val+2); linarith)
  have h := (mul_le_mul_of_nonneg_left hlower hM).trans hs
  rw [Fintype.card_fin] at h
  have hset : sifted x H J a B = (primeSample x F a).filter (fun n => ∀ i : Fin J, (hits (Q i) B n).card = 0) := by
    ext n
    simp only [sifted,mem_filter,Q,F]
  rw [hset]
  convert! h using 3
  apply congrArg Finset.card
  ext n
  simp only [mem_filter,Q,F]

private lemma chebyshev_count : ∀ᶠ x : ℕ in atTop, (x:ℝ) ≤ 4*x.primeCounting*log x := by
  have tend : Tendsto (fun x : ℕ => (x:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [tend.eventually (isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ) < 1/8)),
    eventually_ge_atTop 2] with x h hx
  have hx' : (2:ℝ) ≤ x := by exact_mod_cast hx
  have hl := (div_le_iff₀ (log_pos (by linarith : (1:ℝ)<x))).mp (Chebyshev.pi_ge x)
  have hlog : log ((x:ℝ)+1) ≤ 1/8*((x:ℝ)+1) := by
    simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg (log_nonneg (by linarith : 1 ≤ (x:ℝ)+1)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ x+1)] using h
  have ht : (1:ℝ)/2 ≤ log 2 := by linarith [log_two_gt_d9]
  nlinarith only [hlog,hl,hx',mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (α := ℝ) x)]

private lemma count_dominates (φ C : ℝ) (hφ : 0 < φ) (hC : 0 < C) (m : ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ P J Y S : ℝ, 0 < P → P ≤ log x → J ≤ log x →
      0 ≤ Y → Y < sqrt x →
      (x.primeCounting:ℝ)/φ * (1/2 * (1/P^m)) ≤ S + J*(C*x/log x^(m+3)) → Y < S := by
  have small := (isLittleO_log_rpow_rpow_atTop (s := 1/2) (m+1 : ℕ) (by norm_num)).bound
    (show (0:ℝ) < 1/(16*φ) by positivity)
  have loglim := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [chebyshev_count,tendsto_natCast_atTop_atTop.eventually small,
    loglim.eventually_ge_atTop (16*φ*C), eventually_ge_atTop 2] with x hπ hs hlog hx
  intro P J Y S hP hPt hJ hY hY' hcount
  let t := log (x:ℝ)
  have ht : 0 < t := log_pos (by exact_mod_cast (show 1 < x by omega))
  have hx0 : 0 < (x:ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hs' : t^(m+1) ≤ (1/(16*φ))*sqrt x := by
    simpa only [Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ht.le _),
      ← Real.sqrt_eq_rpow,abs_of_nonneg (sqrt_nonneg _),t] using hs
  let d := (x:ℝ)/(16*φ*t^(m+1))
  have denom : 0 < 16*φ*t^(m+1) := by positivity
  have hy : Y < d := by
    apply (lt_div_iff₀ denom).mpr
    have hsqrt : 16*φ*t^(m+1) ≤ sqrt x := by
      have := mul_le_mul_of_nonneg_left hs' (show 0 ≤ 16*φ by positivity)
      field_simp at this
      linarith only [this]
    calc
      _ < sqrt x * (16*φ*t^(m+1)) := mul_lt_mul_of_pos_right hY' denom
      _ ≤ sqrt x * sqrt x := mul_le_mul_of_nonneg_left hsqrt (sqrt_nonneg _)
      _ = x := Real.mul_self_sqrt hx0.le
  have hm : 2*d ≤ (x.primeCounting:ℝ)/φ * (1/2 * (1/P^m)) := by
    have h1 : 2*d ≤ (x.primeCounting:ℝ)/φ * (1/2 * (1/t^m)) := by
      change 2*((x:ℝ)/(16*φ*t^(m+1))) ≤ _
      rw [pow_succ]
      field_simp
      change (x:ℝ) ≤ 4*x.primeCounting*t at hπ
      nlinarith only [hπ]
    refine h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (by positivity))
    exact one_div_le_one_div_of_le (pow_pos hP _) (pow_le_pow_left₀ hP.le hPt m)
  have herr : J*(C*x/t^(m+3)) ≤ d := by
    refine (mul_le_mul_of_nonneg_right hJ (by positivity)).trans ?_
    change t*(C*x/t^(m+3)) ≤ (x:ℝ)/(16*φ*t^(m+1))
    rw [show m+3 = m+1+2 by omega,pow_add]
    field_simp
    change 16*φ*C ≤ t at hlog
    nlinarith only [hlog]
  linarith only [hy,hm,hcount,herr]

/-- Above an arbitrary threshold there is a prime in the prescribed reduced
classes at the primes up to H, avoiding every forbidden reduced class through Z.
The upper bound on that prime is polynomial in Z, uniformly in H. -/
theorem rough_prime_sample (hBV : BombieriVinogradov) (k H : ℕ) (hH : 1 < H) (hkH : 2*k ≤ H)
    (a : (q : ℕ) → ZMod q) (ha : ∀ q ∈ H.primesLE, IsUnit (a q))
    (B : (q : ℕ) → Finset (ZMod q))
    (hB : ∀ q, q.Prime → H < q → (B q).card ≤ k)
    (hu : ∀ q, q.Prime → H < q → ∀ b ∈ B q, IsUnit b) (X : ℕ) :
    ∃ Z p : ℕ, X < Z ∧ Z < p ∧ p ≤ Z^(4*(8*(36*k)+29)) ∧ p.Prime ∧
      (∀ q ∈ H.primesLE, (p : ZMod q) = a q) ∧
      ∀ q, q.Prime → H < q → q ≤ Z → (p : ZMod q) ∉ B q := by
  classical
  let m := 36*k+1
  let φ := ∏ q ∈ H.primesLE, (q.totient:ℝ)
  have hφ : 0 < φ := prod_pos (fun q hq => by exact_mod_cast Nat.totient_pos.mpr (Nat.prime_of_mem_primesLE hq).pos)
  obtain ⟨C,hC,herr⟩ := weighted_bombieri_vinogradov hBV k (m+3) (by omega)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (herr.and (count_dominates φ C hφ hC m))
  let W := ∏ q ∈ H.primesLE, q
  let J := X+W+N+2
  let Z := level H J
  let A := truncationLevel k
  let x := Z^A
  let S := sifted x H J a B
  have hA : 4 ≤ A := by dsimp [A,truncationLevel]; omega
  have hJ : J+1 ≤ 2^J := Nat.lt_two_pow_self
  have hZ : 2^J ≤ Z := (Nat.lt_two_pow_self (n := 2^J)).le.trans (Nat.pow_le_pow_left hH _)
  have hJZ : J+1 ≤ Z := hJ.trans hZ
  have hZ2 : 2 ≤ Z := by dsimp only [J] at hJZ; omega
  have hZx : Z ≤ x := Nat.le_self_pow (by omega) _
  have hWN : W ≤ Z ∧ N ≤ x ∧ X < Z := by dsimp only [J] at hJZ; omega
  have hh := hN x hWN.2.1
  have hcount := sieve_count x H J k hH hkH a ha B hB hu hWN.1 le_rfl _ hh.1
  have hlogx : log (x:ℝ) = A*((2:ℝ)^J * log H) := by
    dsimp only [x,Z,level]
    rw [Nat.cast_pow, log_pow, Nat.cast_pow, log_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hlogH : (1:ℝ)/2 ≤ log H := by
    have h := log_le_log (by norm_num : (0:ℝ) < 2) (by exact_mod_cast hH : (2:ℝ) ≤ H)
    linarith [log_two_gt_d9]
  have hP : (2:ℝ)^J ≤ log x := by
    rw [hlogx]
    have hA' : (2:ℝ) ≤ A := by exact_mod_cast (show 2 ≤ A by omega)
    have h1 : 1 ≤ (A:ℝ)*log H := by nlinarith [mul_le_mul hA' hlogH (by norm_num) (by positivity)]
    calc
      _ = (2:ℝ)^J * 1 := (mul_one _).symm
      _ ≤ _ := by simpa only [mul_left_comm,mul_assoc] using mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (2:ℝ)^J)
  have hJ' : (J:ℝ)+1 ≤ log x := (by exact_mod_cast hJ : (J:ℝ)+1 ≤ (2:ℝ)^J).trans hP
  have hY : (Z:ℝ)+1 < sqrt x := by
    apply Real.lt_sqrt_of_sq_lt
    have hh : Z^4 ≤ x := Nat.pow_le_pow_right (by omega) hA
    have hle : (Z:ℝ)^4 ≤ x := by exact_mod_cast hh
    have hz : (2:ℝ) ≤ Z := by exact_mod_cast hZ2
    have hz' : (Z:ℝ)+1 < (Z:ℝ)^2 := by nlinarith [sq_nonneg ((Z:ℝ)-2)]
    calc
      _ < ((Z:ℝ)^2)^2 := pow_lt_pow_left₀ hz' (by positivity) (by decide)
      _ ≤ _ := by simpa [← pow_mul] using hle
  have hs := hh.2 ((2:ℝ)^J) (J+1) (Z+1) S.card (by positivity) hP hJ' (by positivity) hY hcount
  have hc : Z+1 < S.card := by exact_mod_cast hs
  obtain ⟨p,hp,hpZ⟩ : ∃ p ∈ S, Z < p := by
    by_contra! hn
    have hsub : S ⊆ range (Z+1) := fun n hn' => mem_range.mpr (Nat.lt_succ_of_le (hn n hn'))
    exact hc.not_ge ((card_le_card hsub).trans_eq (card_range _))
  have hp' := mem_filter.mp (show p ∈ (primeSample x H.primesLE a).filter _ from hp)
  have hap := mem_filter.mp (show p ∈ x.primesLE.filter _ from hp'.1)
  have hpx := Nat.mem_primesLE.mp hap.1
  refine ⟨Z,p,hWN.2.2,hpZ,hpx.1,hpx.2,hap.2,?_⟩
  intro q hq hl hh' hb
  obtain ⟨i,hi⟩ := band_cover hq hl hh'
  have hnil := card_eq_zero.mp (hp'.2 i)
  have hm : q ∈ hits (band H i) B p := mem_filter.mpr ⟨hi,hb⟩
  simp [hnil] at hm

#print axioms rough_prime_sample

end CunninghamChain.PrimeSeedSieve
