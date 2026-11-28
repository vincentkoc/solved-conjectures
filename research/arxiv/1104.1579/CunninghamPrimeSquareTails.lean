import research.arxiv.«1104.1579».CunninghamSquarefreePrimeSieve

/-! Prime seeds in a union of residue classes modulo large prime squares. -/

namespace CunninghamChain
open Finset

/-- A finite tail of reciprocal squares is bounded by the reciprocal cutoff. -/
theorem reciprocal_square_tail_finset {Q : Finset ℕ} {L T : ℕ} (hL : 0<L)
    (hQ : Q ⊆ Ioc L T) : ∑ q ∈ Q, 1/(q:ℝ)^2 ≤ 1/(L:ℝ) := by
  by_cases h : L≤T
  · let f (i : ℕ) := -1/((i:ℝ)-1)
    have hs := sum_Ico_sub f (show L+1 ≤ T+1 by omega)
    have hi : Q ⊆ Ico (L+1) (T+1) := by
      intro q hq; have := mem_Ioc.mp (hQ hq); exact mem_Ico.mpr (by omega)
    have comp (q : ℕ) (hq : q ∈ Ico (L+1) (T+1)) : 1/(q:ℝ)^2 ≤ f (q+1)-f q := by
      have hq' : 1 < (q:ℝ) := by exact_mod_cast (show 1<q by have := (mem_Ico.mp hq).1; omega)
      dsimp [f]
      push_cast
      rw [add_sub_cancel_right]
      have hd : 0 < (q:ℝ)-1 := by linarith
      field_simp [hd]
      nlinarith
    calc
      _ ≤ ∑ q ∈ Ico (L+1) (T+1), 1/(q:ℝ)^2 := sum_le_sum_of_subset_of_nonneg hi (by intros; positivity)
      _ ≤ _ := sum_le_sum comp
      _ = f (T+1)-f (L+1) := hs
      _ ≤ _ := by
        dsimp [f]; push_cast; simp only [add_sub_cancel_right]
        have : 0 ≤ 1/(T:ℝ) := by positivity
        simp only [neg_div,neg_sub_neg]
        linarith
  · have hnil : Q=∅ := eq_empty_of_forall_notMem fun q hq => by
      have := mem_Ioc.mp (hQ hq); omega
    simp [hnil]

private lemma sum_square_class_lengths {Q : Finset ℕ} {L T X : ℕ} (hL : 0<L)
    (hQ : Q ⊆ Ioc L T) :
    ∑ q ∈ Q, ((X/q^2+1:ℕ):ℝ) ≤ (X:ℝ)/L+T := by
  have hc : (Q.card:ℝ) ≤ T := by exact_mod_cast (card_le_card hQ).trans (show (Ioc L T).card ≤ T by simp)
  simp only [Nat.cast_add,Nat.cast_one,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one]
  apply add_le_add _ hc
  calc
    _ ≤ ∑ q ∈ Q, (X:ℝ)*(1/(q:ℝ)^2) := sum_le_sum fun q _ => by
      calc
        _ ≤ (X:ℝ)/((q^2:ℕ):ℝ) := Nat.cast_div_le
        _ = _ := by push_cast; ring
    _ = _ := (mul_sum ..).symm
    _ ≤ _ := by simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (reciprocal_square_tail_finset hL hQ) (Nat.cast_nonneg (α:=ℝ) X)

private lemma square_residue_card_le (q X a : ℕ) :
    ((range X).filter fun p => p%q^2=a).card ≤ X/q^2+1 := by
  let S := (range X).filter fun p => p%q^2=a
  have hc : S.card ≤ (range (X/q^2+1)).card := by
    apply card_le_card_of_injOn (fun p => p/q^2)
    · intro p hp
      have hle : p/q^2 ≤ X/q^2 := Nat.div_le_div_right (mem_range.mp (mem_filter.mp hp).1).le
      exact mem_range.mpr (Nat.lt_succ_of_le hle)
    · intro p hp s hs he
      change p/q^2=s/q^2 at he
      have hm := (mem_filter.mp hp).2.trans (mem_filter.mp hs).2.symm
      calc
        p = p%q^2 + q^2*(p/q^2) := (Nat.mod_add_div ..).symm
        _ = s%q^2 + q^2*(s/q^2) := congrArg₂ (fun i j => i+q^2*j) hm he
        _ = s := Nat.mod_add_div ..
  simpa using hc

/-- Finite bound for primes in one prescribed residue class for each square.
The sieve treats primes up to Y. Above Y an integer count suffices. -/
theorem prime_square_tail_bound (a : ℕ → ℕ) {L Y T z X : ℕ}
    (hL : 0<L) (hY : 0<Y) (hz : 1<z) (hsize : z^16*Y^2 ≤ X) :
    (((range X).filter fun p => p.Prime ∧
      ∃ q ∈ T.primesLE, L<q ∧ p%q^2=a q).card : ℝ) * Real.log ((z:ℝ)+1) ≤
      24*((X:ℝ)/L+Y)+((X:ℝ)/Y+T+(z+1:ℕ))*Real.log ((z:ℝ)+1) := by
  classical
  let P := (range X).filter fun p => p.Prime ∧ ∃ q ∈ T.primesLE, L<q ∧ p%q^2=a q
  let S := T.primesLE.filter fun q => L<q ∧ q≤Y
  let B := T.primesLE.filter fun q => Y<q
  let U (q : ℕ) := (range X).filter fun p => z<p ∧ p.Prime ∧ p%q^2=a q
  let V (q : ℕ) := (range X).filter fun p => p%q^2=a q
  let l := Real.log ((z:ℝ)+1)
  have hl : 0 ≤ l := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) z; linarith)
  have incl : P ⊆ (range (z+1) ∪ S.biUnion U) ∪ B.biUnion V := by
    intro p hp
    obtain ⟨hx,hp, q,hq,hLq,he⟩ := mem_filter.mp hp
    by_cases hzp : p≤z
    · exact mem_union_left _ (mem_union_left _ (mem_range.mpr (by omega)))
    by_cases hqY : q≤Y
    · exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr
        ⟨q,mem_filter.mpr ⟨hq,hLq,hqY⟩,mem_filter.mpr ⟨hx,by omega,hp,he⟩⟩))
    · exact mem_union_right _ (mem_biUnion.mpr
        ⟨q,mem_filter.mpr ⟨hq,by omega⟩,mem_filter.mpr ⟨hx,he⟩⟩)
  have count : P.card ≤ z+1+(∑ q ∈ S,(U q).card)+(∑ q ∈ B,(V q).card) := by
    have h₁ := card_union_le (range (z+1) ∪ S.biUnion U) (B.biUnion V)
    have h₂ := card_union_le (range (z+1)) (S.biUnion U)
    have h₃ := card_biUnion_le (s:=S) (t:=U)
    have h₄ := card_biUnion_le (s:=B) (t:=V)
    have h₅ := card_le_card incl
    rw [card_range] at h₂
    omega
  have sm : (∑ q ∈ S, ((U q).card:ℝ))*l ≤ 24*((X:ℝ)/L+Y) := by
    rw [sum_mul]
    calc
      _ ≤ ∑ q ∈ S, 24*((X/q^2+1:ℕ):ℝ) := sum_le_sum fun q hq => by
        obtain ⟨hp,_,hle⟩ := mem_filter.mp hq
        apply prime_square_residue_sieve (Nat.prime_of_mem_primesLE hp) _ hz
        have hpos := (Nat.prime_of_mem_primesLE hp).pos
        have sumle := (Nat.mul_le_mul_left (z^16) (Nat.pow_le_pow_left hle 2)).trans hsize
        exact (Nat.le_div_iff_mul_le (by positivity)).mpr sumle |>.trans (Nat.le_succ _)
      _ = _ := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_square_class_lengths hL (by
        intro q hq; exact mem_Ioc.mpr (mem_filter.mp hq).2)) (by norm_num)
  have big : (∑ q ∈ B, ((V q).card:ℝ)) ≤ (X:ℝ)/Y+T := by
    calc
      _ ≤ ∑ q ∈ B, ((X/q^2+1:ℕ):ℝ) := sum_le_sum fun q _ => by exact_mod_cast square_residue_card_le q X (a q)
      _ ≤ _ := sum_square_class_lengths hY (by
        intro q hq
        obtain ⟨hp,hy⟩ := mem_filter.mp hq
        exact mem_Ioc.mpr ⟨hy,Nat.le_of_mem_primesLE hp⟩)
  have hc : (P.card:ℝ) ≤ (z+1:ℕ)+(∑ q ∈ S, ((U q).card:ℝ))+(∑ q ∈ B,((V q).card:ℝ)) := by exact_mod_cast count
  change (P.card:ℝ)*l ≤ _
  nlinarith only [mul_le_mul_of_nonneg_right hc hl,sm,mul_le_mul_of_nonneg_right big hl]

#print axioms prime_square_tail_bound
#print axioms reciprocal_square_tail_finset

/-- Primes below X in any of the given classes, retaining only square
moduli up to D X. -/
noncomputable def largeSquareClassPrimes (a : ℕ → ℕ) (D L X : ℕ) : Finset ℕ := by
  classical exact (range X).filter fun p => p.Prime ∧
    ∃ q ∈ (Nat.sqrt (D*X)).primesLE, L<q ∧ p%q^2=a q

private lemma tail_scale_bounds {z X D L T : ℕ} (hz : 1<z) (hLz : L≤z) (hmax : 65536*(D+1)*L≤z)
    (h₀ : z^32≤X) (hT : T ≤ (D+1)*(z+1)^16) :
    z^8*L≤X ∧ z*L≤z^8 ∧ T*z*L≤X ∧ (z+1)*z*L≤X := by
  let Y := z^8
  have YL : Y*L≤X := by
    calc
      _ ≤ z^8*z := Nat.mul_le_mul_left _ hLz
      _ = z^9 := (pow_succ ..).symm
      _ ≤ z^32 := Nat.pow_le_pow_right (by omega) (by decide)
      _ ≤ X := h₀
  have zL : z*L≤Y := by
    calc
      _ ≤ z*z := Nat.mul_le_mul_left _ hLz
      _ = z^2 := (sq _).symm
      _ ≤ z^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have tzL : T*z*L ≤ X := by
    have h₂ : (z+1)^16 ≤ 2^16*z^16 := by rw [←mul_pow]; exact Nat.pow_le_pow_left (by omega) _
    calc
      _ ≤ (D+1)*(2^16*z^16)*z*L := Nat.mul_le_mul_right L
        (Nat.mul_le_mul_right z (hT.trans (Nat.mul_le_mul_left _ h₂)))
      _ = (65536*(D+1)*L)*z^17 := by rw [pow_succ z 16]; ring
      _ ≤ z*z^17 := Nat.mul_le_mul_right _ (by omega)
      _ = z^18 := by rw [pow_succ]; ring
      _ ≤ z^32 := Nat.pow_le_pow_right (by omega) (by decide)
      _ ≤ X := h₀
  have zzL : (z+1)*z*L ≤ X := by
    have hs : z+1 ≤ z^2 := by nlinarith only [hz,Nat.mul_le_mul_left z (show 2≤z by omega)]
    calc
      _ ≤ z^2*z*z := Nat.mul_le_mul (Nat.mul_le_mul_right z hs) hLz
      _ = z^4 := by ring
      _ ≤ z^32 := Nat.pow_le_pow_right (by omega) (by decide)
      _ ≤ X := h₀
  exact ⟨YL,zL,tzL,zzL⟩

/-- Relative to the prime scale X/log X, the upper bound for all squares
above L is O(1/L), uniformly in the choice of residue at each prime. -/
theorem eventually_large_square_class_primes (a : ℕ → ℕ) (D L : ℕ) (hL : 0<L) :
    ∀ᶠ X : ℕ in Filter.atTop,
      ((largeSquareClassPrimes a D L X).card:ℝ)*Real.log X ≤ 1632*((X:ℝ)/L) := by
  classical
  filter_upwards [Filter.eventually_ge_atTop ((2+65536*(D+1)*L)^32)] with X hX
  let z := Nat.nthRoot 32 X
  have hz' : 2+65536*(D+1)*L ≤ z := (Nat.le_nthRoot_iff (by decide : 32≠0)).mpr hX
  have hz : 1<z := by omega
  have hLz : L≤z := by nlinarith only [hz',show 0 ≤ D*L by positivity]
  have h₀ : z^32≤X := Nat.pow_nthRoot_le (Or.inl (by decide : 32≠0))
  have h₁ : X < (z+1)^32 := Nat.lt_pow_nthRoot_add_one (by decide) X
  have hX₀ : 0<X := lt_of_lt_of_le (by positivity : 0<z^32) h₀
  let T := Nat.sqrt (D*X)
  let Y := z^8
  have hT : T ≤ (D+1)*(z+1)^16 := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    have ht : T^2 ≤ D*X := by simpa only [sq] using Nat.sqrt_le (D*X)
    refine ht.trans ?_
    rw [mul_pow,←pow_mul]
    exact Nat.mul_le_mul ((Nat.le_succ D).trans (Nat.le_self_pow (by decide : 2≠0) _)) h₁.le
  have sz : z^16*Y^2 ≤ X := by
    simpa only [Y,←pow_mul,←pow_add] using h₀
  have hraw := prime_square_tail_bound a (T:=T) hL (by dsimp [Y]; positivity) hz sz
  have log_upper : Real.log X ≤ 32*Real.log ((z:ℝ)+1) := by
    have hx : (X:ℝ) ≤ ((z:ℝ)+1)^32 := by exact_mod_cast h₁.le
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log (by exact_mod_cast hX₀) hx
  have log_z : Real.log ((z:ℝ)+1) ≤ z := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (z:ℝ)+1)
    linarith
  obtain ⟨YL,zL,tzL,zzL⟩ := tail_scale_bounds hz hLz (by omega : 65536*(D+1)*L≤z) h₀ hT
  have posL : 0<(L:ℝ) := by exact_mod_cast hL
  have posY : 0<(Y:ℝ) := by dsimp [Y]; positivity
  have hy : (Y:ℝ) ≤ (X:ℝ)/L := (le_div_iff₀ posL).mpr (by exact_mod_cast YL)
  have hxY : (X:ℝ)/Y*z ≤ (X:ℝ)/L := by
    apply (le_div_iff₀ posL).mpr
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (div_le_iff₀ posY).mpr
    have hl : (z:ℝ)*L ≤ Y := by exact_mod_cast zL
    nlinarith only [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α:=ℝ) X)]
  have ht : (T:ℝ)*z ≤ (X:ℝ)/L := (le_div_iff₀ posL).mpr (by exact_mod_cast tzL)
  have hzz : ((z+1:ℕ):ℝ)*z ≤ (X:ℝ)/L := (le_div_iff₀ posL).mpr (by exact_mod_cast zzL)
  let A := largeSquareClassPrimes a D L X
  change (A.card:ℝ)*Real.log ((z:ℝ)+1) ≤ _ at hraw
  have hbig := mul_le_mul_of_nonneg_left log_z (add_nonneg (add_nonneg (div_nonneg (Nat.cast_nonneg (α:=ℝ) X) posY.le) (Nat.cast_nonneg T)) (Nat.cast_nonneg (z+1)))
  have htotal := mul_le_mul_of_nonneg_left log_upper (Nat.cast_nonneg (α:=ℝ) A.card)
  change (A.card:ℝ)*_ ≤ _
  nlinarith only [htotal,hraw,hbig,hxY,ht,hzz,hy]

#print axioms eventually_large_square_class_primes

end CunninghamChain
