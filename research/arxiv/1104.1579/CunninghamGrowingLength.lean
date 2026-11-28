import research.arxiv.«1104.1579».CunninghamSingularSeriesGrowth
import research.arxiv.«1104.1579».CunninghamBrunSieve

/-! Finite sieves for Cunningham prime prefixes of growing length. -/

namespace CunninghamChain

open Finset Filter Real BatemanHornConjecture

private lemma select_unit_mass {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) (hs : 1 ≤ ∑ i ∈ s, f i) :
    ∃ t ⊆ s, 1 ≤ ∑ i ∈ t, f i ∧ ∑ i ∈ t, f i ≤ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num at hs
  | @insert a s ha ih =>
    by_cases h : 1 ≤ ∑ i ∈ s, f i
    · obtain ⟨t,ht,h₁,h₂⟩ := ih (fun i hi => hf i (mem_insert_of_mem hi)) h
      exact ⟨t,ht.trans (subset_insert ..),h₁,h₂⟩
    · refine ⟨insert a s,Subset.rfl,hs,?_⟩
      rw [sum_insert ha]
      linarith [(hf a (mem_insert_self ..)).2]

private lemma euler_inv_bound {q : ℕ} (hp : q.Prime) :
    (1-1/(q:ℝ))⁻¹ ≤ exp (2*(q:ℝ)⁻¹) := by
  have hq : (2:ℝ) ≤ q := by exact_mod_cast hp.two_le
  have hq0 : 0 < (q:ℝ) := by positivity
  have hpos : 0 < 1-1/(q:ℝ) := by apply sub_pos.mpr; apply (div_lt_one hq0).mpr; linarith
  apply le_trans _ (Real.add_one_le_exp _)
  rw [inv_le_iff_one_le_mul₀ hpos]
  field_simp
  nlinarith

/-- A fixed polynomial range of primes supplies between one and two units of
reciprocal mass with all k forbidden residues distinct, uniformly for large k. -/
theorem chain_full_root_band :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ᶠ k : ℕ in atTop, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, q.Prime ∧ k^2 < q ∧ q ≤ k^A ∧ OmegaP (chainForms 1 k) q=k) ∧
      1 ≤ ∑ q ∈ Q, (q:ℝ)⁻¹ ∧ ∑ q ∈ Q, (q:ℝ)⁻¹ ≤ 2 := by
  classical
  obtain ⟨a,ha⟩ := exists_nat_gt (4*exp 6*exp 4)
  let A := a+2
  refine ⟨A,by dsimp [A]; omega,?_⟩
  obtain ⟨m,hm⟩ := eventually_atTop.mp prime_euler_product_log_bounds
  filter_upwards [eventually_ge_atTop (max 2 m)] with k hk
  have hk2 : 2 ≤ k := le_trans (le_max_left ..) hk
  have hm' : m ≤ k := le_trans (le_max_right ..) hk
  let y := k^2
  let z := k^A
  have hky : k≤y := Nat.le_pow (by decide)
  have hyz : y≤z := Nat.pow_le_pow_right (by omega) (by dsimp [A]; omega)
  let E (n : ℕ) := ∏ p ∈ n.primesLE, (1-1/(p:ℝ))⁻¹
  have pos (n : ℕ) : 0<E n := Finset.prod_pos fun p hp => by
    have hp' : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    positivity [show 0<1-1/(p:ℝ) from sub_pos.mpr ((div_lt_one (by linarith)).mpr hp')]
  have hL := (hm y (le_trans hm' hky)).2
  have hU := (hm z (le_trans hm' (hky.trans hyz))).1
  change E y ≤ _ at hL
  change _ ≤ E z at hU
  have hklog := log_natCast_nonneg k
  have hratio : exp 6 * E y ≤ E z := calc
    _ ≤ exp 6 * ((2*exp 4)*log (y:ℝ)) := by gcongr
    _ ≤ log (z:ℝ) := by
      simp only [y,z,Nat.cast_pow,Real.log_pow]
      have hA : 4*exp 6*exp 4 ≤ (A:ℝ) := by dsimp [A]; push_cast; linarith
      norm_num only [Nat.cast_ofNat]
      calc
        _ = (4*exp 6*exp 4)*log (k:ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hA hklog
    _ ≤ log ((z:ℝ)+1) := log_le_log (by dsimp [z]; positivity) (by linarith)
    _ ≤ _ := hU
  let band := z.primesLE \ y.primesLE
  have hsub : y.primesLE ⊆ z.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hyz,Nat.prime_of_mem_primesLE hp⟩
  have hband (q : ℕ) (hq : q ∈ band) : q.Prime ∧ y<q ∧ q≤z := by
    obtain ⟨hz,hy⟩ := mem_sdiff.mp hq
    obtain ⟨hle,hp⟩ := Nat.mem_primesLE.mp hz
    exact ⟨hp,lt_of_not_ge (fun e => hy (Nat.mem_primesLE.mpr ⟨e,hp⟩)),hle⟩
  have hmass : 3 ≤ ∑ q ∈ band, (q:ℝ)⁻¹ := by
    have hprod : exp 6 ≤ ∏ p ∈ band, (1-1/(p:ℝ))⁻¹ := by
      apply le_of_mul_le_mul_right (a:=E y) _ (pos y)
      simpa only [E,band,prod_sdiff hsub] using hratio
    have hh : (∏ p ∈ band, (1-1/(p:ℝ))⁻¹) ≤ exp (2*∑ q ∈ band, (q:ℝ)⁻¹) := by
      rw [mul_sum,exp_sum]
      apply Finset.prod_le_prod
      · intro p hp
        have hp' : (1:ℝ)<p := by exact_mod_cast (hband p hp).1.one_lt
        exact inv_nonneg.mpr (sub_nonneg.mpr ((div_le_one (by linarith)).mpr hp'.le))
      · exact fun p hp => euler_inv_bound (hband p hp).1
    linarith [Real.exp_le_exp.mp (hprod.trans hh)]
  let bad := band.filter fun q => OmegaP (chainForms 1 k) q < k
  have hbad := chainForms_exceptional_reciprocal hk2 bad (by
    intro q hq
    obtain ⟨hm,hc⟩ := mem_filter.mp hq
    exact ⟨(hband _ hm).1,(hband _ hm).2.1,hc⟩)
  have sub : bad ⊆ band := filter_subset ..
  have split := sum_sdiff (f:=fun q : ℕ => (q:ℝ)⁻¹) sub
  obtain ⟨Q,hQ,h₁,h₂⟩ := select_unit_mass (band \ bad) (fun q : ℕ => (q:ℝ)⁻¹) (by
    intro q hq
    have hp := (hband q (mem_sdiff.mp hq).1).1
    exact ⟨by positivity,inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)⟩) (by linarith)
  refine ⟨Q,?_,h₁,h₂⟩
  intro q hq
  obtain ⟨hqb,hne⟩ := mem_sdiff.mp (hQ hq)
  obtain ⟨hp,hlo,hhi⟩ := hband q hqb
  have hcard : k ≤ OmegaP (chainForms 1 k) q :=
    le_of_not_gt fun hlt => hne (mem_filter.mpr ⟨hqb,hlt⟩)
  let : Fact q.Prime := ⟨hp⟩
  have hq2 : 2<q := by dsimp [y] at hlo; nlinarith
  rw [chainForms_omega_odd k q hq2] at hcard ⊢
  exact ⟨hp,hlo,hhi,le_antisymm (min_le_left ..) hcard⟩

private noncomputable def prefixResidues (b : Bool) (k q : ℕ) : Finset (ZMod q) := by
  classical
  by_cases h : q=0
  · exact ∅
  · let : NeZero q := ⟨h⟩
    exact univ.filter fun z => ∃ f ∈ chainForms (if b then 1 else -1) k,
      (f.map (Int.castRingHom (ZMod q))).eval z=0

private lemma prefixResidues_card (b : Bool) (k q : ℕ) (hq : q.Prime) :
    (prefixResidues b k q).card=OmegaP (chainForms 1 k) q := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  have he : (prefixResidues b k q).card=OmegaP (chainForms (if b then 1 else -1) k) q := by
    rw [OmegaP,Set.ncard_eq_toFinset_card]
    congr 1
    ext x
    simp [prefixResidues,hq.ne_zero]
  cases b
  · exact he.trans (chainForms_omega_neg 1 k q).symm
  · exact he

private lemma prefix_residue_avoid (b : Bool) {p k q : ℕ} (hq : q.Prime) (hqp : q<p)
    (h : ∀ i<k, ((if b then firstKindTerm else secondKindTerm) p i).Prime) :
    (p:ZMod q) ∉ prefixResidues b k q := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  let s : ℤ := if b then 1 else -1
  let t := (if b then firstKindTerm else secondKindTerm) p
  have ge (i : ℕ) : p≤t i := by
    induction i with
    | zero => cases b <;> rfl
    | succ i ih =>
      cases b
      · change p≤2*secondKindTerm p i-1
        change p ≤ secondKindTerm p i at ih
        omega
      · change p≤2*firstKindTerm p i+1
        change p≤firstKindTerm p i at ih
        omega
  have term (i : ℕ) : (t i:ZMod q)=2^i*(p:ZMod q)+(s:ZMod q)*(2^i-1) := by
    induction i with
    | zero => cases b <;> simp [t,firstKindTerm,secondKindTerm]
    | succ i ih =>
      have hg := ge i
      cases b
      · change ((2*secondKindTerm p i-1:ℕ):ZMod q)=_
        change p ≤ secondKindTerm p i at hg
        rw [Nat.cast_sub (by omega)]
        push_cast
        change (secondKindTerm p i:ZMod q)=_ at ih
        rw [ih]
        simp [s,pow_succ]; ring
      · change ((2*firstKindTerm p i+1:ℕ):ZMod q)=_
        push_cast
        change (firstKindTerm p i:ZMod q)=_ at ih
        rw [ih]
        simp [s,pow_succ]; ring
  intro he
  simp only [prefixResidues,dif_neg hq.ne_zero,mem_filter,mem_univ,true_and] at he
  obtain ⟨f,hf,he⟩ := he
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hf
  change (((Polynomial.C ((2:ℤ)^i)*Polynomial.X+Polynomial.C (s*(2^i-1))).map
    (Int.castRingHom (ZMod q))).eval (p:ZMod q))=0 at he
  have hz : (t i:ZMod q)=0 := by rw [term]; simpa using he
  exact (hqp.trans_le (ge i)).ne ((Nat.prime_dvd_prime_iff_eq hq (h i (mem_range.mp hi))).mp
    ((ZMod.natCast_eq_zero_iff ..).mp hz))

private lemma sieve_trunc_error (Q : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q)) (m k : ℕ)
    (hb : ∀ q ∈ Q, (B q).card=k) :
    (∑ j ∈ range (m+1), ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, ((B q).card:ℝ)) ≤
      (m+1:ℕ)*(1+(k:ℝ)*Q.card)^m := by
  have prodEq (j : ℕ) (T : Finset ℕ) (hT : T ∈ Q.powersetCard j) :
      (∏ q ∈ T, ((B q).card:ℝ))=(k:ℝ)^j := by
    obtain ⟨ht,hc⟩ := mem_powersetCard.mp hT
    simpa only [prod_const,hc] using prod_congr (s₁:=T) (s₂:=T) rfl
      (g:=fun _ => (k:ℝ)) (fun q hq => (by exact_mod_cast hb q (ht hq) : ((B q).card:ℝ)=k))
  calc
    _ ≤ ∑ _j ∈ range (m+1), (1+(k:ℝ)*Q.card)^m := by
      apply sum_le_sum
      intro j hj
      rw [sum_congr rfl (prodEq j),sum_const,nsmul_eq_mul,card_powersetCard]
      have hh : (Q.card.choose j:ℝ) ≤ (Q.card:ℝ)^j := by exact_mod_cast Nat.choose_le_pow Q.card j
      calc
        _ ≤ (Q.card:ℝ)^j*(k:ℝ)^j := by gcongr
        _ = ((k:ℝ)*Q.card)^j := by ring
        _ ≤ (1+(k:ℝ)*Q.card)^j := by gcongr; linarith
        _ ≤ _ := pow_le_pow_right₀ (by linarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (Nat.cast_nonneg (α:=ℝ) Q.card)]) (by simpa using mem_range.mp hj)
    _ = _ := by simp

private lemma sieve_mass_bounds (Q : Finset ℕ) (u : ℕ → ℝ) (j : ℕ)
    (hu : ∀ q ∈ Q, 0≤u q ∧ u q≤1) :
    (∏ q ∈ Q, (1-u q)) ≤ exp (-∑ q ∈ Q, u q) ∧
    (2:ℝ)^j*(∑ T ∈ Q.powersetCard j, ∏ q ∈ T, u q) ≤ exp (2*∑ q ∈ Q, u q) := by
  constructor
  · rw [←sum_neg_distrib,exp_sum]
    exact prod_le_prod (fun q hq => sub_nonneg.mpr (hu q hq).2)
      (fun q _ => by linarith [Real.add_one_le_exp (-u q)])
  · rw [mul_sum]
    calc
      _ = ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, (2*u q) := by
        apply sum_congr rfl
        intro T hT
        rw [prod_mul_distrib,prod_const,(mem_powersetCard.mp hT).2]
      _ ≤ ∑ T ∈ Q.powerset, ∏ q ∈ T, (2*u q) :=
        sum_le_sum_of_subset_of_nonneg (fun T hT => mem_powerset.mpr (mem_powersetCard.mp hT).1)
          (fun T hT _ => prod_nonneg fun q hq => mul_nonneg (by norm_num) (hu q (mem_powerset.mp hT hq)).1)
      _ = ∏ q ∈ Q, (1+2*u q) := (prod_one_add _).symm
      _ ≤ ∏ q ∈ Q, exp (2*u q) := prod_le_prod (fun q hq => by linarith [(hu q hq).1])
          (fun q _ => by linarith [Real.add_one_le_exp (2*u q)])
      _ = _ := by rw [mul_sum,exp_sum]


private lemma band_sieve_count (b : Bool) (N z k : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ z ∧ OmegaP (chainForms 1 k) q=k)
    (h₁ : 1 ≤ ∑ q ∈ Q, (q:ℝ)⁻¹) (h₂ : ∑ q ∈ Q, (q:ℝ)⁻¹ ≤ 2) :
    (primePrefixSeedCount b k N : ℝ) ≤ (z+1:ℕ)+2*(N+1:ℕ)*exp (-(k:ℝ))+
      (16*k+1:ℕ)*(1+(k:ℝ)*(z+1:ℕ))^(16*k) := by
  classical
  let B := prefixResidues b k
  let u (q : ℕ) := ((B q).card:ℝ)/q
  let F := (range (N+1)).filter fun x => ∀ q ∈ Q, (x:ZMod q) ∉ B q
  have split : primePrefixSeedCount b k N ≤ z+1+F.card := by
    unfold primePrefixSeedCount
    rw [Nat.floor_natCast]
    apply le_trans (card_le_card (t:=range (z+1) ∪ F) ?_)
    · simpa using card_union_le (range (z+1)) F
    intro x hx
    obtain ⟨hx,hp⟩ := mem_filter.mp hx
    by_cases hsmall : x≤z
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,fun q hq =>
        prefix_residue_avoid b (hQ q hq).1 (by have := (hQ q hq).2.1; omega) hp⟩)
  have hb (q : ℕ) (hq : q∈Q) : (B q).card=k :=
    (prefixResidues_card b k q (hQ q hq).1).trans (hQ q hq).2.2
  have hu (q : ℕ) (hq : q∈Q) : 0≤u q ∧ u q≤1 := by
    let : NeZero q := ⟨(hQ q hq).1.ne_zero⟩
    have hle : (B q).card≤q := by simpa only [ZMod.card] using card_le_univ (B q)
    exact ⟨by dsimp [u]; positivity, (div_le_one (by exact_mod_cast (hQ q hq).1.pos)).mpr (by exact_mod_cast hle)⟩
  have hsum : ∑ q ∈ Q, u q=(k:ℝ)*∑ q ∈ Q, (q:ℝ)⁻¹ := by
    rw [mul_sum]
    exact sum_congr rfl (fun q hq => by simp [u,hb q hq,div_eq_mul_inv])
  have mass := sieve_mass_bounds Q u (2*(8*k)+1) hu
  have small : (∏ q ∈ Q, (1-u q)) ≤ exp (-(k:ℝ)) := by
    apply mass.1.trans
    rw [exp_le_exp,hsum]
    nlinarith [mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg (α:=ℝ) k)]
  have tail : (∑ T ∈ Q.powersetCard (2*(8*k)+1), ∏ q ∈ T, u q) ≤ exp (-(k:ℝ)) := by
    apply le_of_mul_le_mul_left (a:=(2:ℝ)^(2*(8*k)+1)) _ (by positivity)
    apply mass.2.trans
    have he : exp (2*∑ q ∈ Q, u q) ≤ exp (4*(k:ℝ)) := by
      rw [exp_le_exp,hsum]
      nlinarith [mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α:=ℝ) k)]
    apply he.trans
    rw [←exp_log (by positivity : 0 < (2:ℝ)^(2*(8*k)+1)),←exp_add,Real.exp_le_exp,log_pow]
    push_cast
    nlinarith [Real.log_two_gt_d9,mul_le_mul_of_nonneg_right Real.log_two_gt_d9.le (Nat.cast_nonneg (α:=ℝ) k)]
  have err := sieve_trunc_error Q B (2*(8*k)) k hb
  have h := brun_upper_residue_count (N+1) Q (fun q hq => (hQ q hq).1) B (8*k)
  have hsb : Q.card ≤ z+1 := by
    simpa using card_le_card (t:=range (z+1)) (fun q hq => mem_range.mpr (by have := (hQ q hq).2.1; omega))
  have hf : (F.card:ℝ) ≤ (N+1:ℕ)*(exp (-(k:ℝ))+exp (-(k:ℝ))) +
        (16*k+1:ℕ)*(1+(k:ℝ)*(z+1:ℕ))^(16*k) := by
    apply h.trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (add_le_add small tail) (by positivity)
    · apply err.trans
      rw [show 2*(8*k)=16*k by omega]
      gcongr
  have hsplit : (primePrefixSeedCount b k N:ℝ) ≤ (z+1:ℕ)+(F.card:ℝ) := by exact_mod_cast split
  linarith


/-- An exponential bound uniform in the chain length and valid for both signs.
The absolute constant in the seed cutoff is independent of k and of the sign. -/
theorem primePrefixSeedCount_uniform_exponential :
    ∃ C : ℕ, 0<C ∧ ∀ᶠ k : ℕ in atTop, ∀ (b : Bool) (N : ℕ), (k+1)^(C*k) ≤ N →
      (primePrefixSeedCount b k N : ℝ) ≤ 4*(N+1:ℕ)*exp (-(k:ℝ)) := by
  obtain ⟨A,hA,hband⟩ := chain_full_root_band
  let D := 16*(A+2)+1
  refine ⟨D+1,by positivity,?_⟩
  filter_upwards [hband,eventually_ge_atTop 16] with k hQ hk
  obtain ⟨Q,hQ,h₁,h₂⟩ := hQ
  intro b N hN
  have hb := band_sieve_count b N (k^A) k Q (fun q hq =>
    ⟨(hQ q hq).1,(hQ q hq).2.2.1,(hQ q hq).2.2.2⟩) h₁ h₂
  let s := k+1
  have hs : 1≤ s := by dsimp [s]; omega
  have hpow (n : ℕ) : 1 ≤ s^n := Nat.one_le_pow _ _ (by omega)
  have hz : k^A+1 ≤ s^(A+1) := by
    have hka : k^A ≤ s^A := Nat.pow_le_pow_left (by dsimp [s]; omega) _
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_left (s^A) (show 2≤ s by dsimp [s]; omega),hpow A]
  have hbase : 1+k*(k^A+1) ≤ s^(A+2) := by
    rw [show A+2=A+1+1 by omega,pow_succ]
    have := Nat.mul_le_mul_left k hz
    have := hpow (A+1)
    dsimp [s] at *
    nlinarith
  have hlin : 16*k+1 ≤ s^k := by
    apply le_trans _ (Nat.pow_le_pow_right hs (show 2≤k by omega))
    dsimp [s]; nlinarith [Nat.mul_le_mul_right k hk]
  have herr : (16*k+1)*(1+k*(k^A+1))^(16*k) ≤ s^(D*k) := calc
    _ ≤ s^k*(s^(A+2))^(16*k) := Nat.mul_le_mul hlin (Nat.pow_le_pow_left hbase _)
    _ = _ := by rw [←pow_mul,←pow_add]; congr 1; dsimp [D]; ring
  have hseed : k^A+1 ≤ s^(D*k) := by
    apply hz.trans
    apply Nat.pow_le_pow_right hs
    dsimp [D]
    nlinarith [Nat.mul_le_mul_left (16*(A+2)+1) (show 1≤k by omega)]
  have hexp : exp (k:ℝ) ≤ (s^k:ℕ) := by
    have hm : exp 1 ≤ (s:ℝ) := le_trans Real.exp_one_lt_three.le (by exact_mod_cast (show 3≤ s by dsimp [s]; omega))
    simpa only [←exp_nat_mul,Nat.cast_pow,mul_one] using pow_le_pow_left₀ (exp_pos 1).le hm k
  have hd : ((s^(D*k):ℕ):ℝ) ≤ (N+1:ℕ)*exp (-(k:ℝ)) := by
    rw [exp_neg,←div_eq_mul_inv]
    apply (le_div_iff₀ (exp_pos _)).mpr
    calc
      _ ≤ ((s^(D*k):ℕ):ℝ)*(s^k:ℕ) := by gcongr
      _ ≤ ((N+1:ℕ):ℝ) := by
        exact_mod_cast (show s^(D*k)*s^k≤N+1 by
          rw [←pow_add,←Nat.succ_mul]
          exact hN.trans (Nat.le_succ _))
  have hs' : (k^A+1:ℕ) ≤ ((N+1:ℕ):ℝ)*exp (-(k:ℝ)) := (by exact_mod_cast hseed : ((k^A+1:ℕ):ℝ)≤(s^(D*k):ℕ)).trans hd
  have he' : ((16*k+1:ℕ):ℝ)*(1+(k:ℝ)*(k^A+1:ℕ))^(16*k) ≤ (N+1:ℕ)*exp (-(k:ℝ)) :=
    (by exact_mod_cast herr : ((16*k+1:ℕ):ℝ)*(1+(k:ℝ)*(k^A+1:ℕ))^(16*k) ≤ (s^(D*k):ℕ)).trans hd
  linarith

#print axioms primePrefixSeedCount_uniform_exponential


private lemma prefix_antitone (b : Bool) (x : ℝ) {a k : ℕ} (ha : a≤k) :
    primePrefixSeedCount b k x ≤ primePrefixSeedCount b a x := by
  classical
  apply card_le_card
  intro p hp
  obtain ⟨hp,h⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp,fun i hi => h i (hi.trans_le ha)⟩

private lemma exact_le_prefix (b : Bool) (x : ℝ) (k : ℕ) :
    exactChainCount (if b then IsFirstKindChainOfLength else IsSecondKindChainOfLength) k x ≤
    primePrefixSeedCount b k x := by
  classical
  apply card_le_card
  intro p hp
  apply mem_filter.mpr
  cases b <;> exact ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.2.1⟩

/-- Outside a set with stretched exponential saving, the prefix length is
below an absolute multiple of log N / log log N. The same bound applies to
the exact-length predicates with Jones's nonprime stopping term. -/
theorem long_prefix_seed_exceptional_bound :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, ∀ (b : Bool) (l : ℕ),
      let L := c*log N/log (log N)
      L ≤ l → (primePrefixSeedCount b l N : ℝ) ≤ 4*(N+1:ℕ)*exp (-L/2) ∧
        (exactChainCount (if b then IsFirstKindChainOfLength else IsSecondKindChainOfLength)
          l N : ℝ) ≤ 4*(N+1:ℕ)*exp (-L/2) := by
  obtain ⟨C,hC,H⟩ := primePrefixSeedCount_uniform_exponential
  obtain ⟨m,hm⟩ := eventually_atTop.mp H
  let c := 1/(2*(C:ℝ))
  have hc : 0<c := by dsimp [c]; positivity
  have hcC : c*C=1/2 := by dsimp [c]; field_simp
  have hc2 : c≤1/2 := by
    dsimp [c]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 2≤2*C))
  refine ⟨c,hc,?_⟩
  let x (N : ℕ) := log N
  have hX : Tendsto x atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog := (isLittleO_log_id_atTop.def (show 0<c/(m+2:ℕ) by positivity))
  filter_upwards [hX.eventually hlog, (tendsto_log_atTop.comp hX).eventually_ge_atTop 1,
    hX.eventually_ge_atTop 2,eventually_gt_atTop 0] with N hslow hlg hx hN
  change 1 ≤ log (x N) at hlg
  have hy : 0<log (x N) := by linarith
  have hx0 : 0≤x N := by linarith
  simp only [id_eq,Real.norm_eq_abs,abs_of_nonneg hx0,abs_of_pos hy] at hslow
  let L := c*x N/log (x N)
  have hmL : (m+2:ℕ)≤L := by
    apply (le_div_iff₀ hy).mpr
    have he : ((m+2:ℕ):ℝ)*((c/(m+2:ℕ))*x N)=c*x N := by field_simp
    linarith [mul_le_mul_of_nonneg_left hslow (Nat.cast_nonneg (α:=ℝ) (m+2))]
  let k := ⌊L⌋₊
  have hL : 0≤L := by dsimp [L]; positivity
  have hk1 : m≤k := Nat.le_floor ((by exact_mod_cast (Nat.le_add_right m 2) : (m:ℝ) ≤ (m+2:ℕ)).trans hmL)
  have hk2 : (k:ℝ) ≤ L := Nat.floor_le hL
  have hhalf : L/2 ≤ k := by
    have := Nat.lt_floor_add_one L
    have h2 : (2:ℝ)≤L := le_trans (by exact_mod_cast (by omega : 2 ≤ m+2)) hmL
    change L/2 ≤ (⌊L⌋₊:ℝ)
    linarith
  have hLsmall : L≤x N/2 := by
    apply (div_le_iff₀ hy).mpr
    nlinarith [mul_le_mul_of_nonneg_right hc2 hx0,mul_le_mul_of_nonneg_right hlg hx0]
  have hkplus : ((k+1:ℕ):ℝ)≤x N := by push_cast; linarith
  have hklog := log_le_log (show 0<((k+1:ℕ):ℝ) by positivity) hkplus
  have hcut : (k+1)^(C*k)≤N := by
    have he : (L*log (x N))*(C:ℝ)=x N/2 := by
      dsimp [L]
      rw [div_mul_cancel₀ _ hy.ne']
      linear_combination (x N)*hcC
    have hprod : (C:ℝ)*k*log ((k+1:ℕ):ℝ) ≤ x N := by
      have h₁ := mul_le_mul_of_nonneg_left hklog (mul_nonneg (Nat.cast_nonneg (α:=ℝ) C) (Nat.cast_nonneg (α:=ℝ) k))
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 (Nat.cast_nonneg (α:=ℝ) C)) hy.le]
    have hn := (log_le_log_iff (x:=(((k+1)^(C*k):ℕ):ℝ)) (y:=(N:ℝ)) (by positivity)
      (by exact_mod_cast hN)).mp (by simpa only [Nat.cast_pow,log_pow,Nat.cast_mul] using hprod)
    exact_mod_cast hn
  intro b l
  dsimp only
  intro hl
  change L≤(l:ℝ) at hl
  have hkl : k≤l := by exact_mod_cast hk2.trans hl
  have h := (by exact_mod_cast prefix_antitone b (N:ℝ) hkl :
      (primePrefixSeedCount b l N:ℝ) ≤ primePrefixSeedCount b k N).trans (hm k hk1 b N hcut)
  have hbound : (primePrefixSeedCount b l N:ℝ) ≤ 4*(N+1:ℕ)*exp (-L/2) := by
    apply h.trans
    gcongr
    linarith
  exact ⟨hbound,(by exact_mod_cast exact_le_prefix b (N:ℝ) l :
    (exactChainCount (if b then IsFirstKindChainOfLength else IsSecondKindChainOfLength) l N:ℝ) ≤
    primePrefixSeedCount b l N).trans hbound⟩

#print axioms long_prefix_seed_exceptional_bound

#print axioms chain_full_root_band

end CunninghamChain
