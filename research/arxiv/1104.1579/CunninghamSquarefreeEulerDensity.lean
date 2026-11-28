import research.arxiv.«1104.1579».CunninghamSquarefreeLocalFactors
import research.arxiv.«1104.1579».CunninghamSquarefreePrimeMass

/-! # Squarefree Cunningham prefix products at prime seeds -/

namespace CunninghamChain.SquarefreeDensity
open Finset Filter Topology PrimeMass SquarefreeSeeds

/-- The running product includes the seed and ends at site k−1. -/
def prefixProduct (first : Bool) (p k : ℕ) : ℕ := ∏ i ∈ range k, term first p i

private theorem prefix_modEq (first : Bool) {m a b : ℕ} (ha : 0<a) (hb : 0<b)
    (h : a ≡ b [MOD m]) (k : ℕ) : prefixProduct first a k ≡ prefixProduct first b k [MOD m] := by
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  simp only [prefixProduct,Nat.cast_prod]
  exact prod_congr rfl fun i _ => by rw [cast_term first ha,cast_term first hb,
    (ZMod.natCast_eq_natCast_iff ..).mpr h]

private def reduced (m : ℕ) : Finset ℕ := (range m).filter (m.Coprime ·)

private def goodResidues (first : Bool) (q k : ℕ) : Finset (ZMod (q^2)) :=
  ((reduced (q^2)) \ badResidues first q k).image Nat.cast

private theorem mem_reduced {q x : ℕ} (hq : q.Prime) :
    x ∈ reduced (q^2) ↔ x < q^2 ∧ ¬q ∣ x := by
  simp [reduced,Nat.coprime_pow_left_iff (by decide : 0<2),hq.coprime_iff_not_dvd]

private theorem bad_subset (first : Bool) {q k : ℕ} (hq : q.Prime) :
    badResidues first q k ⊆ reduced (q^2) := by
  intro x hx
  obtain ⟨hr,hd,_⟩ := mem_filter.mp hx
  exact (mem_reduced hq).mpr ⟨mem_range.mp hr,hd⟩

private theorem good_card (first : Bool) {q : ℕ} (hq : q.Prime) (k : ℕ) :
    (goodResidues first q k).card = (q^2).totient - (badResidues first q k).card := by
  rw [goodResidues,card_image_of_injOn,card_sdiff_of_subset (bad_subset first hq)]
  · rfl
  · intro x hx y hy he
    exact ((ZMod.natCast_eq_natCast_iff ..).mp he).eq_of_lt_of_lt
      ((mem_reduced hq).mp (Finset.mem_sdiff.mp hx).1).1 ((mem_reduced hq).mp (Finset.mem_sdiff.mp hy).1).1

private theorem mem_good (first : Bool) {p q : ℕ} (hq : q.Prime) (k : ℕ) :
    (p : ZMod (q^2)) ∈ goodResidues first q k ↔ ¬q ∣ p ∧ ¬q^2 ∣ prefixProduct first p k := by
  rw [goodResidues,mem_image]
  have mod_mem (x : ℕ) (he : x ≡ p [MOD q^2]) (hx : x < q^2) :
      x ∈ reduced (q^2) \ badResidues first q k ↔ ¬q ∣ p ∧ ¬q^2 ∣ prefixProduct first p k := by
    have hd := he.dvd_iff (dvd_pow_self q (by decide : 2≠0))
    by_cases hp : q ∣ p
    · simp [mem_reduced hq,hd,hp]
    · have hx' : ¬q ∣ x := fun hz => hp (hd.mp hz)
      have hposx : 0<x := Nat.pos_of_ne_zero (fun h => hx' (h ▸ dvd_zero q))
      have hposp : 0<p := Nat.pos_of_ne_zero (fun h => hp (h ▸ dvd_zero q))
      have hc := (prefix_modEq first hposx hposp he k).dvd_iff (dvd_refl (q^2))
      simpa [mem_reduced hq,badResidues,hx,hx',hp,prefixProduct] using! (show (¬q^2 ∣ prefixProduct first x k) ↔ ¬q^2 ∣ prefixProduct first p k from not_congr hc)
  constructor
  · rintro ⟨x,hx,he⟩
    exact (mod_mem x ((ZMod.natCast_eq_natCast_iff ..).mp he)
      ((mem_reduced hq).mp (Finset.mem_sdiff.mp hx).1).1).mp hx
  · intro h
    have he := Nat.mod_modEq p (q^2)
    exact ⟨p%(q^2),(mod_mem _ he (Nat.mod_lt _ (pow_pos hq.pos _))).mpr h,
      (ZMod.natCast_eq_natCast_iff ..).mpr he⟩

/-- The local proportion is measured among reduced classes modulo q². -/
noncomputable def localFactor (first : Bool) (q k : ℕ) : ℝ :=
  ((q^2).totient - (badResidues first q k).card : ℕ)/( (q^2).totient : ℝ)

/-- Exact finite sieve among prime seeds. Removing the primes dividing the
modulus makes the reduced-residue restriction literal. -/
theorem finite_prefix_mass (first : Bool) (Q : Finset ℕ) (hq : ∀ q ∈ Q, q.Prime) (k : ℕ) :
    HasPrimeMass {p : ℕ | ∀ q ∈ Q, ¬q ∣ p ∧ ¬q^2 ∣ prefixProduct first p k}
      (∏ q ∈ Q, localFactor first q k) := by
  classical
  let m (q : Q) := q.val^2
  have hpos (q : Q) := pow_pos (hq q q.prop).pos 2
  have hcop : Pairwise fun i j : Q => (m i).Coprime (m j) := fun i j hij =>
    (((Nat.coprime_primes (hq i i.prop) (hq j j.prop)).mpr (Subtype.val_injective.ne hij)).pow_left 2).pow_right 2
  have hu (q : Q) (a : ZMod (m q)) (ha : a ∈ goodResidues first q k) : IsUnit a := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    exact (ZMod.isUnit_iff_coprime ..).mpr (mem_filter.mp (Finset.mem_sdiff.mp hx).1).2.symm
  have h := finite_crt_mass m hpos hcop (fun q => goodResidues first q k) hu
  have hset : {p : ℕ | ∀ q : Q, (p : ZMod (m q)) ∈ goodResidues first q k} =
      {p : ℕ | ∀ q ∈ Q, ¬q ∣ p ∧ ¬q^2 ∣ prefixProduct first p k} := by
    ext p
    exact ⟨fun hh q hmem => (mem_good first (hq q hmem) k).mp (hh ⟨q,hmem⟩),
      fun hh q => (mem_good first (hq q q.prop) k).mpr (hh q q.prop)⟩
  rw [hset] at h
  rw [←prod_attach Q (fun q => localFactor first q k)]
  have hcard (q : Q) := good_card first (hq q q.prop) k
  simpa only [m,hcard,localFactor,univ_eq_attach] using h

theorem localFactor_two (first : Bool) (k : ℕ) : localFactor first 2 k = 1 := by
  norm_num [localFactor,badResidues_two,Nat.totient_prime_pow_succ Nat.prime_two 1]

private theorem order_two_le {q : ℕ} (hq : q.Prime) (h2 : 2<q) :
    orderOf (2 : ZMod q) ≤ q-1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hn : (2 : ZMod q) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) h2)
  exact Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hn))

private theorem order_two_large {q : ℕ} (hq : q.Prime) (h2 : 2<q) {k : ℕ} (hbig : 2^k<q) :
    k < orderOf (2 : ZMod q) := by
  let : Fact q.Prime := ⟨hq⟩
  let d := orderOf (2 : ZMod q)
  have hfin : (2 : ZMod q)^(q-1)=1 := ZMod.pow_card_sub_one_eq_one (by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) h2))
  have hd : 0 < d := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨q-1,by omega,hfin⟩)
  by_contra! h
  have hl := (Nat.pow_le_pow_right (by decide : 0<2) h).trans_lt hbig
  have he : 2^d ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff ..).mp (by
    push_cast; exact pow_orderOf_eq_one _)
  exact (one_lt_pow₀ (by decide : 1<(2:ℕ)) hd.ne').ne' (he.eq_of_lt_of_lt hl hq.one_lt)

/-- Away from every possible return in the prefix, each noninitial site
removes exactly one reduced residue modulo the prime square. -/
theorem localFactor_large (first : Bool) {q k : ℕ} (hq : q.Prime) (h2 : 2<q) (hbig : 2^k<q) :
    localFactor first q k = 1 - (k-1 : ℕ)/((q : ℝ)*(q-1 : ℕ)) := by
  let : Fact q.Prime := ⟨hq⟩
  have hd := order_two_large hq h2 hbig
  have bad := card_badResidues_odd first h2 k
  simp [min_eq_left hd.le,Nat.sub_eq_zero_of_le hd.le] at bad
  have ht : (q^2).totient = q*(q-1) := by
    simpa using Nat.totient_prime_pow_succ hq 1
  have leCount : (badResidues first q k).card ≤ (q^2).totient :=
    card_le_card (bad_subset first hq)
  have hp : (0 : ℝ) < (q : ℝ)*(q-1 : ℕ) := by exact_mod_cast Nat.mul_pos hq.pos (by omega : 0<q-1)
  rw [localFactor,Nat.cast_sub leCount,bad,ht,Nat.cast_mul,sub_div,div_self hp.ne']

theorem localFactor_pos (first : Bool) {q : ℕ} (hq : q.Prime) (k : ℕ) : 0 < localFactor first q k := by
  rcases hq.eq_two_or_odd with rfl|ho
  · rw [localFactor_two]; norm_num
  let : Fact q.Prime := ⟨hq⟩
  have h2 : 2 < q := by have := hq.two_le; omega
  let d := orderOf (2 : ZMod q)
  have hd : d ≤ q-1 := order_two_le hq h2
  have hn : min k d - 1 < q-1 := by omega
  have hb : min d (k-d) - 1 ≤ q-1 := by omega
  have hm := Nat.mul_le_mul_left (q-1) hb
  have hcount : (badResidues first q k).card < q*(q-1) := by
    rw [card_badResidues_odd first h2]
    change min k d-1+(q-1)*(min d (k-d)-1) < _
    calc
      _ < (q-1)+(q-1)*(q-1) := Nat.add_lt_add_of_lt_of_le hn hm
      _ = q*(q-1) := by rw [add_comm,←Nat.succ_mul]; congr 1; omega
  have ht : (q^2).totient = q*(q-1) := by simpa using Nat.totient_prime_pow_succ hq 1
  unfold localFactor
  apply div_pos
  · exact_mod_cast Nat.sub_pos_of_lt (ht ▸ hcount)
  · exact_mod_cast Nat.totient_pos.mpr (pow_pos hq.pos _)

theorem localFactor_same {q : ℕ} (hq : q.Prime) (k : ℕ) : localFactor false q k = localFactor true q k := by
  rcases hq.eq_two_or_odd with rfl|ho
  · simp [localFactor_two]
  let : Fact q.Prime := ⟨hq⟩
  have h2 : 2 < q := by have := hq.two_le; omega
  simp only [localFactor,card_badResidues_odd _ h2]

private noncomputable def eulerFactor (k q : ℕ) : ℝ :=
  if q.Prime then localFactor true q k else 1

/-- The common Euler product for reduced squarefree Cunningham prefix products. -/
noncomputable def prefixDensity (k : ℕ) : ℝ := Real.exp (∑' q, Real.log (eulerFactor k q))

theorem prefixDensity_pos (k : ℕ) : 0 < prefixDensity k := Real.exp_pos _

private theorem eulerFactor_pos (k q : ℕ) : 0 < eulerFactor k q := by
  unfold eulerFactor
  split_ifs with hp
  · exact localFactor_pos true hp k
  · exact zero_lt_one

private theorem summable_log_factors (k : ℕ) : Summable (fun q => Real.log (eulerFactor k q)) := by
  have hsum : Summable (fun q => eulerFactor k q - 1) := by
    apply Summable.of_norm_bounded_eventually_nat
      ((Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).mul_left (2*(k:ℝ)))
    filter_upwards [eventually_gt_atTop (2^k),eventually_gt_atTop 2] with q hbig hq
    unfold eulerFactor
    split_ifs with hp
    · rw [localFactor_large true hp hq hbig,sub_sub_cancel_left, norm_neg,Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      have hq' : (2:ℝ)<q := by exact_mod_cast hq
      have hk : ((k-1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      rw [Nat.cast_sub (by omega : 1≤q),Nat.cast_one]
      have hpos' : 0 < (q:ℝ)-1 := by linarith
      calc
        _ ≤ (k:ℝ)/(q*(q-1)) := div_le_div_of_nonneg_right hk (by positivity)
        _ ≤ _ := by
          field_simp
          nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (show 0≤(q:ℝ)-2 by linarith)]
    · simp only [sub_self,norm_zero]; positivity
  simpa using Real.summable_log_one_add_of_summable hsum

theorem tendsto_prefix_product (first : Bool) (k : ℕ) :
    Tendsto (fun L : ℕ => ∏ q ∈ L.primesLE, localFactor first q k) atTop (𝓝 (prefixDensity k)) := by
  have h := ((Real.hasProd_of_hasSum_log (eulerFactor_pos k) (summable_log_factors k).hasSum).tendsto_prod_nat).comp
    (tendsto_add_atTop_nat 1)
  apply h.congr
  intro L
  change ∏ q ∈ range (L+1), eulerFactor k q = _
  rw [Nat.primesLE_eq_filter_range,prod_filter]
  apply prod_congr rfl
  intro q _
  unfold eulerFactor
  split_ifs with hp
  · cases first <;> simp [localFactor_same hp k]
  · rfl

private def finiteSieve (first : Bool) (L k : ℕ) : Set ℕ :=
  {p | ∀ q ∈ L.primesLE, ¬q ∣ p ∧ ¬q^2 ∣ prefixProduct first p k}

private def tailSet (first : Bool) (k L : ℕ) : Set ℕ :=
  {p | ∃ i : Fin k, p ∈ SquarefreeAtPrimes.largeHits
    (fun q => root first (q^2) i.val % q^2) (2^(k+1)) L}

private theorem tail_cover (first : Bool) {L k p : ℕ} (hL : 2^k+2≤L) (hp : p.Prime)
    (hin : p ∈ finiteSieve first L k) (hb : ¬Squarefree (prefixProduct first p k)) :
    p ∈ tailSet first k L := by
  rw [Nat.squarefree_iff_prime_squarefree] at hb
  push Not at hb
  obtain ⟨q,hq,hq2⟩ := hb
  have hsq : q^2 ∣ prefixProduct first p k := by simpa [sq] using hq2
  have high : L < q := lt_of_not_ge fun h => (hin q (Nat.mem_primesLE.mpr ⟨h,hq⟩)).2 hsq
  have h2 : 2<q := by have := pow_pos (by decide : 0 < (2:ℕ)) k; omega
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨i,hi,_,hrep | ht⟩ := (square_dvd_chain_prefix_iff first h2 hp.pos k).mp hsq
  · have := order_two_large hq h2 (by omega : 2^k<q)
    omega
  · have hik := hi.trans_le (min_le_left ..)
    have hl := term_bounds first hp.pos i
    have hs : q^2 ≤ 2^(k+1)*p := calc
      q^2 ≤ term first p i := Nat.le_of_dvd hl.1 ht
      _ ≤ 2^i*(p+1) := by omega
      _ ≤ 2^k*(2*p) := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hik.le) (by have := hp.pos; omega)
      _ = _ := by rw [pow_succ]; ring
    have hodd := ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_right 2
    exact ⟨⟨i,hik⟩,q,hq,high,hs,(root_iff first hp.pos hodd i).mp ht⟩

private theorem mass_cover_two {A B C : Set ℕ} (h : ∀ p ∈ A, p.Prime → p∈B ∨ p∈C)
    {s : ℝ} (hs : 1<s) : mass A s ≤ mass B s + mass C s := by
  simpa using mass_le_cover (∅ : Finset ℕ) (fun _ => A) A B C
    (fun p hp hprime => Or.inr (h p hp hprime)) hs

/-- For both canonical recurrences, prime seeds whose first k terms have
squarefree product have normalized logarithmic Dirichlet mass equal to the
positive Euler product. -/
theorem squarefree_prefix_mass (first : Bool) (k : ℕ) :
    HasPrimeMass {p | Squarefree (prefixProduct first p k)} (prefixDensity k) := by
  let G := {p | Squarefree (prefixProduct first p k)}
  let P (L : ℕ) := ∏ q ∈ L.primesLE, localFactor first q k
  have hP := tendsto_prefix_product first k
  have hfin (L : ℕ) : HasPrimeMass (finiteSieve first L k) (P L) :=
    finite_prefix_mass first L.primesLE (fun q h => Nat.prime_of_mem_primesLE h) k
  apply tendsto_order.mpr
  constructor
  · intro c hc
    let e := (prefixDensity k-c)/3
    have he : 0<e := by dsimp [e]; linarith
    have hnear : ∀ᶠ L : ℕ in atTop, c+e<P L := hP.eventually_const_lt (by dsimp [e]; linarith)
    obtain ⟨N,hN⟩ := exists_nat_gt ((k:ℝ)*1632/e)
    obtain ⟨L,hl,hbig,hN'⟩ := (hnear.and ((eventually_ge_atTop (2^k+2)).and (eventually_ge_atTop N))).exists
    have hL : 0<L := by have := pow_pos (by decide : 0 < (2:ℕ)) k; omega
    have hC : (k:ℝ)*(1632/L)<e := by
      have hlarge := hN.trans_le (show (N:ℝ)≤L by exact_mod_cast hN')
      rw [div_lt_iff₀ he] at hlarge
      rw [←mul_div_assoc,div_lt_iff₀ (by exact_mod_cast hL : (0:ℝ)<L)]
      linarith only [hlarge]
    have bad : ∀ᶠ s : ℝ in 𝓝[>] 1, (s-1)*mass (tailSet first k L) s < e :=
      SquarefreeAtPrimes.largeHits_mass_lt _ _ L hL hC
    filter_upwards [self_mem_nhdsWithin,(hfin L).eventually_const_lt hl,bad] with s hs ha hb
    have bound := mass_cover_two (A:=finiteSieve first L k) (B:=G) (C:=tailSet first k L)
      (fun p hin hp => or_iff_not_imp_left.mpr (tail_cover first hbig hp hin)) hs
    have hm := mul_le_mul_of_nonneg_left bound (sub_nonneg.mpr (le_of_lt (show 1<s from hs)))
    change c < (s-1)*mass G s
    linarith only [hm,ha,hb]
  · intro c hc
    obtain ⟨L,hL⟩ := (hP.eventually_lt_const hc).exists
    have lim := (hfin L).add (finite_mass_tendsto (Set.finite_Iic L))
    have hlt := lim.eventually_lt_const (show P L+0<c by simpa using hL)
    filter_upwards [self_mem_nhdsWithin,hlt] with s hs hb
    have bound := mass_cover_two (A:=G) (B:=finiteSieve first L k) (C:=Set.Iic L)
      (fun p h hp => by
        by_cases hsmall : p≤L
        · exact Or.inr hsmall
        apply Or.inl
        intro q hq
        obtain ⟨hle,prime⟩ := Nat.mem_primesLE.mp hq
        refine ⟨fun hd => hsmall (((Nat.prime_dvd_prime_iff_eq prime hp).mp hd) ▸ hle),?_⟩
        simpa [sq] using (Nat.squarefree_iff_prime_squarefree.mp h q prime)) hs
    have hm := mul_le_mul_of_nonneg_left bound (sub_nonneg.mpr (le_of_lt (show 1<s from hs)))
    change (s-1)*mass G s < c
    change (s-1)*mass _ s + (s-1)*mass _ s < c at hb
    linarith only [hm,hb]

private theorem localFactor_antitone (first : Bool) (q : ℕ) :
    Antitone (localFactor first q) := by
  apply antitone_nat_of_succ_le
  intro k
  have hsub : badResidues first q k ⊆ badResidues first q (k+1) := by
    intro p h
    obtain ⟨hp,hu,hd⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨hp,hu,by rw [prod_range_succ]; exact dvd_mul_of_dvd_left hd _⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.sub_le_sub_left (card_le_card hsub) _

theorem density_succ_le (k : ℕ) : prefixDensity (k+1) ≤ prefixDensity k := by
  apply Real.exp_le_exp.mpr
  apply (summable_log_factors (k+1)).tsum_le_tsum _ (summable_log_factors k)
  intro q
  apply Real.log_le_log (eulerFactor_pos ..)
  unfold eulerFactor
  split_ifs with hq
  · exact localFactor_antitone true q (Nat.le_succ k)
  · rfl

/-- At every positive length, adjoining the next term removes positive prime mass. -/
theorem prefixDensity_succ_lt {k : ℕ} (hk : 0 < k) : prefixDensity (k+1) < prefixDensity k := by
  obtain ⟨q,hl,hq⟩ := Nat.exists_infinite_primes (2^(k+1)+3)
  have hbig : 2^(k+1)<q := by omega
  have hlk : 2^k<q := (Nat.pow_le_pow_right (by decide) (Nat.le_succ k)).trans_lt hbig
  have h2 : 2<q := by have := Nat.one_le_two_pow (n:=k+1); omega
  have hden : 0 < (q:ℝ)*(q-1 : ℕ) := by exact_mod_cast Nat.mul_pos hq.pos (by omega : 0<q-1)
  apply Real.exp_lt_exp.mpr
  apply Summable.tsum_lt_tsum (i:=q) _ _ (summable_log_factors (k+1)) (summable_log_factors k)
  · intro p
    apply Real.log_le_log (eulerFactor_pos ..)
    unfold eulerFactor
    split_ifs with hp
    · exact localFactor_antitone true p (Nat.le_succ k)
    · rfl
  · apply Real.log_lt_log (eulerFactor_pos ..)
    simp only [eulerFactor,if_pos hq,localFactor_large true hq h2 hbig,localFactor_large true hq h2 hlk]
    apply sub_lt_sub_left
    apply div_lt_div_of_pos_right _ hden
    exact_mod_cast (show k-1 < k+1-1 by omega)

theorem prefixDensity_one : prefixDensity 1 = 1 := by
  have h (q : ℕ) : eulerFactor 1 q = 1 := by
    unfold eulerFactor
    split_ifs with hp
    · rcases hp.eq_two_or_odd with rfl|ho
      · exact localFactor_two true 1
      · have hq : 2<q := by have := hp.two_le; omega
        simp [localFactor_large true hp hq (by simpa using hq : 2^1<q)]
    · rfl
  simp [prefixDensity,h]

private theorem mass_sdiff {A B : Set ℕ} (h : B ⊆ A) {a b : ℝ}
    (ha : HasPrimeMass A a) (hb : HasPrimeMass B b) : HasPrimeMass (A \ B) (a-b) := by
  apply (ha.sub hb).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1<s := hs
  have he : mass (A \ B) s = mass A s - mass B s := by
    unfold mass
    rw [←(summable_weight A hs').tsum_sub (summable_weight B hs')]
    apply tsum_congr
    intro p
    rw [←sub_div]
    congr 1
    by_cases hp : p.Prime <;> by_cases hB : p∈B
    · simp [weight,hp,hB,h hB]
    · by_cases hA : p∈A <;> simp [weight,hp,hB,hA]
    · simp [weight,hp]
    · simp [weight,hp]
  change _ = (s-1)*mass (A \ B) s
  rw [he,mul_sub]

/-- The first square obstruction occurs upon adjoining site k with the
difference of two successive Euler products as its prime mass. -/
theorem first_square_mass (first : Bool) (k : ℕ) :
    HasPrimeMass {p | Squarefree (prefixProduct first p k) ∧
      ¬Squarefree (prefixProduct first p (k+1))} (prefixDensity k - prefixDensity (k+1)) := by
  exact mass_sdiff (fun p h => Squarefree.squarefree_of_dvd (by
    change (∏ i ∈ range k, term first p i) ∣ ∏ i ∈ range (k+1), term first p i
    rw [prod_range_succ]; exact dvd_mul_right ..) h) (squarefree_prefix_mass first k)
    (squarefree_prefix_mass first (k+1))

/-- In a prefix long enough for every orbit class to recur, a reduced residue
is bad exactly when its orbit meets zero. -/
theorem localFactor_saturated (first : Bool) {q k : ℕ} [h : Fact q.Prime] (h2 : 2<q) (hk : 2*q ≤ k) :
    localFactor first q k = 1 - (orderOf (2 : ZMod q)-1 : ℕ)/(q-1 : ℕ) := by
  let d := orderOf (2 : ZMod q)
  have hd : d ≤ q-1 := order_two_le h.out h2
  have hmin : min k d = d := min_eq_right (by omega)
  have hmin' : min d (k-d) = d := min_eq_left (by omega)
  have hbad : (badResidues first q k).card = q*(d-1) := by
    rw [card_badResidues_odd first h2]
    change min k d - 1 + (q-1)*(min d (k-d)-1) = _
    rw [hmin,hmin',add_comm,←Nat.succ_mul]
    congr 1; omega
  have ht : (q^2).totient = q*(q-1) := by simpa using Nat.totient_prime_pow_succ h.out 1
  have hc : (badResidues first q k).card ≤ (q^2).totient := card_le_card (bad_subset first h.out)
  have hp : 0 < (q:ℝ)*(q-1 : ℕ) := by exact_mod_cast Nat.mul_pos h.out.pos (by omega : 0<q-1)
  rw [localFactor,Nat.cast_sub hc,hbad,ht,Nat.cast_mul,Nat.cast_mul,sub_div,div_self hp.ne']
  change 1 - (q:ℝ)*(d-1 : ℕ)/((q:ℝ)*(q-1 : ℕ)) = 1 - ((d-1 : ℕ):ℝ)/(q-1 : ℕ)
  rw [mul_div_mul_left _ _ (by exact_mod_cast h.out.ne_zero : (q:ℝ)≠0)]

/-- Dropping local factors outside a finite set gives an upper bound on the density. -/
theorem prefixDensity_le_product (k : ℕ) (Q : Finset ℕ) (hp : ∀ q∈Q,q.Prime) :
    prefixDensity k ≤ ∏ q ∈ Q,localFactor true q k := by
  apply le_of_tendsto (tendsto_prefix_product true k)
  filter_upwards [eventually_ge_atTop (Q.sup id)] with L hL
  apply Finset.prod_le_prod_of_subset_of_le_one
  · intro q hq
    exact Nat.mem_primesLE.mpr ⟨(le_sup (f:=id) hq).trans hL,hp q hq⟩
  · exact fun q hq => (localFactor_pos true (Nat.prime_of_mem_primesLE hq) k).le
  · intro q hq _
    unfold localFactor
    apply (div_le_one (by exact_mod_cast Nat.totient_pos.mpr (pow_pos (Nat.prime_of_mem_primesLE hq).pos 2))).mpr
    exact_mod_cast Nat.sub_le _ _

#print axioms localFactor_saturated
#print axioms prefixDensity_le_product
#print axioms first_square_mass
#print axioms prefixDensity_succ_lt
#print axioms prefixDensity_one
#print axioms squarefree_prefix_mass
#print axioms tendsto_prefix_product
#print axioms localFactor_large
#print axioms localFactor_pos
#print axioms localFactor_same
#print axioms finite_prefix_mass

end CunninghamChain.SquarefreeDensity
