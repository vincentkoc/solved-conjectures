import ThetaCharacterThree

/-! The quadratic character modulo seven and the signed primitive reciprocal rows. -/
namespace Arxiv.«2501.03234».ThetaCharacterSeven
open Finset ThetaCharacterThree ThetaRowCorrelations

/-- The quadratic character of conductor seven, with value zero on multiples of seven. -/
def chi7 (n : ℕ) : ℤ :=
  if n%7=0 then 0 else if n%7=1 ∨ n%7=2 ∨ n%7=4 then 1 else -1

theorem chi7_mul (a b : ℕ) : chi7 (a*b)=chi7 a*chi7 b := by
  unfold chi7
  rw [Nat.mul_mod]
  have ha := Nat.mod_lt a (by decide : 0<7)
  have hb := Nat.mod_lt b (by decide : 0<7)
  interval_cases a%7 <;> interval_cases b%7 <;> decide

private lemma chi7_le (n : ℕ) : chi7 n≤1 := by unfold chi7; split_ifs <;> decide

private lemma parity_odd_mul {p : ℕ} (hp : Odd p) (j : ℕ) : parity (p*j)=parity j := by
  simp [parity,pow_mul,hp.neg_one_pow]

section Sieve
variable {R : Type*} [CommRing R]

private def sift (f : ℕ → R) (s : Finset ℕ) (j : ℕ) : R :=
  if ∀ p∈s, ¬p∣j then f j else 0

private def siftedSum (f : ℕ → R) (s : Finset ℕ) (K : ℕ) : R := ∑ j∈range (K+1),sift f s j

private lemma prefix_insert (f : ℕ → R) {p : ℕ} (hp : Nat.Prime p) {g : R} (h : ∀ j, f (p*j)=g*f j)
    {s : Finset ℕ} (hn : p∉s) (hs : ∀ a∈s,Nat.Prime a) (K : ℕ) :
    siftedSum f (insert p s) K=siftedSum f s K-g*siftedSum f s (K/p) := by
  classical
  have H (i : ℕ) : sift f s (p*i)=g*sift f s i := by
    have hg : (∀ a∈s, ¬a∣p*i) ↔ (∀ a∈s, ¬a∣i) := by
      constructor
      · intro h a ha hai; exact h a ha (hai.trans (dvd_mul_left i p))
      · intro h a ha
        have hc : a.Coprime p := (Nat.coprime_primes (hs a ha) hp).mpr (fun e => hn (e ▸ ha))
        exact fun hai => h a ha (hc.dvd_mul_left.mp hai)
    simp only [sift,hg,h]; split_ifs <;> simp
  have ht (j : ℕ) : sift f (insert p s) j=sift f s j-(if p∣j then sift f s j else 0) := by
    simp only [sift,forall_mem_insert]; by_cases h : p∣j <;> simp [h]
  have he : (∑ j∈(range (K+1)).filter (fun j => p∣j),sift f s j) =
      ∑ i∈range (K/p+1),sift f s (p*i) := by
    symm; apply sum_bij (fun i _ => p*i)
    · intro i hi
      have h := (Nat.le_div_iff_mul_le hp.pos).mp (Nat.le_of_lt_succ (mem_range.mp hi))
      exact mem_filter.mpr ⟨mem_range.mpr (by rw [mul_comm]; omega),dvd_mul_right ..⟩
    · intro i _ j _ he; exact Nat.eq_of_mul_eq_mul_left hp.pos he
    · intro j hj; obtain ⟨h,⟨i,rfl⟩⟩ := mem_filter.mp hj
      have hc := (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa [mul_comm] using Nat.le_of_lt_succ (mem_range.mp h))
      exact ⟨i,mem_range.mpr (Nat.lt_succ_of_le hc),rfl⟩
    · intros; rfl
  unfold siftedSum
  simp_rw [ht]; rw [sum_sub_distrib,← sum_filter,he]; simp_rw [H]; rw [← mul_sum]
end Sieve

private lemma raw {d : ℕ} (ho : Odd d) (h7 : 7∣d) :
    siftedSum (fun j => parity j*chi7 j) ∅ d = -2 := by
  let f j := parity j*chi7 j
  have period (n : ℕ) : f (n+14)=f n := by simp [f,parity,chi7,pow_add,Nat.add_mod]
  have H (k) : ∀ j, f (14*k+j)=f j := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro j
      rw [show 14*(k+1)+j=(14*k+j)+14 by ring]
      exact (period _).trans (ih j)
  have hz : ∑ j∈range 14,f j=0 := by decide +kernel
  have h0 (k) : ∑ j∈range (14*k),f j=0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ,sum_range_add,ih]; simpa [H] using hz
  obtain ⟨a,ha⟩ := ho
  obtain ⟨b,hb⟩ := h7
  have hd : d+1=14*(d/14)+8 := by omega
  simp only [siftedSum,sift,notMem_empty,IsEmpty.forall_iff,implies_true,if_true]
  change ∑ j∈range (d+1),f j= -2
  rw [hd,sum_range_add,h0,zero_add]
  simp_rw [H]
  decide +kernel

private theorem parity_prefix (s : Finset ℕ) {d : ℕ} (ho : Odd d) (h7 : 7∣d)
    (hs : ∀ a∈s, Nat.Prime a ∧ a≠7 ∧ a∣d) :
    siftedSum (fun j => parity j*chi7 j) s d = -2*∏ a∈s,(1-chi7 a) := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty => simpa using raw ho h7
  | @insert p s hp ih =>
    obtain ⟨hpr,hne,hpd⟩ := hs p (mem_insert_self ..)
    have hs' (a) (ha : a∈s) := hs a (mem_insert_of_mem ha)
    have H := Nat.mul_div_cancel' hpd
    have hdiv {a : ℕ} (ha : a.Coprime p) (had : a∣d) : a∣d/p := ha.dvd_mul_left.mp (H.symm ▸ had)
    have h7' := hdiv ((Nat.coprime_primes (by decide : Nat.Prime 7) hpr).mpr hne.symm) h7
    have ho' : Odd (d/p) := ho.of_dvd_nat ⟨p,by rw [mul_comm,H]⟩
    have hf (i) : parity (p*i)*chi7 (p*i)=chi7 p*(parity i*chi7 i) := by
      rw [parity_odd_mul (ho.of_dvd_nat hpd),chi7_mul]; ring
    rw [prefix_insert _ hpr hf hp (fun a ha => (hs' a ha).1),ih ho h7 hs',
      ih ho' h7' (fun a ha => ⟨(hs' a ha).1,(hs' a ha).2.1,
        hdiv ((Nat.coprime_primes (hs' a ha).1 hpr).mpr (fun e => hp (e ▸ ha))) (hs' a ha).2.2⟩),prod_insert hp]
    ring
private lemma sieve_good {d j : ℕ} (hd : d≠0) (h : ¬7∣j) :
    j.Coprime d ↔ ∀ p∈d.primeFactors.erase 7, ¬p∣j := by
  constructor
  · intro hc p hp
    have hpr := Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2
    exact fun hpj => hpr.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpj (Nat.dvd_of_mem_primeFactors (mem_erase.mp hp).2))
  · intro hs; by_contra hn
    obtain ⟨p,hpr,hpj,hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    exact hs p (mem_erase.mpr ⟨fun he => h (he ▸ hpj),hpr.mem_primeFactors hpd hd⟩) hpj

/-- The unnormalized parity transform at conductor seven has the opposite sign
to the conductor-three transform. Its exact factor at the conductor is −2. -/
theorem parity_transform_seven {d : ℕ} (ho : Odd d) (h7 : 7∣d) :
    (∑ j∈(range d).filter (·.Coprime d), parity j*chi7 j) =
      -2*∏ p∈d.primeFactors.erase 7,(1-chi7 p) := by
  classical
  let s := d.primeFactors.erase 7
  have H := parity_prefix s ho h7 (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2,
    (mem_erase.mp hp).1,Nat.dvd_of_mem_primeFactors (mem_erase.mp hp).2⟩)
  have hz : chi7 d=0 := by simp [chi7,Nat.mod_eq_zero_of_dvd h7]
  rw [← H,siftedSum,sum_range_succ,show sift (fun j => parity j*chi7 j) s d=0 by simp [sift,hz],
    add_zero,sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases h : 7∣j
  · simp [sift,chi7,Nat.mod_eq_zero_of_dvd h]
  · simp only [sift,s,sieve_good ho.pos.ne' h]

private lemma chi7_mod {d : ℕ} (h7 : 7∣d) (j : ℕ) : chi7 (j%d)=chi7 j := by
  simp [chi7,Nat.mod_mod_of_dvd j h7]

private lemma chi7_unit_sq {d : ℕ} (h7 : 7∣d) (u : (ZMod d)ˣ) : chi7 (u:ZMod d).val^2=1 := by
  have hc := ((ZMod.val_coe_unit_coprime u).coprime_dvd_right h7).symm
  have hn := (show Nat.Prime 7 by decide).coprime_iff_not_dvd.mp hc
  have hz : (u:ZMod d).val%7≠0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  simp only [chi7,if_neg hz]
  split_ifs <;> norm_num

private lemma chi7_unit_mul {d : ℕ} (h7 : 7∣d) (u v : (ZMod d)ˣ) :
    chi7 ((u*v:(ZMod d)ˣ):ZMod d).val=chi7 (u:ZMod d).val*chi7 (v:ZMod d).val := by
  rw [Units.val_mul,ZMod.val_mul,chi7_mod h7,chi7_mul]

theorem wave_transform_seven {d w : ℕ} [NeZero d] (hd : Odd d) (h7 : 7∣d) (hw : Odd w) (hc : w.Coprime d) :
    ∑ u : (ZMod d)ˣ,chi7 (u:ZMod d).val*wave (u:ZMod d).val d w =
      chi7 w*(-2*∏ p∈d.primeFactors.erase 7,(1-chi7 p)) := by
  classical
  let v := ZMod.unitOfCoprime w hc
  have hv : chi7 (v:ZMod d).val=chi7 w := by simp [v,ZMod.val_natCast,chi7_mod h7]
  have hW := ThetaCharacterThree.wave_unit hd hw hc
  have hC (u : (ZMod d)ˣ) : chi7 (u:ZMod d).val=chi7 w*chi7 ((v/u:(ZMod d)ˣ):ZMod d).val := by
    have H := chi7_unit_mul h7 u (v/u)
    rw [mul_div_cancel] at H
    rw [← hv,H]
    linear_combination -(chi7 (u:ZMod d).val)*(chi7_unit_sq h7 (v/u))
  simp_rw [hW]
  rw [← parity_transform_seven hd h7,← ThetaReciprocalFibers.unit_sum_nat,mul_sum]
  apply Fintype.sum_bijective (fun u : (ZMod d)ˣ => v/u)
    ((show Function.Involutive (fun u : (ZMod d)ˣ => v/u) from fun u => div_div_cancel v u).bijective)
  intro u
  rw [hC u]
  ring

#print axioms parity_transform_seven
#print axioms wave_transform_seven
private def oddSign (j : ℕ) : ℤ := if j%2=1 then chi7 j else 0

private noncomputable def bare (j : ℕ) : ℝ := (oddSign j:ℝ)/j

private lemma sign_period (k j : ℕ) : oddSign (14*k+j)=oddSign j := by
  simp [oddSign,chi7,Nat.add_mod,Nat.mul_mod]

private lemma full_block (k : ℕ) : 0≤∑ j∈range 14,bare (14*k+j) := by
  simp only [bare,sign_period,sum_range_succ,sum_range_zero]
  norm_num [oddSign,chi7,Nat.cast_add]
  field_simp
  ring_nf
  positivity

private lemma partial_block {k r : ℕ} (hk : 1≤k) (hr : r≤14) :
    -((3:ℝ)/(14*k)) ≤ ∑ j∈range r,bare (14*k+j) := by
  let lo (j : ℕ) : ℝ := if oddSign j = -1 then -((1:ℝ)/(14*k)) else 0
  have hLo (j : ℕ) : lo j ≤ bare (14*k+j) := by
    have hj : (14:ℝ)*k ≤ (14*k+j:ℕ) := by exact_mod_cast Nat.le_add_right (14*k) j
    have hkpos : (0:ℝ)<14*k := by exact_mod_cast (by omega : 0<14*k)
    have hpos : (0:ℝ)<(14*k+j:ℕ) := hkpos.trans_le hj
    rw [bare,sign_period]
    dsimp [lo]
    by_cases h : oddSign j= -1
    · rw [if_pos h,h]; push_cast
      have H := one_div_le_one_div_of_le hkpos hj
      push_cast at H
      simpa only [neg_div] using neg_le_neg H
    · rw [if_neg h]
      apply div_nonneg _ hpos.le
      exact_mod_cast (show 0≤oddSign j by unfold oddSign chi7 at *; split_ifs at * <;> omega)
  apply le_trans _ (sum_le_sum (fun j _ => hLo j))
  have hp : 0≤(k:ℝ)⁻¹ := by positivity
  interval_cases r <;> norm_num [sum_range_succ,lo,oddSign,chi7,div_eq_mul_inv] <;> linarith

private lemma lower_after_blocks {K kmin : ℕ} (hkmin : 0<kmin) (hK : 14*kmin≤K+1) :
    (3808/6435:ℝ)-3/(14*kmin) ≤ siftedSum bare ∅ K := by
  have first : (3808/6435:ℝ) ≤ ∑ j∈range 14,bare j := by norm_num [sum_range_succ,bare,oddSign,chi7]
  have block_sum (k : ℕ) (hk : 0<k) : (3808/6435:ℝ) ≤ ∑ j∈range (14*k),bare j := by
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases h : k=0
      · subst k; simpa using first
      · rw [Nat.mul_succ,sum_range_add]
        exact (ih (Nat.pos_of_ne_zero h)).trans (le_add_of_nonneg_right (full_block k))
  let k := (K+1)/14
  let r := (K+1)%14
  have hk : kmin≤k := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simpa [Nat.mul_comm] using hK)
  have hD : (14:ℝ)*kmin≤14*k := by exact_mod_cast Nat.mul_le_mul_left 14 hk
  have hE := div_le_div_of_nonneg_left (a:=(3:ℝ)) (by norm_num) (show (0:ℝ)<14*kmin by positivity) hD
  have H := block_sum k (hkmin.trans_le hk)
  have G := partial_block (hkmin.trans_le hk) (r:=r) ((Nat.mod_lt _ (by decide)).le)
  simp only [siftedSum,sift,notMem_empty,IsEmpty.forall_iff,implies_true,if_true]
  rw [show K+1=14*k+r from (Nat.div_add_mod _ _).symm,sum_range_add]
  linarith only [H,G,hE]

private lemma bare_prefix {K : ℕ} (hK : 0<K) :
    (1/3:ℝ) ≤ siftedSum bare ∅ K := by
  by_cases h : K+1<14
  · have hk : K≤12 := by omega
    interval_cases K <;> norm_num [siftedSum,sift,sum_range_succ,bare,oddSign,chi7] at *
  · have H := lower_after_blocks (K:=K) (kmin:=1) (by decide) (by omega)
    norm_num at H
    linarith only [H]

private lemma bare_mul_odd {p : ℕ} (ho : Odd p) (i : ℕ) :
    bare (p*i)=((chi7 p:ℝ)/p)*bare i := by
  simp only [bare,oddSign,Nat.mul_mod,Nat.odd_iff.mp ho,one_mul,Nat.mod_mod,chi7_mul,
    Nat.cast_mul]
  split_ifs <;> push_cast <;> ring

private lemma numerator_nonneg (s : Finset ℕ) (hs : ∀ p∈s,p.Prime ∧ Odd p ∧ chi7 p= -1) (K : ℕ) :
    0 ≤ siftedSum bare s K := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
    by_cases h : 0<K
    · exact (by norm_num : (0:ℝ)≤1/3).trans (bare_prefix h)
    · have : K=0 := by omega
      simp [this,siftedSum,sift,bare,oddSign]
  | @insert p s hp ih =>
    have hs' (a) (ha : a∈s) := hs a (mem_insert_of_mem ha)
    obtain ⟨hpr,ho,hc⟩ := hs p (mem_insert_self ..)
    rw [prefix_insert _ hpr (bare_mul_odd ho) hp (fun a ha => (hs' a ha).1),hc]
    simp only [Int.cast_neg,Int.cast_one,neg_div,one_div,neg_mul,sub_neg_eq_add]
    exact add_nonneg (ih hs' K) (mul_nonneg (by positivity) (ih hs' (K/p)))

private lemma sifted_eq {d : ℕ} [NeZero d] (j : ℕ) :
    sift bare (d.primeFactors.erase 7) j =
      if j%2=1 ∧ j.Coprime d then (chi7 j:ℝ)/j else 0 := by
  rw [sift,bare,oddSign]
  by_cases h : 7∣j
  · have hz : chi7 j=0 := by simp [chi7,Nat.mod_eq_zero_of_dvd h]
    simp [hz]
  · simp only [← sieve_good (NeZero.ne d) h]
    split_ifs <;> simp_all
private theorem row_seven_aux {d : ℕ} [NeZero d] (hd : Odd d) (h7 : 7∣d) (K : ℕ) :
    (∑ u : (ZMod d)ˣ,(chi7 (u:ZMod d).val:ℝ)*row d K (u:ZMod d).val) =
      ((-2*∏ p∈d.primeFactors.erase 7,(1-chi7 p):ℤ):ℝ)*siftedSum bare (d.primeFactors.erase 7) K := by
  classical
  let s := d.primeFactors.erase 7
  let A : ℤ := -2*∏ p∈s,(1-chi7 p)
  have ht (w : ℕ) :
      (∑ u : (ZMod d)ˣ,chi7 (u:ZMod d).val*wave (u:ZMod d).val d w) =
        if w%2=1 ∧ w.Coprime d then chi7 w*A else 0 := by
    split_ifs with h
    · exact wave_transform_seven hd h7 (Nat.odd_iff.mpr h.1) h.2
    · have H (n : ℕ) : wave n d w=0 := if_neg (fun H => h H.2.2)
      simp [H]
  have he (i : ℕ) :
      (∑ u : (ZMod d)ˣ,(chi7 (u:ZMod d).val:ℝ)*(((i:ℝ)+1)⁻¹*
        (wave (u:ZMod d).val d (i+1):ℝ))) =
        (A:ℝ)*sift bare s (i+1) := by
    have H := congrArg (Int.cast (R:=ℝ)) (ht (i+1))
    push_cast at H
    rw [show s=d.primeFactors.erase 7 from rfl,sifted_eq]
    simp_rw [show ∀ (a b c:ℝ),a*(b*c)=b*(a*c) by intros; ring,← mul_sum]
    rw [H]; split_ifs <;> push_cast <;> ring
  change _=(A:ℝ)*siftedSum bare s K
  unfold row
  simp_rw [mul_sum]; rw [sum_comm]; simp_rw [he]; rw [← mul_sum]
  congr 1
  unfold siftedSum
  rw [sum_range_succ']
  simp [sift,bare,oddSign]

/-- Every finite primitive row has a nonpositive conductor-seven transform. -/
theorem row_transform_nonpos {d : ℕ} [NeZero d] (hd : Odd d) (h7 : 7∣d) (K : ℕ) :
    (∑ u : (ZMod d)ˣ,(chi7 (u:ZMod d).val:ℝ)*row d K (u:ZMod d).val) ≤ 0 := by
  classical
  let s := d.primeFactors.erase 7
  let A : ℤ := -2*∏ p∈s,(1-chi7 p)
  rw [row_seven_aux hd h7]
  change (A:ℝ)*siftedSum bare s K ≤ 0
  by_cases hz : A=0
  · simp [hz]
  · have hs (p) (hp : p∈s) : Nat.Prime p ∧ Odd p ∧ chi7 p= -1 := by
      obtain ⟨hne,hf⟩ := mem_erase.mp hp
      have hpr := Nat.prime_of_mem_primeFactors hf
      have hh : chi7 p≠1 := by
        intro hh
        have hprod : (∏ a∈s,(1-chi7 a))=0 := prod_eq_zero hp (by simp [hh])
        exact hz (by simp [A,hprod])
      have hn : ¬7∣p := fun H => hne ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) hpr).mp H).symm
      have h0 : p%7≠0 := fun H => hn (Nat.dvd_of_mod_eq_zero H)
      refine ⟨hpr,hd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hf),?_⟩
      unfold chi7 at *
      split_ifs <;> omega
    have hA : A ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (prod_nonneg (fun p _ => sub_nonneg.mpr (chi7_le p)))
    exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hA) (numerator_nonneg s hs K)

private lemma long_prefix {K : ℕ} (hK : 448≤K) : (7/12:ℝ) ≤ siftedSum bare ∅ K := by
  have H := lower_after_blocks (K:=K) (kmin:=32) (by decide) (by omega)
  norm_num only [Nat.cast_ofNat] at H
  linarith only [H]

/-- The conductor row contributes at least 7/6 in absolute size for K ≥ 448. -/
theorem seven_row_bound {K : ℕ} (hK : 448≤K) :
    (∑ u : (ZMod 7)ˣ,(chi7 (u:ZMod 7).val:ℝ)*row 7 K (u:ZMod 7).val) ≤ -(7/6:ℝ) := by
  rw [row_seven_aux (by decide) (dvd_refl 7)]
  simp only [Nat.Prime.primeFactors (by decide : Nat.Prime 7),erase_singleton,prod_empty,mul_one,Int.cast_neg,Int.cast_ofNat]
  linarith only [long_prefix hK]

/-- At denominator 21, sifting out 3 adds a second positive prefix at K/3. -/
theorem twentyone_row_bound {K : ℕ} (hK : 1344≤K) :
    (∑ u : (ZMod 21)ˣ,(chi7 (u:ZMod 21).val:ℝ)*row 21 K (u:ZMod 21).val) ≤ -(28/9:ℝ) := by
  rw [row_seven_aux (by decide) (by decide),show (21:ℕ).primeFactors.erase 7={3} by decide +kernel]
  have he := prefix_insert bare (p:=3) (by decide) (bare_mul_odd (by decide : Odd 3))
    (s:=∅) (by simp) (by simp) K
  rw [insert_empty_eq] at he
  rw [he]
  norm_num [chi7]
  linarith only [long_prefix (K:=K) (by omega),long_prefix (K:=K/3) (by omega)]

#print axioms row_transform_nonpos
#print axioms seven_row_bound
#print axioms twentyone_row_bound

end Arxiv.«2501.03234».ThetaCharacterSeven
