import ThetaCharacterHarmonicLimit
import ThetaCharacterSeven
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! Exact theta row factors for a Jacobi character whose conductor divides the row modulus. -/
namespace Arxiv.«2501.03234».ThetaJacobiRows
open Finset Filter Topology ThetaCharacterThree ThetaCharacterSeven ThetaRowCorrelations
variable (q : ℕ) [NeZero q]

/-- Natural-input Jacobi symbol. -/
noncomputable def symbol (n : ℕ) : ℤ := jacobiSym (n:ℤ) q

omit [NeZero q] in
lemma symbol_mul (a b : ℕ) : symbol q (a*b)=symbol q a*symbol q b := by
  simp only [symbol,Nat.cast_mul,jacobiSym.mul_left]

omit [NeZero q] in
lemma symbol_mod {d : ℕ} (hd : q∣d) (n : ℕ) : symbol q (n%d)=symbol q n := by
  apply jacobiSym.mod_left'
  exact_mod_cast ((Nat.mod_modEq n d).of_dvd hd : (n%d)%q=n%q)

lemma symbol_zero {n : ℕ} (h : ¬n.Coprime q) : symbol q n=0 := by
  exact jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa [Int.gcd] using h)

omit [NeZero q] in
lemma symbol_unit {n : ℕ} (h : n.Coprime q) : symbol q n=1 ∨ symbol q n= -1 :=
  jacobiSym.eq_one_or_neg_one (by simpa [Int.gcd] using h.gcd_eq_one)

/-- Euler primes in the row modulus outside the Jacobi modulus. -/
def sieve (d : ℕ) : Finset ℕ := d.primeFactors.filter (·.Coprime q)

noncomputable def parityFactor : ℤ := ∑ i∈range q,parity i*symbol q i

private lemma zero_multiple (h₁ : 1<q) {d : ℕ} (h : q∣d) : symbol q d=0 := by
  apply symbol_zero
  rw [Nat.Coprime,Nat.gcd_eq_right h]
  omega

private theorem raw {d : ℕ} (h₁ : 1<q) (ho : Odd d) (hd : q∣d) :
    siftedSum (fun j => parity j*symbol q j) ∅ d = parityFactor q := by
  obtain ⟨k,rfl⟩ := hd
  have hq := ho.of_dvd_nat (dvd_mul_right q k)
  have hk := ho.of_dvd_nat (dvd_mul_left k q)
  let f j := parity j*symbol q j
  have hshift (a j : ℕ) : f (q*a+j)=(-1:ℤ)^a*f j := by
    have he : symbol q (q*a+j)=symbol q j := by
      rw [← symbol_mod q (dvd_refl q) (q*a+j),Nat.mul_add_mod_self_left, symbol_mod q (dvd_refl q)]
    simp only [f,parity,he,pow_add,pow_mul,hq.neg_one_pow]
    ring
  have H (a : ℕ) : ∑ j ∈ range (q*a), f j = if a%2=1 then parityFactor q else 0 := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Nat.mul_succ,sum_range_add,ih]
      simp_rw [hshift,← mul_sum]
      change _ + (-1:ℤ)^a * parityFactor q = _
      simp only [neg_one_pow_eq_ite,Nat.even_iff]
      split_ifs <;> omega
  simp only [siftedSum,sift,notMem_empty,IsEmpty.forall_iff,implies_true,if_true,sum_range_succ,
    zero_multiple q h₁ (dvd_mul_right q k),mul_zero,add_zero]
  simpa only [Nat.odd_iff.mp hk,if_true] using H k

private theorem parity_prefix (s : Finset ℕ) {d : ℕ} (h₁ : 1<q) (ho : Odd d) (hq : q∣d)
    (hs : ∀ a∈s, Nat.Prime a ∧ a.Coprime q ∧ a∣d) :
    siftedSum (fun j => parity j*symbol q j) s d = parityFactor q*∏ a∈s,(1-symbol q a) := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty => simpa using raw q h₁ ho hq
  | @insert p s hp ih =>
    obtain ⟨hpr,hne,hpd⟩ := hs p (mem_insert_self ..)
    have hs' (a) (ha : a∈s) := hs a (mem_insert_of_mem ha)
    have H := Nat.mul_div_cancel' hpd
    have hdiv {a : ℕ} (ha : a.Coprime p) (had : a∣d) : a∣d/p := ha.dvd_mul_left.mp (H.symm ▸ had)
    have hq' := hdiv hne.symm hq
    have ho' : Odd (d/p) := ho.of_dvd_nat ⟨p,by rw [mul_comm,H]⟩
    have hf (i) : parity (p*i)*symbol q (p*i)=symbol q p*(parity i*symbol q i) := by
      rw [parity_odd_mul (ho.of_dvd_nat hpd),symbol_mul q]; ring
    rw [prefix_insert _ hpr hf hp (fun a ha => (hs' a ha).1),ih ho hq hs',
      ih ho' hq' (fun a ha => ⟨(hs' a ha).1,(hs' a ha).2.1,
        hdiv ((Nat.coprime_primes (hs' a ha).1 hpr).mpr (fun e => hp (e ▸ ha))) (hs' a ha).2.2⟩),prod_insert hp]
    ring
omit [NeZero q] in
private lemma sieve_good {d j : ℕ} (hd : d≠0) (h : j.Coprime q) :
    j.Coprime d ↔ ∀ p∈sieve q d, ¬p∣j := by
  constructor
  · intro hc p hp
    have hpr := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    exact fun hpj => hpr.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpj (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1))
  · intro hs; by_contra hn
    obtain ⟨p,hpr,hpj,hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    exact hs p (mem_filter.mpr ⟨hpr.mem_primeFactors hpd hd,h.coprime_dvd_left hpj⟩) hpj

/-- The conductor parity transform and its finite sieve factors. -/
theorem parity_transform {d : ℕ} (h₁ : 1<q) (ho : Odd d) (hq : q∣d) :
    (∑ j∈(range d).filter (·.Coprime d), parity j*symbol q j) =
      parityFactor q*∏ p∈sieve q d,(1-symbol q p) := by
  classical
  let s := sieve q d
  have H := parity_prefix q s h₁ ho hq (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1,
    (mem_filter.mp hp).2,Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1⟩)
  have hz : symbol q d=0 := zero_multiple q h₁ hq
  rw [← H,siftedSum,sum_range_succ,show sift (fun j => parity j*symbol q j) s d=0 by simp [sift,hz],
    add_zero,sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases h : j.Coprime q
  · simp only [sift,s,sieve_good q ho.pos.ne' h]
  · simp [sift,symbol_zero q h]

omit [NeZero q] in
private lemma unit_sq {d : ℕ} (hd : q∣d) (u : (ZMod d)ˣ) : symbol q (u:ZMod d).val^2=1 := by
  have hc := (ZMod.val_coe_unit_coprime u).coprime_dvd_right hd
  rcases symbol_unit q hc with h|h <;> rw [h] <;> norm_num

omit [NeZero q] in
private lemma unit_mul {d : ℕ} (hq : q∣d) (u v : (ZMod d)ˣ) :
    symbol q ((u*v:(ZMod d)ˣ):ZMod d).val=symbol q (u:ZMod d).val*symbol q (v:ZMod d).val := by
  rw [Units.val_mul,ZMod.val_mul,symbol_mod q hq,symbol_mul q]

theorem wave_transform {d w : ℕ} [NeZero d] (h₁ : 1<q) (hd : Odd d) (hq : q∣d) (hw : Odd w) (hc : w.Coprime d) :
    ∑ u : (ZMod d)ˣ,symbol q (u:ZMod d).val*wave (u:ZMod d).val d w =
      symbol q w*(parityFactor q*∏ p∈sieve q d,(1-symbol q p)) := by
  classical
  let v := ZMod.unitOfCoprime w hc
  have hv : symbol q (v:ZMod d).val=symbol q w := by simp [v,ZMod.val_natCast,symbol_mod q hq]
  have hW := ThetaCharacterThree.wave_unit hd hw hc
  have hC (u : (ZMod d)ˣ) : symbol q (u:ZMod d).val=symbol q w*symbol q ((v/u:(ZMod d)ˣ):ZMod d).val := by
    have H := unit_mul q hq u (v/u)
    rw [mul_div_cancel] at H
    rw [← hv,H]
    linear_combination -(symbol q (u:ZMod d).val)*(unit_sq q hq (v/u))
  simp_rw [hW]
  rw [← parity_transform q h₁ hd hq,← ThetaReciprocalFibers.unit_sum_nat,mul_sum]
  apply Fintype.sum_bijective (fun u : (ZMod d)ˣ => v/u)
    ((show Function.Involutive (fun u : (ZMod d)ˣ => v/u) from fun u => div_div_cancel v u).bijective)
  intro u
  rw [hC u]
  ring

/-- Ordinary reciprocal Legendre term; the zero index contributes zero. -/
noncomputable def term (n : ℕ) : ℝ := (symbol q n:ℝ)/n

omit [NeZero q] in
/-- Deleting a finite set of primes gives the usual Euler factors in the ordinary limit. -/
theorem sifted_limit {L : ℝ} (hL : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L))
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Tendsto (siftedSum (term q) s) atTop (𝓝 (L * ∏ p ∈ s,(1-(symbol q p:ℝ)/p))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hL
  | @insert p s hp ih =>
    have hpr := hs p (mem_insert_self ..)
    have hs' (a) (ha : a ∈ s) := hs a (mem_insert_of_mem ha)
    have hterm (j : ℕ) : term q (p*j)=((symbol q p:ℝ)/p)*term q j := by
      simp only [term,symbol_mul,Nat.cast_mul,Int.cast_mul]; ring
    have H := ih hs'
    have G := H.sub ((H.comp (Nat.tendsto_div_const_atTop hpr.ne_zero)).const_mul ((symbol q p:ℝ)/p))
    rw [prod_insert hp]
    convert G using 1
    · funext K; exact prefix_insert _ hpr hterm hp hs' K
    · congr 1; ring

private lemma sifted_eq {d : ℕ} [NeZero d] (j : ℕ) :
    sift (term q) (insert 2 (sieve q d)) j =
      if j%2=1 ∧ j.Coprime d then (symbol q j:ℝ)/j else 0 := by
  by_cases h : j.Coprime q
  · simp only [sift,term,forall_mem_insert,← sieve_good q (NeZero.ne d) h]
    have he : (¬2∣j) ↔ j%2=1 := by omega
    simp only [he]
  · simp [sift,term,symbol_zero q h]

theorem row_factorization {d : ℕ} [NeZero d] (h₁ : 1<q) (hd : Odd d) (hq : q∣d) (K : ℕ) :
    (∑ u : (ZMod d)ˣ,(symbol q (u:ZMod d).val:ℝ)*row d K (u:ZMod d).val) =
      ((parityFactor q*∏ p∈sieve q d,(1-symbol q p):ℤ):ℝ)*siftedSum (term q) (insert 2 (sieve q d)) K := by
  classical
  let s := sieve q d
  let A : ℤ := parityFactor q*∏ p∈s,(1-symbol q p)
  have ht (w : ℕ) :
      (∑ u : (ZMod d)ˣ,symbol q (u:ZMod d).val*wave (u:ZMod d).val d w) =
        if w%2=1 ∧ w.Coprime d then symbol q w*A else 0 := by
    split_ifs with h
    · exact wave_transform q h₁ hd hq (Nat.odd_iff.mpr h.1) h.2
    · have H (n : ℕ) : wave n d w=0 := if_neg (fun H => h H.2.2)
      simp [H]
  have he (i : ℕ) :
      (∑ u : (ZMod d)ˣ,(symbol q (u:ZMod d).val:ℝ)*(((i:ℝ)+1)⁻¹*
        (wave (u:ZMod d).val d (i+1):ℝ))) =
        (A:ℝ)*sift (term q) (insert 2 s) (i+1) := by
    have H := congrArg (Int.cast (R:=ℝ)) (ht (i+1))
    push_cast at H
    rw [show s=sieve q d from rfl,sifted_eq q]
    simp_rw [show ∀ (a b c:ℝ),a*(b*c)=b*(a*c) by intros; ring,← mul_sum]
    rw [H]; split_ifs <;> push_cast <;> ring
  change _=(A:ℝ)*siftedSum (term q) (insert 2 s) K
  unfold row
  simp_rw [mul_sum]; rw [sum_comm]; simp_rw [he]; rw [← mul_sum]
  congr 1
  unfold siftedSum
  rw [sum_range_succ']
  simp [sift,term]

/-- All denominator-dependent factors multiply the same signed conductor factor. -/
theorem row_limit {d : ℕ} [NeZero d] (h₁ : 1<q) (ho : Odd d) (hd : q∣d) {L : ℝ}
    (hL : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L)) :
    Tendsto (fun K => ∑ u : (ZMod d)ˣ,(symbol q (u:ZMod d).val:ℝ)*row d K (u:ZMod d).val) atTop
      (𝓝 (((parityFactor q*∏ p∈sieve q d,(1-symbol q p):ℤ):ℝ) *
        (L*∏ p∈insert 2 (sieve q d),(1-(symbol q p:ℝ)/p)))) := by
  simp_rw [row_factorization q h₁ ho hd]
  apply Tendsto.const_mul
  apply sifted_limit q hL
  intro p hp
  rcases mem_insert.mp hp with rfl|hp
  · decide
  · exact Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1

#print axioms parity_transform
#print axioms wave_transform
#print axioms row_factorization
#print axioms row_limit
end Arxiv.«2501.03234».ThetaJacobiRows
