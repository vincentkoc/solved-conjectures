import ThetaJacobiRows
import ThetaPrimitiveTwist

/-! Complex Dirichlet character transforms of odd reciprocal rows. -/
namespace Arxiv.«2501.03234».ThetaDirichletRows
open Finset Filter Topology ThetaCharacterThree ThetaCharacterSeven ThetaRowCorrelations
open ThetaJacobiRows (sieve)
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

noncomputable abbrev symbol (n : ℕ) : ℂ := χ (n:ZMod q)

omit [NeZero q] in
private lemma symbol_mul (a b : ℕ) : symbol χ (a*b)=symbol χ a*symbol χ b := by
  simp only [symbol,Nat.cast_mul,map_mul]

omit [NeZero q] in
private lemma symbol_mod {d : ℕ} (hd : q∣d) (n : ℕ) : symbol χ (n%d)=symbol χ n := by
  apply congrArg χ
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((Nat.mod_modEq n d).of_dvd hd)

omit [NeZero q] in
private lemma symbol_zero {n : ℕ} (h : ¬n.Coprime q) : symbol χ n=0 :=
  χ.map_nonunit (fun hu => h ((ZMod.isUnit_iff_coprime n q).mp hu))

noncomputable def parityFactor : ℂ := ∑ i∈range q,(parity i:ℂ)*symbol χ i

private lemma zero_multiple (h₁ : 1<q) {d : ℕ} (h : q∣d) : symbol χ d=0 := by
  apply symbol_zero
  rw [Nat.Coprime,Nat.gcd_eq_right h]
  omega

private theorem raw {d : ℕ} (h₁ : 1<q) (ho : Odd d) (hd : q∣d) :
    siftedSum (fun j => parity j*symbol χ j) ∅ d = parityFactor χ := by
  obtain ⟨k,rfl⟩ := hd
  have hq := ho.of_dvd_nat (dvd_mul_right q k)
  have hk := ho.of_dvd_nat (dvd_mul_left k q)
  let f j := parity j*symbol χ j
  have hshift (a j : ℕ) : f (q*a+j)=(-1:ℂ)^a*f j := by
    have he : symbol χ (q*a+j)=symbol χ j := by
      rw [← symbol_mod χ (dvd_refl q) (q*a+j),Nat.mul_add_mod_self_left, symbol_mod χ (dvd_refl q)]
    simp only [f,parity,he,pow_add,pow_mul,hq.neg_one_pow,Int.cast_pow,Int.cast_neg,Int.cast_one]
    ring
  have H (a : ℕ) : ∑ j ∈ range (q*a), f j = if a%2=1 then parityFactor χ else 0 := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Nat.mul_succ,sum_range_add,ih]
      simp_rw [hshift,← mul_sum]
      change _ + (-1:ℂ)^a * parityFactor χ = _
      simp only [neg_one_pow_eq_ite,Nat.even_iff]
      split_ifs <;> first | omega | ring
  simp only [siftedSum,sift,notMem_empty,IsEmpty.forall_iff,implies_true,if_true,sum_range_succ,
    zero_multiple χ h₁ (dvd_mul_right q k),mul_zero,add_zero]
  simpa only [Nat.odd_iff.mp hk,if_true] using H k

private theorem parity_prefix (s : Finset ℕ) {d : ℕ} (h₁ : 1<q) (ho : Odd d) (hq : q∣d)
    (hs : ∀ a∈s, Nat.Prime a ∧ a.Coprime q ∧ a∣d) :
    siftedSum (fun j => parity j*symbol χ j) s d = parityFactor χ*∏ a∈s,(1-symbol χ a) := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty => simpa using raw χ h₁ ho hq
  | @insert p s hp ih =>
    obtain ⟨hpr,hne,hpd⟩ := hs p (mem_insert_self ..)
    have hs' (a) (ha : a∈s) := hs a (mem_insert_of_mem ha)
    have H := Nat.mul_div_cancel' hpd
    have hdiv {a : ℕ} (ha : a.Coprime p) (had : a∣d) : a∣d/p := ha.dvd_mul_left.mp (H.symm ▸ had)
    have hq' := hdiv hne.symm hq
    have ho' : Odd (d/p) := ho.of_dvd_nat ⟨p,by rw [mul_comm,H]⟩
    have hf (i) : parity (p*i)*symbol χ (p*i)=symbol χ p*(parity i*symbol χ i) := by
      rw [parity_odd_mul (ho.of_dvd_nat hpd),symbol_mul χ]; ring
    rw [prefix_insert _ hpr hf hp (fun a ha => (hs' a ha).1),ih ho hq hs',
      ih ho' hq' (fun a ha => ⟨(hs' a ha).1,(hs' a ha).2.1,
        hdiv ((Nat.coprime_primes (hs' a ha).1 hpr).mpr (fun e => hp (e ▸ ha))) (hs' a ha).2.2⟩),prod_insert hp]
    ring
omit [NeZero q] χ in
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
    (∑ j∈(range d).filter (·.Coprime d), parity j*symbol χ j) =
      parityFactor χ*∏ p∈sieve q d,(1-symbol χ p) := by
  classical
  let s := sieve q d
  have H := parity_prefix χ s h₁ ho hq (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1,
    (mem_filter.mp hp).2,Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1⟩)
  have hz : symbol χ d=0 := zero_multiple χ h₁ hq
  rw [← H,siftedSum,sum_range_succ,show sift (fun j => parity j*symbol χ j) s d=0 by simp [sift,hz],
    add_zero,sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases h : j.Coprime q
  · simp only [sift,s,sieve_good (q:=q) ho.pos.ne' h]
  · simp [sift,symbol_zero χ h]

omit [NeZero q] in
private lemma unit_mul {d : ℕ} (hq : q∣d) (u v : (ZMod d)ˣ) :
    symbol χ ((u*v:(ZMod d)ˣ):ZMod d).val=symbol χ (u:ZMod d).val*symbol χ (v:ZMod d).val := by
  rw [Units.val_mul,ZMod.val_mul,symbol_mod χ hq,symbol_mul χ]

theorem wave_transform {d w : ℕ} [NeZero d] (h₁ : 1<q) (hd : Odd d) (hq : q∣d) (hw : Odd w) (hc : w.Coprime d) :
    ∑ u : (ZMod d)ˣ,symbol χ (u:ZMod d).val*wave (u:ZMod d).val d w =
      symbol χ w*(parityFactor χ⁻¹*∏ p∈sieve q d,(1-symbol χ⁻¹ p)) := by
  classical
  let v := ZMod.unitOfCoprime w hc
  have hv : symbol χ (v:ZMod d).val=symbol χ w := by simp [v,ZMod.val_natCast,symbol_mod χ hq]
  have hW := ThetaCharacterThree.wave_unit hd hw hc
  have hC (u : (ZMod d)ˣ) : symbol χ (u:ZMod d).val=symbol χ w*symbol χ⁻¹ ((v/u:(ZMod d)ˣ):ZMod d).val := by
    have H := unit_mul χ hq u (v/u)
    rw [mul_div_cancel] at H
    rw [← hv,H]
    simp only [symbol,MulChar.inv_apply_eq_inv']
    change _=_*symbol χ ((v/u:(ZMod d)ˣ):ZMod d).val * (symbol χ ((v/u:(ZMod d)ˣ):ZMod d).val)⁻¹
    rw [mul_inv_cancel_right₀]
    exact MulChar.apply_ne_zero_iff.mpr ((ZMod.isUnit_iff_coprime _ q).mpr ((ZMod.val_coe_unit_coprime (v/u)).coprime_dvd_right hq))
  simp_rw [hW]
  rw [← parity_transform χ⁻¹ h₁ hd hq,← ThetaReciprocalFibers.unit_sum_nat,mul_sum]
  apply Fintype.sum_bijective (fun u : (ZMod d)ˣ => v/u)
    ((show Function.Involutive (fun u : (ZMod d)ˣ => v/u) from fun u => div_div_cancel v u).bijective)
  intro u
  rw [hC u]
  ring

/-- Ordinary reciprocal character term; the zero index contributes zero. -/
noncomputable def term (n : ℕ) : ℂ := symbol χ n/n

omit [NeZero q] in
/-- Deleting a finite set of primes gives the usual Euler factors in the ordinary limit. -/
theorem sifted_limit {L : ℂ} (hL : Tendsto (siftedSum (term χ) ∅) atTop (𝓝 L))
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Tendsto (siftedSum (term χ) s) atTop (𝓝 (L * ∏ p ∈ s,(1-symbol χ p/p))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hL
  | @insert p s hp ih =>
    have hpr := hs p (mem_insert_self ..)
    have hs' (a) (ha : a ∈ s) := hs a (mem_insert_of_mem ha)
    have hterm (j : ℕ) : term χ (p*j)=(symbol χ p/p)*term χ j := by
      simp only [term,symbol_mul,Nat.cast_mul]; ring
    have H := ih hs'
    have G := H.sub ((H.comp (Nat.tendsto_div_const_atTop hpr.ne_zero)).const_mul (symbol χ p/p))
    rw [prod_insert hp]
    convert G using 1
    · funext K; exact prefix_insert _ hpr hterm hp hs' K
    · congr 1; ring

private lemma sifted_eq {d : ℕ} [NeZero d] (j : ℕ) :
    sift (term χ) (insert 2 (sieve q d)) j =
      if j%2=1 ∧ j.Coprime d then symbol χ j/j else 0 := by
  by_cases h : j.Coprime q
  · simp only [sift,term,forall_mem_insert,← sieve_good (q:=q) (NeZero.ne d) h]
    have he : (¬2∣j) ↔ j%2=1 := by omega
    simp only [he]
  · simp [sift,term,symbol_zero χ h]

theorem row_factorization {d : ℕ} [NeZero d] (h₁ : 1<q) (hd : Odd d) (hq : q∣d) (K : ℕ) :
    (∑ u : (ZMod d)ˣ,(symbol χ (u:ZMod d).val:ℂ)*row d K (u:ZMod d).val) =
      (parityFactor χ⁻¹*∏ p∈sieve q d,(1-symbol χ⁻¹ p))*siftedSum (term χ) (insert 2 (sieve q d)) K := by
  classical
  let s := sieve q d
  let A : ℂ := parityFactor χ⁻¹*∏ p∈s,(1-symbol χ⁻¹ p)
  have ht (w : ℕ) :
      (∑ u : (ZMod d)ˣ,symbol χ (u:ZMod d).val*wave (u:ZMod d).val d w) =
        if w%2=1 ∧ w.Coprime d then symbol χ w*A else 0 := by
    split_ifs with h
    · exact wave_transform χ h₁ hd hq (Nat.odd_iff.mpr h.1) h.2
    · have H (n : ℕ) : wave n d w=0 := if_neg (fun H => h H.2.2)
      simp [H]
  have he (i : ℕ) :
      (∑ u : (ZMod d)ˣ,(symbol χ (u:ZMod d).val:ℂ)*(((i:ℂ)+1)⁻¹*
        (wave (u:ZMod d).val d (i+1):ℂ))) =
        (A:ℂ)*sift (term χ) (insert 2 s) (i+1) := by
    have H := ht (i+1)
    rw [show s=sieve q d from rfl,sifted_eq χ]
    simp_rw [show ∀ (a b c:ℂ),a*(b*c)=b*(a*c) by intros; ring,← mul_sum]
    rw [H]; split_ifs <;> push_cast <;> ring
  change _=(A:ℂ)*siftedSum (term χ) (insert 2 s) K
  unfold row
  push_cast
  simp_rw [mul_sum]; rw [sum_comm]; simp_rw [he]; rw [← mul_sum]
  congr 1
  unfold siftedSum
  rw [sum_range_succ']
  simp [sift,term]

/-- All denominator-dependent factors multiply the same signed conductor factor. -/
theorem row_limit {d : ℕ} [NeZero d] (h₁ : 1<q) (ho : Odd d) (hd : q∣d) {L : ℂ}
    (hL : Tendsto (siftedSum (term χ) ∅) atTop (𝓝 L)) :
    Tendsto (fun K => ∑ u : (ZMod d)ˣ,(symbol χ (u:ZMod d).val:ℂ)*row d K (u:ZMod d).val) atTop
      (𝓝 ((parityFactor χ⁻¹*∏ p∈sieve q d,(1-symbol χ⁻¹ p)) *
        (L*∏ p∈insert 2 (sieve q d),(1-symbol χ p/p)))) := by
  simp_rw [row_factorization χ h₁ ho hd]
  apply Tendsto.const_mul
  apply sifted_limit χ hL
  intro p hp
  rcases mem_insert.mp hp with rfl|hp
  · decide
  · exact Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1

#print axioms parity_transform
#print axioms wave_transform
#print axioms row_factorization
#print axioms row_limit
end Arxiv.«2501.03234».ThetaDirichletRows
