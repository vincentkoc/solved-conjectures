import ThetaRowCorrelations
/-! The quadratic character modulo three detects a signed row bias. -/
namespace Arxiv.«2501.03234».ThetaCharacterThree
open Finset

/-- The quadratic character of conductor three on natural representatives. -/
def chi (n : ℕ) : ℤ :=
  if n%3=1 then 1 else if n%3=2 then -1 else 0

private lemma chi_mul (a b : ℕ) : chi (a*b)=chi a*chi b := by
  unfold chi; rw [Nat.mul_mod]
  have ha := Nat.mod_lt a (by decide : 0<3)
  have hb := Nat.mod_lt b (by decide : 0<3)
  interval_cases a%3 <;> interval_cases b%3 <;> decide

/-- The sign is positive at odd representatives. -/
def parity (n : ℕ) : ℤ := -(-1:ℤ)^n

private lemma parity_mul {a : ℕ} (ha : Odd a) (b : ℕ) : parity (a*b)=parity b := by
  simp [parity,pow_mul,ha.neg_one_pow]

private lemma period_six (n : ℕ) : parity (n+6)*chi (n+6)=parity n*chi n := by
  simp [parity,chi,pow_add,Nat.add_mod]

private lemma raw {d : ℕ} (ho : Odd d) (h3 : 3∣d) :
    ∑ j∈range d, parity j*chi j=2 := by
  let f j := parity j*chi j
  have H (k) : ∀ j, f (6*k+j)=f j := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro j
      rw [show 6*(k+1)+j=(6*k+j)+6 by ring]
      exact (period_six _).trans (ih j)
  have h6 : ∑ j∈range 6,f j=0 := by decide +kernel
  have h0 (k) : ∑ j∈range (6*k),f j=0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ,sum_range_add,ih]; simpa [H] using h6
  obtain ⟨a,ha⟩ := ho
  obtain ⟨b,hb⟩ := h3
  have hd : d=6*(d/6)+3 := by omega
  change ∑ j∈range d,f j=2
  rw [hd,sum_range_add,h0,zero_add]
  simp_rw [H]
  decide +kernel

private def fiber (d : ℕ) (s : Finset ℕ) : ℤ :=
  ∑ j∈range d, if ∀ p∈s, ¬p∣j then parity j*chi j else 0

private lemma sum_multiples {d p : ℕ} (hp : 0<p) (hpd : p∣d) (f : ℕ → ℤ) :
    ∑ j ∈ (range d).filter (fun j => p∣j), f j=∑ i∈range (d/p),f (p*i) := by
  obtain ⟨k,rfl⟩ := hpd
  rw [Nat.mul_div_cancel_left _ hp]
  symm
  apply sum_bij (fun i _ => p*i)
  · intro i hi; exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hi) hp),dvd_mul_right ..⟩
  · intro i _ j _ he; exact Nat.eq_of_mul_eq_mul_left hp he
  · intro n hn; obtain ⟨h,⟨i,rfl⟩⟩ := mem_filter.mp hn
    exact ⟨i,mem_range.mpr (Nat.lt_of_mul_lt_mul_left (mem_range.mp h)),rfl⟩
  · intros; rfl

private lemma fiber_insert {d p : ℕ} {s : Finset ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hn : p∉s) (hpd : p∣d) (hs : ∀ a∈s, Nat.Prime a) :
    fiber d (insert p s) = fiber d s-chi p*fiber (d/p) s := by
  classical
  let good j := ∀ a∈s, ¬a∣j
  let f (j : ℕ) : ℤ := if good j then parity j*chi j else 0
  have H (i) : f (p*i)=chi p*f i := by
    have hg : good (p*i) ↔ good i := by
      dsimp [good]
      constructor
      · intro h a ha hai
        exact h a ha (hai.trans (dvd_mul_left i p))
      · intro h a ha
        have hc : a.Coprime p := (Nat.coprime_primes (hs _ ha) hp).mpr (fun e => hn (e ▸ ha))
        exact fun H => h a ha (hc.dvd_mul_left.mp H)
    by_cases h : good i
    · dsimp only [f]; rw [if_pos (hg.mpr h),if_pos h,parity_mul ho,chi_mul]; ring
    · dsimp only [f]; rw [if_neg (fun H => h (hg.mp H)),if_neg h,mul_zero]
  have he (j) : (if ∀ a∈insert p s, ¬a∣j then parity j*chi j else 0) =
      f j-(if p∣j then f j else 0) := by
    simp only [forall_mem_insert]; by_cases h : p∣j <;> simp [h,f,good]
  unfold fiber
  simp_rw [he]; rw [sum_sub_distrib]
  change _-(∑ j∈range d,if p∣j then f j else 0) = _-chi p*(∑ i∈range (d/p), f i)
  congr 1
  rw [← sum_filter, sum_multiples hp.pos hpd]; simp_rw [H]; rw [← mul_sum]

/-- Parity of the unit representatives paired with the quadratic character
modulo three. Every sieving prime contributes an explicit factor. -/
private theorem fiber_primes (s : Finset ℕ) {d : ℕ} (ho : Odd d) (h3 : 3∣d)
    (hs : ∀ a∈s, Nat.Prime a ∧ a≠3 ∧ a∣d) :
    fiber d s = 2*∏ a∈s, (1-chi a) := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty => simpa [fiber] using raw ho h3
  | @insert p s hp ih =>
    obtain ⟨hpr,hne,hpd⟩ := hs p (mem_insert_self ..)
    have hs' (a) (ha : a∈s) := hs a (mem_insert_of_mem ha)
    have H := Nat.mul_div_cancel' hpd
    have hdiv {a : ℕ} (ha : a.Coprime p) (had : a∣d) : a∣d/p :=
      ha.dvd_mul_left.mp (H.symm ▸ had)
    have h3' := hdiv ((Nat.coprime_primes (by decide : Nat.Prime 3) hpr).mpr hne.symm) h3
    have ho' : Odd (d/p) := ho.of_dvd_nat ⟨p,by rw [mul_comm,H]⟩
    rw [fiber_insert hpr (ho.of_dvd_nat hpd) hp hpd (fun a ha => (hs' a ha).1),
      ih ho h3 hs',ih ho' h3' (fun a ha => ⟨(hs' a ha).1,(hs' a ha).2.1,
        hdiv ((Nat.coprime_primes (hs' a ha).1 hpr).mpr (fun e => hp (e ▸ ha))) (hs' a ha).2.2⟩),
      prod_insert hp]
    ring

/-- For odd d divisible by three, the unnormalized quadratic twist of the parity
of its reduced representatives has a nonnegative Euler product. -/
theorem parity_transform {d : ℕ} (ho : Odd d) (h3 : 3∣d) :
    (∑ j∈(range d).filter (·.Coprime d), parity j*chi j) =
      2*∏ p∈d.primeFactors.erase 3,(1-chi p) := by
  classical
  let s := d.primeFactors.erase 3
  have hd : d≠0 := by obtain ⟨a,ha⟩ := ho; omega
  have H := fiber_primes s ho h3 (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2,
    (mem_erase.mp hp).1,Nat.dvd_of_mem_primeFactors (mem_erase.mp hp).2⟩)
  rw [← H,sum_filter]; unfold fiber
  apply sum_congr rfl; intro j hj
  by_cases h : 3∣j
  · have hz : chi j=0 := by simp [chi,Nat.mod_eq_zero_of_dvd h]
    simp [hz]
  · have hh : j.Coprime d ↔ ∀ p∈s, ¬p∣j := by
      constructor
      · intro hc p hp
        have hpr := Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2
        exact fun hpj => hpr.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpj (Nat.dvd_of_mem_primeFactors (mem_erase.mp hp).2))
      · intro hs; by_contra hn
        obtain ⟨p,hpr,hpj,hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
        have hne : p≠3 := fun he => h (he ▸ hpj)
        exact hs p (mem_erase.mpr ⟨hne,hpr.mem_primeFactors hpd hd⟩) hpj
    simp only [hh]

private lemma chi_mod {d : ℕ} (h3 : 3∣d) (j : ℕ) : chi (j%d)=chi j := by
  simp [chi,Nat.mod_mod_of_dvd j h3]

private lemma chi_unit_sq {d : ℕ} (h3 : 3∣d) (u : (ZMod d)ˣ) :
    chi (u:ZMod d).val^2=1 := by
  have hc := ((ZMod.val_coe_unit_coprime u).coprime_dvd_right h3).symm
  have hn := (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mp hc
  have hz : (u:ZMod d).val%3≠0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  have ht := Nat.mod_lt (u:ZMod d).val (by decide : 0<3)
  unfold chi; split_ifs <;> norm_num
  omega

private lemma chi_unit_mul {d : ℕ} (h3 : 3∣d) (u v : (ZMod d)ˣ) :
    chi ((u*v:(ZMod d)ˣ):ZMod d).val=chi (u:ZMod d).val*chi (v:ZMod d).val := by
  rw [Units.val_mul,ZMod.val_mul,chi_mod h3,chi_mul]

/-- On units the primitive wave is parity after the permutation (u↦w/u). -/
theorem wave_unit {d w : ℕ} [NeZero d] (hd : Odd d) (hw : Odd w) (hc : w.Coprime d)
    (u : (ZMod d)ˣ) : ThetaRowCorrelations.wave (u:ZMod d).val d w =
      parity ((ZMod.unitOfCoprime w hc/u:(ZMod d)ˣ):ZMod d).val := by
  rw [ThetaRowCorrelations.wave,if_pos ⟨ZMod.val_coe_unit_coprime u,Nat.odd_iff.mp hd,
    Nat.odd_iff.mp hw,hc⟩,ThetaRowCorrelations.sign_neg_pow]
  simp only [parity,ZMod.natCast_zmod_val,div_eq_mul_inv,Units.val_mul,← ZMod.inv_coe_unit,
    ZMod.coe_unitOfCoprime]

/-- The modulo-three twist of an actual primitive reciprocal wave factors
into the numerator character and a nonnegative denominator transform. -/
theorem wave_transform {d w : ℕ} [NeZero d] (hd : Odd d) (h3 : 3∣d) (hw : Odd w) (hc : w.Coprime d) :
    ∑ u : (ZMod d)ˣ, chi (u:ZMod d).val*ThetaRowCorrelations.wave (u:ZMod d).val d w =
      chi w*(2*∏ p∈d.primeFactors.erase 3,(1-chi p)) := by
  classical
  let v := ZMod.unitOfCoprime w hc
  have hv : chi (v:ZMod d).val=chi w := by
    simp [v,ZMod.val_natCast,chi_mod h3]
  have hW := wave_unit hd hw hc
  have hC (u : (ZMod d)ˣ) : chi (u:ZMod d).val=chi w*chi ((v/u:(ZMod d)ˣ):ZMod d).val := by
    have H := chi_unit_mul h3 u (v/u)
    rw [mul_div_cancel] at H
    rw [← hv,H]
    linear_combination -(chi (u:ZMod d).val)*(chi_unit_sq h3 (v/u))
  simp_rw [hW]
  rw [← parity_transform hd h3,← ThetaReciprocalFibers.unit_sum_nat,mul_sum]
  apply Fintype.sum_bijective (fun u : (ZMod d)ˣ => v/u)
    ((show Function.Involutive (fun u : (ZMod d)ˣ => v/u) from fun u => div_div_cancel v u).bijective)
  intro u
  rw [hC u]
  ring

/-- Reciprocal numerator in the odd part of the character modulo three. -/
noncomputable def bareTerm (j : ℕ) : ℝ :=
  if j%6=1 then (j:ℝ)⁻¹ else if j%6=5 then -(j:ℝ)⁻¹ else 0

private lemma bare_block (k : ℕ) {r : ℕ} (hr : r≤6) :
    0≤∑ j∈range r,bareTerm (6*k+1+j) := by
  have h (j : ℕ) : (6*k+1+j)%6=(1+j)%6 := by omega
  have hle : ((6*k+1:ℕ):ℝ)⁻¹≥((6*k+1+4:ℕ):ℝ)⁻¹ :=
    inv_anti₀ (by positivity) (by exact_mod_cast (by omega : 6*k+1≤6*k+1+4))
  interval_cases r <;> simp only [sum_range_succ,sum_range_zero,zero_add] <;>
    norm_num [bareTerm,h] <;> first | positivity | (push_cast at hle; linarith)

private lemma bare_prefix {K : ℕ} (hK : 0<K) :
    4/5 ≤ ∑ j∈range (K+1),bareTerm j := by
  have step (k : ℕ) {r : ℕ} (hr : r≤6) :
      (∑ j∈range (6*k+1),bareTerm j) ≤ ∑ j∈range (6*k+r+1),bareTerm j := by
    rw [show 6*k+r+1=(6*k+1)+r by omega,sum_range_add bareTerm (6*k+1) r]
    exact le_add_of_nonneg_right (bare_block k hr)
  have H (k : ℕ) : 4/5 ≤ ∑ j∈range (6*(k+1)+1),bareTerm j := by
    induction k with
    | zero => norm_num [sum_range_succ,bareTerm]
    | succ k ih => exact ih.trans (by simpa only [Nat.mul_succ] using step (k+1) (r:=6) le_rfl)
  by_cases h : K<6
  · interval_cases K <;> norm_num [sum_range_succ,bareTerm] at *
  · have he : 6*(K/6)+K%6=K := Nat.div_add_mod K 6
    have hr : K%6≤6 := (Nat.mod_lt _ (by decide)).le
    have ha := step (K/6) hr
    rw [he] at ha
    have hq : K/6-1+1=K/6 := by omega
    exact ((hq ▸ H (K/6-1))).trans ha

private noncomputable def sifted (s : Finset ℕ) (j : ℕ) : ℝ :=
  if ∀ p∈s, ¬p∣j then bareTerm j else 0

private noncomputable def siftedPrefix (s : Finset ℕ) (K : ℕ) : ℝ :=
  ∑ j∈range (K+1),sifted s j

private lemma bare_eq (j : ℕ) :
    bareTerm j=if j%2=1 then (chi j:ℝ)/j else 0 := by
  have h₂ := Nat.mod_mod_of_dvd j (by decide : 2∣6)
  have h₃ := Nat.mod_mod_of_dvd j (by decide : 3∣6)
  have h := Nat.mod_lt j (by decide : 0<6)
  unfold bareTerm chi
  rw [← h₂,← h₃]
  interval_cases j%6 <;> norm_num [div_eq_mul_inv]

private lemma bare_mul_odd {p : ℕ} (hp : Odd p) (i : ℕ) :
    bareTerm (p*i) = ((chi p : ℝ)/p)*bareTerm i := by
  simp only [bare_eq, Nat.mul_mod, Nat.odd_iff.mp hp, one_mul, Nat.mod_mod,
    chi_mul,Int.cast_mul,Nat.cast_mul]
  split_ifs <;> ring

private lemma prefix_insert_odd {p : ℕ} (hp : Nat.Prime p) (ho : Odd p) {s : Finset ℕ}
    (hn : p∉s) (hs : ∀ a∈s,Nat.Prime a) (K : ℕ) :
    siftedPrefix (insert p s) K=siftedPrefix s K-((chi p:ℝ)/p)*siftedPrefix s (K/p) := by
  classical
  have H (i : ℕ) : sifted s (p*i)= ((chi p:ℝ)/p)*sifted s i := by
    have hg : (∀ a∈s, ¬a∣p*i) ↔ (∀ a∈s, ¬a∣i) := by
      constructor
      · intro h a ha hai; exact h a ha (hai.trans (dvd_mul_left i p))
      · intro h a ha
        have hc : a.Coprime p := (Nat.coprime_primes (hs a ha) hp).mpr (fun e => hn (e ▸ ha))
        exact fun hai => h a ha (hc.dvd_mul_left.mp hai)
    simp only [sifted,hg,bare_mul_odd ho]; split_ifs <;> simp
  have ht (j : ℕ) : sifted (insert p s) j=sifted s j-(if p∣j then sifted s j else 0) := by
    simp only [sifted,forall_mem_insert]; by_cases h : p∣j <;> simp [h]
  have he : (∑ j∈(range (K+1)).filter (fun j => p∣j),sifted s j) =
      ∑ i∈range (K/p+1),sifted s (p*i) := by
    symm; apply sum_bij (fun i _ => p*i)
    · intro i hi
      have h := (Nat.le_div_iff_mul_le hp.pos).mp (Nat.le_of_lt_succ (mem_range.mp hi))
      exact mem_filter.mpr ⟨mem_range.mpr (by rw [mul_comm]; omega),dvd_mul_right ..⟩
    · intro i _ j _ he; exact Nat.eq_of_mul_eq_mul_left hp.pos he
    · intro j hj; obtain ⟨h,⟨i,rfl⟩⟩ := mem_filter.mp hj
      have hc := (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa [mul_comm] using Nat.le_of_lt_succ (mem_range.mp h))
      exact ⟨i,mem_range.mpr (Nat.lt_succ_of_le hc),rfl⟩
    · intros; rfl
  unfold siftedPrefix
  simp_rw [ht]; rw [sum_sub_distrib,← sum_filter,he]; simp_rw [H]; rw [← mul_sum]

private theorem prefix_nonneg (s : Finset ℕ) (hs : ∀ p∈s,Nat.Prime p ∧ p%6=5) (K : ℕ) :
    0 ≤ siftedPrefix s K := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
    by_cases h : 0<K
    · exact (by norm_num : (0:ℝ)≤4/5).trans (by simpa [siftedPrefix,sifted] using bare_prefix h)
    · have : K=0 := by omega
      simp [this,siftedPrefix,sifted,bareTerm]
  | @insert p s hp ih =>
    have hs' (a) (ha : a∈s) := hs a (mem_insert_of_mem ha)
    obtain ⟨hpr,hp6⟩ := hs p (mem_insert_self ..)
    have ho : Odd p := Nat.odd_iff.mpr (by omega)
    have hc : chi p = -1 := by simp [chi,show p%3=2 by omega]
    rw [prefix_insert_odd hpr ho hp (fun a ha => (hs' a ha).1),hc]
    simp only [Int.cast_neg,Int.cast_one,neg_div,one_div,neg_mul,sub_neg_eq_add]
    exact add_nonneg (ih hs' K) (mul_nonneg (by positivity) (ih hs' (K/p)))

private lemma sifted_eq {d : ℕ} [NeZero d] (j : ℕ) :
    sifted (d.primeFactors.erase 3) j =
      if j%2=1 ∧ j.Coprime d then (chi j:ℝ)/j else 0 := by
  rw [sifted,bare_eq]
  by_cases h : 3∣j
  · have hz : chi j=0 := by simp [chi,Nat.mod_eq_zero_of_dvd h]
    simp [hz]
  · have hh : j.Coprime d ↔ ∀ p∈d.primeFactors.erase 3, ¬p∣j := by
      constructor
      · intro hc p hp
        have hpr := Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2
        exact fun hpj => hpr.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpj (Nat.dvd_of_mem_primeFactors (mem_erase.mp hp).2))
      · intro hs; by_contra hn
        obtain ⟨p,hpr,hpj,hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
        exact hs p (mem_erase.mpr ⟨fun e => h (e ▸ hpj),hpr.mem_primeFactors hpd (NeZero.ne _)⟩) hpj
    simp only [← hh]; split_ifs <;> simp_all

private lemma chi_le (p : ℕ) : chi p≤1 := by simp [chi]; split_ifs <;> decide

private theorem row_transform_aux {d : ℕ} [NeZero d] (hd : Odd d) (h3 : 3∣d) (K : ℕ) :
    (∑ u : (ZMod d)ˣ,(chi (u:ZMod d).val:ℝ)*ThetaRowCorrelations.row d K (u:ZMod d).val) =
      ((2*∏ p∈d.primeFactors.erase 3,(1-chi p):ℤ):ℝ)*siftedPrefix (d.primeFactors.erase 3) K := by
  classical
  let s := d.primeFactors.erase 3
  let A : ℤ := 2*∏ p∈s,(1-chi p)
  have ht (w : ℕ) :
      (∑ u : (ZMod d)ˣ,chi (u:ZMod d).val*ThetaRowCorrelations.wave (u:ZMod d).val d w) =
        if w%2=1 ∧ w.Coprime d then chi w*A else 0 := by
    split_ifs with h
    · exact wave_transform hd h3 (Nat.odd_iff.mpr h.1) h.2
    · have H (n : ℕ) : ThetaRowCorrelations.wave n d w=0 := if_neg (fun H => h H.2.2)
      simp [H]
  have he (i : ℕ) :
      (∑ u : (ZMod d)ˣ,(chi (u:ZMod d).val:ℝ)*(((i:ℝ)+1)⁻¹*
        (ThetaRowCorrelations.wave (u:ZMod d).val d (i+1):ℝ))) =
        (A:ℝ)*sifted s (i+1) := by
    have H := congrArg (Int.cast (R:=ℝ)) (ht (i+1))
    push_cast at H
    rw [show s=d.primeFactors.erase 3 from rfl,sifted_eq]
    simp_rw [show ∀ (a b c:ℝ),a*(b*c)=b*(a*c) by intros; ring,← mul_sum]
    rw [H]; split_ifs <;> push_cast <;> ring
  change _=(A:ℝ)*siftedPrefix s K
  unfold ThetaRowCorrelations.row
  simp_rw [mul_sum]; rw [sum_comm]; simp_rw [he]; rw [← mul_sum]
  congr 1
  unfold siftedPrefix
  rw [sum_range_succ']
  simp [sifted,bareTerm]

open Filter
open scoped Topology

private theorem sifted_limit {b : ℝ}
    (hb : Tendsto (fun n => ∑ j∈range n,bareTerm j) atTop (𝓝 b))
    (s : Finset ℕ) (hs : ∀ p∈s,Nat.Prime p ∧ Odd p) :
    Tendsto (siftedPrefix s) atTop (𝓝 (b*∏ p∈s,(1-(chi p:ℝ)/p))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty,mul_one]
    apply (hb.comp (tendsto_add_atTop_nat 1)).congr'
    exact Eventually.of_forall fun n => by simp [siftedPrefix,sifted]
  | @insert p s hps ih =>
    have hs' (a) (ha : a∈s) := hs a (mem_insert_of_mem ha)
    have hp := hs p (mem_insert_self ..)
    have H := ih hs'
    have H' := H.comp (Nat.tendsto_div_const_atTop hp.1.ne_zero)
    have result := H.sub (H'.const_mul ((chi p : ℝ)/p))
    rw [prod_insert hps]
    convert result.congr' (Eventually.of_forall fun K =>
      (prefix_insert_odd hp.1 hp.2 hps (fun a h => (hs' a h).1) K).symm) using 1
    congr 1
    ring

/-- Full numerator-window limit of the modulo-three transform at a fixed
odd denominator divisible by three. -/
theorem row_transform_limit {b : ℝ}
    (hb : Tendsto (fun n => ∑ j∈range n,bareTerm j) atTop (𝓝 b))
    {d : ℕ} [NeZero d] (hd : Odd d) (h3 : 3 ∣ d) :
    Tendsto (fun K => ∑ u : (ZMod d)ˣ,(chi (u:ZMod d).val:ℝ)*ThetaRowCorrelations.row d K (u:ZMod d).val)
      atTop (𝓝 (((2*∏ p∈d.primeFactors.erase 3,(1-chi p):ℤ):ℝ) *
        (b*∏ p∈d.primeFactors.erase 3,(1-(chi p:ℝ)/p)))) := by
  have hs (p) (hp : p∈d.primeFactors.erase 3) : p.Prime ∧ Odd p :=
    ⟨Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2,
      hd.of_dvd_nat (Nat.dvd_of_mem_primeFactors (mem_erase.mp hp).2)⟩
  exact ((sifted_limit hb _ hs).const_mul _).congr' (Eventually.of_forall fun K =>
    (row_transform_aux hd h3 K).symm)

/-- The signed character transform of a whole reciprocal row separates into a
denominator product and an explicit primitive numerator sum. -/
theorem row_transform {d : ℕ} [NeZero d] (hd : Odd d) (h3 : 3∣d) (K : ℕ) :
    (∑ u : (ZMod d)ˣ,(chi (u:ZMod d).val:ℝ)*ThetaRowCorrelations.row d K (u:ZMod d).val) =
      ((2*∏ p∈d.primeFactors.erase 3,(1-chi p):ℤ):ℝ)*
        ∑ j∈range (K+1),if j%2=1 ∧ j.Coprime d then (chi j:ℝ)/j else 0 := by
  rw [row_transform_aux hd h3]
  simp only [siftedPrefix,sifted_eq]

/-- The character-weighted mean of a finite reciprocal row is nonnegative.
This holds for every numerator cutoff, including partial periods. -/
theorem row_transform_nonneg {d : ℕ} [NeZero d] (hd : Odd d) (h3 : 3∣d) (K : ℕ) :
    0≤∑ u : (ZMod d)ˣ,(chi (u:ZMod d).val:ℝ)*ThetaRowCorrelations.row d K (u:ZMod d).val := by
  classical
  let s := d.primeFactors.erase 3
  let A : ℤ := 2*∏ p∈s,(1-chi p)
  rw [row_transform_aux hd h3]
  by_cases hz : A=0
  · change 0 ≤ (A:ℝ)*siftedPrefix s K
    simp [hz]
  · have hs (p) (hp : p∈s) : Nat.Prime p ∧ p%6=5 := by
      obtain ⟨h3',hf⟩ := mem_erase.mp hp
      have hpr := Nat.prime_of_mem_primeFactors hf
      have ho := Nat.odd_iff.mp (hd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hf))
      have hh : chi p≠1 := by
        intro hh
        have hprod : (∏ a∈s,(1-chi a))=0 := prod_eq_zero hp (by simp [hh])
        exact hz (by simp [A,hprod])
      have hn : ¬3∣p := fun H => h3' ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hpr).mp H).symm
      have h0 : p%3≠0 := fun H => hn (Nat.dvd_of_mod_eq_zero H)
      have h1 : p%3≠1 := fun H => hh (by simp [chi,H])
      exact ⟨hpr,by omega⟩
    have hA : 0≤A := mul_nonneg (by decide) (prod_nonneg (fun p _ => sub_nonneg.mpr (chi_le p)))
    exact mul_nonneg (by exact_mod_cast hA) (prefix_nonneg s hs K)

/-- The first contributing denominator has a uniform positive twist,
including every nonempty partial period. -/
theorem row_three_lower {K : ℕ} (hK : 0<K) :
    8/5 ≤ ∑ u : (ZMod 3)ˣ,(chi (u:ZMod 3).val:ℝ)*ThetaRowCorrelations.row 3 K (u:ZMod 3).val := by
  rw [row_transform_aux (by decide : Odd 3) (dvd_refl 3)]
  simp [siftedPrefix,sifted]
  linarith [bare_prefix hK]

end Arxiv.«2501.03234».ThetaCharacterThree
#print axioms Arxiv.«2501.03234».ThetaCharacterThree.wave_unit
#print axioms Arxiv.«2501.03234».ThetaCharacterThree.row_three_lower
#print axioms Arxiv.«2501.03234».ThetaCharacterThree.row_transform
#print axioms Arxiv.«2501.03234».ThetaCharacterThree.row_transform_nonneg
#print axioms Arxiv.«2501.03234».ThetaCharacterThree.wave_transform
#print axioms Arxiv.«2501.03234».ThetaCharacterThree.parity_transform

#print axioms Arxiv.«2501.03234».ThetaCharacterThree.row_transform_limit
