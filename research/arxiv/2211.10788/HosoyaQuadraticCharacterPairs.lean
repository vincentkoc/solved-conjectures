import HosoyaSimultaneousNonresidues

/-! Joint quadratic character counts on the units of a common period. -/

namespace Arxiv.«2211.10788».PrimeObstruction
open Finset

/-- The Jacobi symbol attached to an integer on representatives of reduced classes. -/
def unitSymbol {M : ℕ} (a : ℤ) (u : (ZMod M)ˣ) : ℤ := jacobiSym a (u : ZMod M).val

private theorem symbol_period {M : ℕ} {a : ℤ} (hd : 4*a.natAbs ∣ M) {m n : ℕ}
    (hm : Odd m) (hn : Odd n) (h : m ≡ n [MOD M]) : jacobiSym a m = jacobiSym a n := by
  rw [jacobiSym.mod_right a hm, jacobiSym.mod_right a hn]
  rw [show m % (4*a.natAbs) = n % (4*a.natAbs) from h.of_dvd hd]

private lemma odd_unit {M : ℕ} (h : 2 ∣ M) (u : (ZMod M)ˣ) : Odd (u : ZMod M).val :=
  (Nat.Coprime.of_dvd_right h (ZMod.val_coe_unit_coprime u)).odd_of_right

theorem symbol_at_unit {M : ℕ} [NeZero M] {a : ℤ} (hd : 4*a.natAbs ∣ M)
    {n : ℕ} (hc : n.Coprime M) :
    unitSymbol a (ZMod.unitOfCoprime n hc) = jacobiSym a n := by
  have h₂ : 2 ∣ M := dvd_trans (dvd_mul_of_dvd_left (by decide : 2 ∣ 4) _) hd
  apply symbol_period hd (odd_unit h₂ _) (Nat.Coprime.of_dvd_right h₂ hc).odd_of_right
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  simp [ZMod.coe_unitOfCoprime]

private lemma symbol_mul {M : ℕ} [NeZero M] {a : ℤ} (hd : 4*a.natAbs ∣ M)
    (u v : (ZMod M)ˣ) : unitSymbol a (u*v) = unitSymbol a u * unitSymbol a v := by
  have h₂ : 2 ∣ M := dvd_trans (dvd_mul_of_dvd_left (by decide : 2 ∣ 4) _) hd
  have hu := odd_unit h₂ u
  have hv := odd_unit h₂ v
  simp only [unitSymbol]
  rw [←jacobiSym.mul_right' a (by rintro he; simp [he] at hu) (by rintro he; simp [he] at hv)]
  apply symbol_period hd (odd_unit h₂ _) (hu.mul hv)
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  simp

theorem symbol_sign {M : ℕ} {a : ℤ} (hd : 4*a.natAbs ∣ M) (u : (ZMod M)ˣ) :
    unitSymbol a u = 1 ∨ unitSymbol a u = -1 := by
  apply jacobiSym.eq_one_or_neg_one
  exact (Nat.Coprime.of_dvd_right ((dvd_mul_left a.natAbs 4).trans hd)
    (ZMod.val_coe_unit_coprime u)).symm

/-- Every nonsquare signed integer has negative Jacobi symbol at arbitrarily large primes. -/
theorem large_negative_symbol {a : ℤ} (ha : ¬IsSquare a) (N : ℕ) :
    ∃ p>N, p.Prime ∧ jacobiSym a p = -1 := by
  by_cases h : IsSquare a.natAbs
  · obtain ⟨v,hv⟩ := h
    have hn : a < 0 := by
      by_contra! hpos
      apply ha
      refine ⟨(v:ℤ),?_⟩
      rw [←abs_of_nonneg hpos,←Int.natCast_natAbs,hv,Nat.cast_mul]
    have he : a = -((v:ℤ)^2) := by
      have hh : (a.natAbs:ℤ)=(v:ℤ)*v := by exact_mod_cast hv
      rw [Int.natCast_natAbs,abs_of_neg hn] at hh
      nlinarith
    obtain ⟨p,hp,pp,h3⟩ := Nat.forall_exists_prime_gt_and_modEq (max N v)
      (by decide : 4≠0) (by decide : Nat.Coprime 3 4)
    let : Fact p.Prime := ⟨pp⟩
    have hv0 : v≠0 := by rintro rfl; simp at he; omega
    have hvp : (v:ZMod p)≠0 := by
      intro hz
      have hvlt := (le_max_right N v).trans_lt hp
      have := congrArg ZMod.val hz
      simp [ZMod.val_natCast_of_lt hvlt,hv0] at this
    have hminus : legendreSym p (-1) = -1 := by
      apply (legendreSym.eq_neg_one_iff p).mpr
      simpa [ZMod.exists_sq_eq_neg_one_iff] using (show p%4=3 from h3)
    refine ⟨p,(le_max_left ..).trans_lt hp,pp,?_⟩
    rw [←jacobiSym.legendreSym.to_jacobiSym,he,neg_eq_neg_one_mul,legendreSym.mul,hminus,
      legendreSym.sq_one' p (by simpa using hvp),mul_one]
  · obtain ⟨M,r,_,hM,hr,hclass⟩ := two_nonsquares_prime_progression h h
    obtain ⟨p,hp,pp,hpmod⟩ := Nat.forall_exists_prime_gt_and_modEq N hM.ne' hr
    let : Fact p.Prime := ⟨pp⟩
    obtain ⟨h4,hn,_⟩ := hclass p pp hpmod
    refine ⟨p,hp,pp,ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr ?_⟩
    intro hs
    rcases Int.natAbs_eq a with he|he
    · rw [he] at hs
      exact hn (by simpa using hs)
    · rw [he] at hs
      have hneg := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega : p%4≠3)
      exact hn (by simpa using hneg.mul hs)

theorem sum_symbol_zero {M : ℕ} [NeZero M] {a : ℤ}
    (hd : 4*a.natAbs ∣ M) (ha : ¬IsSquare a) : ∑ u : (ZMod M)ˣ, unitSymbol a u = 0 := by
  obtain ⟨p,hp,pp,hn⟩ := large_negative_symbol ha M
  have hc := pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (NeZero.pos M) hp)
  let t := ZMod.unitOfCoprime p hc
  have ht : unitSymbol a t = -1 := (symbol_at_unit hd hc).trans hn
  have e := Equiv.sum_comp (Equiv.mulLeft t) (unitSymbol a)
  change (∑ u : (ZMod M)ˣ, unitSymbol a (t*u)) = _ at e
  simp only [symbol_mul hd,ht,neg_one_mul,Finset.sum_neg_distrib] at e
  omega

/-- Reduced classes on which both signed discriminants have negative Jacobi symbol. -/
noncomputable def negativeClasses (M : ℕ) [NeZero M] (a b : ℤ) : Finset (ZMod M)ˣ :=
  open Classical in univ.filter fun u => unitSymbol a u = -1 ∧ unitSymbol b u = -1

/-- For two independent square classes exactly one quarter of the units carry two minus signs. -/
theorem quarter_negative_classes {M : ℕ} [NeZero M] {a b : ℤ}
    (h₁ : 4*a.natAbs ∣ M) (h₂ : 4*b.natAbs ∣ M) (h₃ : 4*(a*b).natAbs ∣ M)
    (ha : ¬IsSquare a) (hb : ¬IsSquare b) (hab : ¬IsSquare (a*b)) :
    4*(negativeClasses M a b).card = M.totient := by
  classical
  have hf (u : (ZMod M)ˣ) : (if unitSymbol a u = -1 ∧ unitSymbol b u = -1 then (4:ℤ) else 0) =
      1 - unitSymbol a u - unitSymbol b u + unitSymbol (a*b) u := by
    rw [show unitSymbol (a*b) u = unitSymbol a u * unitSymbol b u from jacobiSym.mul_left ..]
    rcases symbol_sign h₁ u with h|h <;> rcases symbol_sign h₂ u with k|k <;> simp [h,k]
  have e := sum_congr (s₁ := (univ : Finset (ZMod M)ˣ)) rfl (fun u _ => hf u)
  simp only [sum_add_distrib,sum_sub_distrib,sum_symbol_zero h₁ ha,sum_symbol_zero h₂ hb,
    sum_symbol_zero h₃ hab,sub_zero,add_zero,sum_const,card_univ,nsmul_eq_mul,mul_one,
    ZMod.card_units_eq_totient] at e
  rw [←Finset.sum_filter] at e
  have hc : (4:ℤ)*(negativeClasses M a b).card = M.totient := by
    simpa [negativeClasses,mul_comm] using e
  exact_mod_cast hc

#print axioms sum_symbol_zero
#print axioms symbol_sign
#print axioms symbol_at_unit
#print axioms large_negative_symbol
#print axioms quarter_negative_classes

end Arxiv.«2211.10788».PrimeObstruction
