import HosoyaQuadraticCharacterPairs
import HosoyaReducedClassMass
import LucasFibonacciDiagonalUnion

/-! The prime mass of the simultaneous Pell nonresidue certificate for a candidate value. -/

namespace Arxiv.«2211.10788».PrimeObstruction
open Finset Filter Topology CunninghamChain.PrimeMass

/-- Primes at which neither of the two Pell equations attached to a candidate can hold. -/
def pellDetectingPrimes (y : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ¬IsSquare (5*(y:ZMod p)^2+44) ∧ ¬IsSquare (5*(y:ZMod p)^2-44)}

/-- The product of the two signed discriminants is a square only at the common value five. -/
theorem pell_product_square_iff (y : ℕ) :
    IsSquare ((5*(y:ℤ)^2+44)*(5*(y:ℤ)^2-44)) ↔ y=5 := by
  by_cases h : y<14
  · interval_cases y <;> norm_num
  · have hy : (14:ℤ)≤y := by exact_mod_cast (by omega : 14≤y)
    constructor
    · rintro ⟨v,hv⟩
      let d := 5*(y:ℤ)^2
      have hd : (980:ℤ)≤d := by
        dsimp [d]; nlinarith [mul_nonneg (sub_nonneg.mpr hy) (show 0≤(y:ℤ)+14 by omega)]
      have e : (v.natAbs:ℤ)^2 = d^2-1936 := by
        rw [Int.natAbs_sq]; dsimp [d]; nlinarith
      have both : d-1<(v.natAbs:ℤ) ∧ (v.natAbs:ℤ)<d := by
        constructor
        · by_contra! hn
          nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0≤d-1+(v.natAbs:ℤ) by omega)]
        · by_contra! hn
          nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0≤d+(v.natAbs:ℤ) by omega)]
      omega
    · omega

private theorem diagonal_iff_square (y : ℕ) :
    ((∃ n, y=lucasFibonacciSum n) ∨ IsLowerNeighborValue y) ↔
      IsSquare (5*(y:ℤ)^2+44) ∨ IsSquare (5*(y:ℤ)^2-44) := by
  rw [either_diagonal_iff_pell]
  constructor
  · rintro ⟨v,h|h⟩
    · exact Or.inl ⟨(v:ℤ),by exact_mod_cast (by nlinarith : 5*y^2+44=v*v)⟩
    · have he : (v:ℤ)^2+44=5*(y:ℤ)^2 := by exact_mod_cast h
      exact Or.inr ⟨v,by nlinarith⟩
  · rintro (⟨v,hv⟩ | ⟨v,hv⟩)
    · refine ⟨v.natAbs,Or.inl ?_⟩
      exact_mod_cast (show (v.natAbs:ℤ)^2=5*(y:ℤ)^2+44 by rw [Int.natAbs_sq]; nlinarith)
    · refine ⟨v.natAbs,Or.inr ?_⟩
      exact_mod_cast (show (v.natAbs:ℤ)^2+44=5*(y:ℤ)^2 by rw [Int.natAbs_sq]; nlinarith)

private theorem nonresidue_coprime {p : ℕ} [Fact p.Prime] {a : ℤ}
    (h : ¬IsSquare (a:ZMod p)) : p.Coprime a.natAbs := by
  apply Nat.Coprime.symm
  change a.gcd p = 1
  by_contra hn
  have h0 := jacobiSym.eq_zero_iff_not_coprime.mpr hn
  have h1 := ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr h
  omega

private theorem detecting_iff_class {p M : ℕ} [NeZero M] {a b : ℤ}
    (hm : M=4*a.natAbs*b.natAbs) (hp : p.Prime) :
    (¬IsSquare (a:ZMod p) ∧ ¬IsSquare (b:ZMod p)) ↔
      p∈represented (negativeClasses M a b) := by
  let : Fact p.Prime := ⟨hp⟩
  have h₁ : 4*a.natAbs ∣ M := hm ▸ dvd_mul_right _ _
  have h₂ : 4*b.natAbs ∣ M := by rw [hm,mul_right_comm]; exact dvd_mul_right _ _
  constructor
  · rintro ⟨ha,hb⟩
    have hp2 : p≠2 := by
      rintro rfl
      have h (x : ZMod 2) : IsSquare x := by
        fin_cases x
        · exact IsSquare.zero
        · exact IsSquare.one
      exact ha (h _)
    have hc4 : p.Coprime 4 := by
      simpa using (hp.odd_of_ne_two hp2).coprime_two_right.pow_right 2
    have hc : p.Coprime M := hm ▸ (hc4.mul_right (nonresidue_coprime ha)).mul_right (nonresidue_coprime hb)
    refine ⟨ZMod.unitOfCoprime p hc,?_,(ZMod.coe_unitOfCoprime ..).symm⟩
    simp only [negativeClasses,mem_filter,mem_univ,true_and,symbol_at_unit h₁ hc,symbol_at_unit h₂ hc]
    exact ⟨ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr ha,ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr hb⟩
  · rintro ⟨u,hu,he⟩
    have hc : p.Coprime M := (ZMod.isUnit_iff_coprime p M).mp (he ▸ u.isUnit)
    have eu : u=ZMod.unitOfCoprime p hc := Units.ext (he.symm.trans (ZMod.coe_unitOfCoprime ..).symm)
    simpa [negativeClasses,eu,symbol_at_unit h₁ hc,symbol_at_unit h₂ hc,
      ZMod.nonsquare_iff_jacobiSym_eq_neg_one] using hu

/-- A prime detected by the two quadratic characters excludes every term of the upper sequence. -/
theorem detecting_excludes {y p : ℕ} (hp : p∈pellDetectingPrimes y) (n : ℕ) :
    ¬lucasFibonacciSum n ≡ y [MOD p] := by
  intro h
  have e := (ZMod.natCast_eq_natCast_iff ..).mpr h
  obtain ⟨v,hv|hv⟩ := (either_diagonal_iff_pell (lucasFibonacciSum n)).mp (Or.inl ⟨n,rfl⟩)
  · have hh := congrArg (fun z : ℕ => (z : ZMod p)) hv
    push_cast at hh
    rw [e] at hh
    exact hp.2.1 ⟨v,by linear_combination -hh⟩
  · have hh := congrArg (fun z : ℕ => (z : ZMod p)) hv
    push_cast at hh
    rw [e] at hh
    exact hp.2.2 ⟨v,by linear_combination -hh⟩

/-- Away from both diagonals exactly one quarter of normalized prime mass detects the candidate
by simultaneous quadratic nonresidues. -/
theorem pell_detecting_prime_mass (y : ℕ)
    (hy : ¬((∃ n, y=lucasFibonacciSum n) ∨ IsLowerNeighborValue y)) :
    Tendsto (fun x : ℝ => (x-1)*mass (pellDetectingPrimes y) x) (𝓝[>] 1) (𝓝 (1/4 : ℝ)) := by
  let a := 5*(y:ℤ)^2+44
  let b := 5*(y:ℤ)^2-44
  have h : ¬(IsSquare a ∨ IsSquare b) := fun hh => hy ((diagonal_iff_square y).mpr hh)
  have ha := fun hs => h (Or.inl hs)
  have hb := fun hs => h (Or.inr hs)
  have hab : ¬IsSquare (a*b) := by
    intro hs
    have he := (pell_product_square_iff y).mp hs
    subst y; exact ha (by norm_num [a])
  let M := 4*a.natAbs*b.natAbs
  have hpos (z : ℤ) (hz : ¬IsSquare z) : 0<z.natAbs := Int.natAbs_pos.mpr (by
    rintro rfl; exact hz IsSquare.zero)
  have hM : 0<M := by dsimp [M]; exact Nat.mul_pos (Nat.mul_pos (by decide) (hpos a ha)) (hpos b hb)
  let : NeZero M := ⟨hM.ne'⟩
  let S := negativeClasses M a b
  have count : 4*S.card = M.totient := by
    apply quarter_negative_classes (dvd_mul_right ..) _ _ ha hb hab
    · rw [mul_right_comm]; exact dvd_mul_right ..
    · simp [Int.natAbs_mul,mul_assoc]
  have weight_eq (n : ℕ) : weight (pellDetectingPrimes y) n = weight (represented S) n := by
    by_cases hn : n.Prime
    · have he := detecting_iff_class (M:=M) (a:=a) (b:=b) rfl hn
      have mem : n∈pellDetectingPrimes y ↔ n∈represented S := by
        simpa [pellDetectingPrimes,a,b,S,hn] using he
      by_cases hm : n∈pellDetectingPrimes y
      · simp [weight,hn,hm,mem.mp hm]
      · have hs : n∉represented S := fun hh => hm (mem.mpr hh)
        simp [weight,hn,hm,hs]
    · simp [weight,hn]
  have lim := mass_represented S
  have eq (x : ℝ) : mass (pellDetectingPrimes y) x = mass (represented S) x := by
    simp only [mass,weight_eq]
  have ratio : (S.card:ℝ) / M.totient = 1/4 := by
    have ht : (0:ℝ)<M.totient := by exact_mod_cast Nat.totient_pos.mpr hM
    have hc : (4:ℝ)*S.card=M.totient := by exact_mod_cast count
    field_simp; linarith
  simpa only [eq,ratio] using lim

/-- All prime moduli missing a candidate off both diagonals have normalized mass eventually
above every constant below one quarter. -/
theorem missing_prime_mass_lower (y : ℕ)
    (hy : ¬((∃ n, y=lucasFibonacciSum n) ∨ IsLowerNeighborValue y)) {c : ℝ} (hc : c<1/4) :
    ∀ᶠ x : ℝ in 𝓝[>] 1, c<(x-1)*mass {p : ℕ | p.Prime ∧
      ∀ n : ℕ, ¬lucasFibonacciSum n ≡ y [MOD p]} x := by
  let B := {p : ℕ | p.Prime ∧ ∀ n : ℕ, ¬lucasFibonacciSum n ≡ y [MOD p]}
  have hsub : pellDetectingPrimes y ⊆ B := fun p hp => ⟨hp.1,detecting_excludes hp⟩
  filter_upwards [(pell_detecting_prime_mass y hy).eventually_const_lt hc,self_mem_nhdsWithin] with x hx h1
  apply hx.trans_le
  apply mul_le_mul_of_nonneg_left _ (by exact sub_nonneg.mpr (le_of_lt h1))
  apply (summable_weight _ h1).tsum_le_tsum _ (summable_weight B h1)
  intro p
  apply div_le_div_of_nonneg_right _ (by positivity)
  by_cases hp : p.Prime ∧ p∈pellDetectingPrimes y
  · simp [weight,hp.1,hp.2,hsub hp.2]
  · rw [weight,if_neg hp]
    exact weight_nonneg B p

/-- On either complete diagonal the simultaneous obstruction never occurs. -/
theorem pell_detecting_empty (y : ℕ) (hy : (∃ n, y=lucasFibonacciSum n) ∨ IsLowerNeighborValue y) :
    pellDetectingPrimes y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  rcases (diagonal_iff_square y).mp hy with ⟨v,hv⟩|⟨v,hv⟩
  · exact hp.2.1 ⟨v,by simpa using congrArg (fun z : ℤ => (z:ZMod p)) hv⟩
  · exact hp.2.2 ⟨v,by simpa using congrArg (fun z : ℤ => (z:ZMod p)) hv⟩

#print axioms pell_product_square_iff
#print axioms detecting_excludes
#print axioms pell_detecting_prime_mass
#print axioms missing_prime_mass_lower
#print axioms pell_detecting_empty

end Arxiv.«2211.10788».PrimeObstruction
