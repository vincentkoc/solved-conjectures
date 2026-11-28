import HosoyaRealEleven
import LucasFibonacciDiagonalUnion

/-! Sixth-power descent for cubes on either Hosoya diagonal. -/

namespace Arxiv.«2211.10788».HosoyaCubes

open RealEleven
open scoped RealEleven

private theorem negative_impossible (x t : ℤ) : x^2 + 44 ≠ 5*t^6 := by
  intro he
  have h := congrArg (fun n : ℤ => (n : ZMod 7)) he
  push_cast at h
  exact (by decide : ∀ a b : ZMod 7, a^2+44 ≠ 5*b^6) _ _ h

private theorem trace_coprime {x t : ℤ} (he : x^2 = 5*t^6+44) :
    IsCoprime (2*x) (5*t^6) := by
  have hodd : ¬ (2:ℤ) ∣ t := by
    rintro ⟨v,rfl⟩
    have h := congrArg (fun n : ℤ => (n : ZMod 16)) he
    push_cast at h
    exact (by decide : ∀ a b : ZMod 16, a^2 ≠ 5*(2*b)^6+44) _ _ h
  have h11 : ¬ (11:ℤ) ∣ t := by
    rintro ⟨v,hv⟩
    have hp : Prime (11:ℤ) := by decide
    obtain ⟨j,hj⟩ := hp.dvd_of_dvd_pow (n:=2) (show (11:ℤ) ∣ x^2 from
      ⟨5*11^5*v^6+4,by rw [he,hv]; ring⟩)
    rw [hj,hv] at he
    ring_nf at he
    omega
  have hC : IsCoprime (5*t^6) 176 := by
    have h₂ : IsCoprime t 2 :=
      ((show Prime (2:ℤ) by decide).irreducible.coprime_iff_not_dvd.mpr hodd).symm
    have h₁₁ : IsCoprime t 11 :=
      ((show Prime (11:ℤ) by decide).irreducible.coprime_iff_not_dvd.mpr h11).symm
    have h : IsCoprime t (2^4*11) := h₂.pow_right.mul_right h₁₁
    exact (show IsCoprime (5:ℤ) 176 from ⟨-35,1,by decide⟩).mul_left
      (show IsCoprime (t^6) 176 from h.pow_left)
  obtain ⟨a,b,hab⟩ := hC
  exact ⟨b*(2*x),a-4*b,by linear_combination hab + 4*b*he⟩

private def splitPrime : RingEleven := ⟨4,1⟩
private def twistBase : RingEleven := ⟨7,-2⟩

private theorem normalize_x {x t : ℤ} (he : x^2 = 5*t^6+44) :
    ∃ k : ℤ, (5*k+3)^2 = 5*t^6+44 := by
  have hh := congrArg (fun n : ℤ => (n : ZMod 5)) he
  push_cast at hh
  have h := (by decide : ∀ a b : ZMod 5, a^2 = 5*b^6+44 → a=3 ∨ -a=3) _ _ hh
  rcases h with h | h
  · have h' := (ZMod.intCast_eq_intCast_iff x 3 5).mp (by simpa using h)
    exact ⟨x/5,by rwa [show 5*(x/5)+3 = x by change x%5 = (3:ℤ)%5 at h'; omega]⟩
  · have h' := (ZMod.intCast_eq_intCast_iff (-x) 3 5).mp (by simpa using h)
    exact ⟨(-x)/5,by rwa [show 5*((-x)/5)+3 = -x by change (-x)%5 = (3:ℤ)%5 at h'; omega, neg_sq]⟩

private theorem split_sixth {k t : ℤ} (he : (5*k+3)^2 = 5*t^6+44) :
    ∃ w : RingEleven, ∃ u : RingElevenˣ,
      (⟨5*k+3,2⟩ : RingEleven) = splitPrime * ((u:RingEleven)*w^6) := by
  classical
  let := EuclideanDomain.gcdMonoid RingEleven
  let z : RingEleven := ⟨5*k+3,2⟩
  let b : RingEleven := ⟨4*k-2,1-k⟩
  have hz : z = splitPrime*b := by ext <;> simp [z,b,splitPrime] <;> ring
  have hn : b.norm = t^6 := by
    change (4*k-2)*(4*k-2)-11*(1-k)*(1-k) = _
    ring_nf at he ⊢
    omega
  have htr : algebraMap ℤ RingEleven (2*(5*k+3)) = z + star z := by
    ext <;> simp [z]; ring
  have hprod : algebraMap ℤ RingEleven (5*t^6) = z * star z := by
    rw [← Zsqrtd.norm_eq_mul_conj]
    change ((5*t^6 : ℤ) : RingEleven) = (z.norm : RingEleven)
    congr 1
    change 5*t^6 = (5*k+3)*(5*k+3)-11*2*2
    linear_combination -he
  have hc := (trace_coprime he).map (algebraMap ℤ RingEleven)
  rw [htr,hprod] at hc
  have hd : gcd b (star b) ∣ z := (gcd_dvd_left ..).trans (hz ▸ dvd_mul_left ..)
  have hd' : gcd b (star b) ∣ star z := (gcd_dvd_right ..).trans (by rw [hz,star_mul]; exact dvd_mul_right ..)
  have hu := hc.isUnit_of_dvd' (dvd_add hd hd') (dvd_mul_of_dvd_left hd _)
  have hb : b * star b = (t:RingEleven)^6 := by rw [← Zsqrtd.norm_eq_mul_conj,hn]; push_cast; rfl
  obtain ⟨w,u,hw⟩ := exists_associated_pow_of_mul_eq_pow hu hb
  exact ⟨w,u,by change z = _; rw [hz,←hw,mul_comm (u:RingEleven)]⟩


private theorem six_twists {t : ℤ} (hex : ∃ x : ℤ, x^2 = 5*t^6+44) :
    ∃ i : Fin 6, ∃ v : RingEleven,
      let g := (twistBase*(baseUnit:RingEleven)^i.val)*v^6
      (g.im = 2 ∨ g.im = -2) ∧ g.norm = 5*t^6 := by
  obtain ⟨x,he⟩ := hex
  obtain ⟨j,hj⟩ := normalize_x he
  obtain ⟨w,u,hw⟩ := split_sixth hj
  obtain ⟨n,hn⟩ := unit_signed_power u
  let k : ℤ := (n+1)/6
  let i : Fin 6 := ⟨((n+1)%6).toNat,by omega⟩
  have hi : (i.val:ℤ) + k*6 = 1+n := by dsimp [i,k]; omega
  have hp : baseUnit^i.val * (baseUnit^k)^6 = baseUnit * baseUnit^n := by
    calc baseUnit^i.val * (baseUnit^k)^6 =
        baseUnit^(i.val:ℤ) * (baseUnit^k)^(6:ℤ) := by simp
      _ = baseUnit^(1+n) := by rw [← zpow_mul,← zpow_add,hi]
      _ = _ := by rw [zpow_add,zpow_one]
  let v := (↑(baseUnit^k):RingEleven)*w
  let g := (twistBase*(baseUnit:RingEleven)^i.val)*v^6
  have hg : g = splitPrime*((↑(baseUnit^n):RingEleven)*w^6) := by
    have hval := congrArg (fun q : RingElevenˣ => (q:RingEleven)) hp
    simp only [Units.val_mul,Units.val_pow_eq_pow_val] at hval
    calc g = (twistBase*((baseUnit:RingEleven)^i.val*(↑(baseUnit^k):RingEleven)^6))*w^6 := by
          dsimp [g,v]; ring
      _ = (twistBase*(baseUnit:RingEleven))*((↑(baseUnit^n):RingEleven)*w^6) := by rw [hval]; ring
      _ = _ := rfl
  let z : RingEleven := ⟨5*j+3,2⟩
  have hs : z = g ∨ z = -g := by
    rcases hn with hu | hu
    · exact Or.inl (hw.trans (hu ▸ hg.symm))
    · right; change (⟨_,_⟩ : RingEleven) = _; rw [hw,hu,hg]; simp
  have hz : z.norm = 5*t^6 := by
    change (5*j+3)*(5*j+3)-11*2*2 = _; linear_combination hj
  refine ⟨i,v,?_⟩
  change (_ ∨ _) ∧ g.norm = _
  rcases hs with hs | hs
  · exact ⟨Or.inl ((congrArg Zsqrtd.im hs).symm),hs ▸ hz⟩
  · have h := congrArg Zsqrtd.im hs
    change 2 = -g.im at h
    exact ⟨Or.inr (show g.im = -2 by omega),by simpa [hs] using hz⟩

/-- The real coefficient of the sixth power of x+y√11. -/
def sexticReal {R : Type*} [CommRing R] (x y : R) : R :=
  x^6+165*x^4*y^2+1815*x^2*y^4+1331*y^6

/-- Half the coefficient of √11 in the same power. -/
def sexticHalf {R : Type*} [CommRing R] (x y : R) : R :=
  3*x^5*y+110*x^3*y^3+363*x*y^5

private theorem sixth_parts (v : RingEleven) :
    (v^6).re = sexticReal v.re v.im ∧ (v^6).im = 2*sexticHalf v.re v.im := by
  constructor <;> simp only [pow_succ,pow_zero,one_mul,Zsqrtd.re_mul,Zsqrtd.im_mul,
    sexticReal,sexticHalf] <;> ring

private def coeffs : Fin 6 → ℤ × ℤ :=
  ![(7,-2),(4,1),(73,22),(1456,439),(29047,8758),(579484,174721)]

private def twistIm {R : Type*} [CommRing R] (i : Fin 6) (a b : R) : R :=
  ((coeffs i).1 : R)*(2*sexticHalf a b) + ((coeffs i).2 : R)*sexticReal a b

private theorem twist_im (i : Fin 6) (v : RingEleven) :
    ((twistBase*(baseUnit:RingEleven)^i.val)*v^6).im = twistIm i v.re v.im := by
  have h (j : Fin 6) : twistBase*(baseUnit:RingEleven)^j.val =
      ⟨(coeffs j).1,(coeffs j).2⟩ := by fin_cases j <;> decide
  rw [h,Zsqrtd.im_mul,(sixth_parts v).1,(sixth_parts v).2]; rfl


private lemma cast_twist (m : ℕ) (i : Fin 6) (a b : ℤ) :
    ((twistIm i a b : ℤ) : ZMod m) = twistIm i (a : ZMod m) (b : ZMod m) := by
  simp [twistIm,sexticReal,sexticHalf]

set_option maxRecDepth 8192 in
private theorem local_twists {i : Fin 6} {a b : ℤ}
    (h : twistIm i a b = 2 ∨ twistIm i a b = -2) :
    (i = 0 ∨ i = 2) ∧ twistIm i a b = -2 := by
  have hm (m : ℕ) : twistIm i (a : ZMod m) (b : ZMod m) = 2 ∨
      twistIm i (a : ZMod m) (b : ZMod m) = -2 := by
    rw [← cast_twist]; rcases h with he | he <;> rw [he] <;> norm_num
  have h₄ : ∀ j : Fin 6, ∀ u v : ZMod 4,
      twistIm j u v = 2 ∨ twistIm j u v = -2 → j=0 ∨ j=2 ∨ j=4 := by decide +kernel
  have h₉ : ∀ u v : ZMod 9, ¬(twistIm 4 u v = 2 ∨ twistIm 4 u v = -2) := by decide +kernel
  have h₇ : ∀ j : Fin 6, ∀ u v : ZMod 7, twistIm j u v ≠ 2 := by decide +kernel
  refine ⟨?_,h.resolve_left (fun he => h₇ i a b (by rw [← cast_twist,he]; rfl))⟩
  rcases h₄ i a b (hm 4) with hh | hh | rfl
  · exact Or.inl hh
  · exact Or.inr hh
  · exact False.elim (h₉ a b (hm 9))

private theorem twist_norm (i : Fin 6) (v : RingEleven) :
    ((twistBase*(baseUnit:RingEleven)^i.val)*v^6).norm = 5*v.norm^6 := by
  simp only [Zsqrtd.norm_mul,show ∀ (z : RingEleven) (k : ℕ), (z^k).norm = z.norm^k
    from fun z k => map_pow Zsqrtd.normMonoidHom z k]
  change 5*(1:ℤ)^i.val*v.norm^6 = _
  simp

private theorem cube_norm_iff (t : ℕ) :
    ((∃ n, t^3 = lucasFibonacciSum n) ∨ IsLowerNeighborValue (t^3)) ↔
      ∃ x : ℤ, x^2 = 5*(t:ℤ)^6+44 := by
  rw [either_diagonal_iff_pell]
  constructor
  · rintro ⟨x,h | h⟩
    · exact ⟨x,by exact_mod_cast (show x^2=5*t^6+44 by linear_combination h)⟩
    · exfalso
      apply negative_impossible x t
      exact_mod_cast (show x^2+44=5*t^6 by linear_combination h)
  · rintro ⟨x,h⟩
    refine ⟨x.natAbs,Or.inl ?_⟩
    zify
    rw [sq_abs]
    linear_combination h

/-- The two homogeneous sextics remaining after the local obstructions. -/
def formZero {R : Type*} [CommRing R] (a b : R) : R := sexticReal a b - 7*sexticHalf a b

def formTwo {R : Type*} [CommRing R] (a b : R) : R := -11*sexticReal a b - 73*sexticHalf a b

private lemma twist_zero (a b : ℤ) : twistIm 0 a b = -2*formZero a b := by
  change 7*(2*sexticHalf a b)+(-2)*sexticReal a b = -2*(sexticReal a b-7*sexticHalf a b)
  ring

private lemma twist_two (a b : ℤ) : twistIm 2 a b = -2*formTwo a b := by
  change 73*(2*sexticHalf a b)+22*sexticReal a b = -2*(-11*sexticReal a b-73*sexticHalf a b)
  ring

/-- Exact over the integers, including reconstruction of the cube root from a solution. -/
theorem either_diagonal_cube_iff_sextics (t : ℕ) :
    ((∃ n, t^3 = lucasFibonacciSum n) ∨ IsLowerNeighborValue (t^3)) ↔
      ∃ a b : ℤ, (a^2-11*b^2).natAbs = t ∧ (formZero a b = 1 ∨ formTwo a b = 1) := by
  rw [cube_norm_iff]
  constructor
  · intro he
    obtain ⟨i,v,him,hn⟩ := six_twists he
    change (_ ∨ _) at him
    rw [twist_im] at him
    obtain ⟨hi,hi'⟩ := local_twists him
    have hn' : v.norm^6 = (t:ℤ)^6 := by rw [twist_norm] at hn; omega
    have hab : v.norm.natAbs^6 = t^6 := by simpa [Int.natAbs_pow] using congrArg Int.natAbs hn'
    refine ⟨v.re,v.im,?_,?_⟩
    · rw [show v.re^2-11*v.im^2 = v.norm by rw [Zsqrtd.norm_def]; ring]
      exact Nat.pow_left_injective (by decide : 6 ≠ 0) hab
    · rcases hi with rfl | rfl
      · left; rw [twist_zero] at hi'; omega
      · right; rw [twist_two] at hi'; omega
  · rintro ⟨a,b,hab,hforms⟩
    let v : RingEleven := ⟨a,b⟩
    have hnorm : v.norm.natAbs = t := by
      convert hab using 2
      change a*a-11*b*b = _; ring
    have hn : v.norm^6 = (t:ℤ)^6 := by
      rw [← hnorm,Int.natCast_natAbs,← abs_pow,abs_of_nonneg (by positivity)]
    obtain ⟨i,hi⟩ : ∃ i : Fin 6, twistIm i a b = -2 := by
      rcases hforms with hh | hh
      · exact ⟨0,by rw [twist_zero,hh]; decide⟩
      · exact ⟨2,by rw [twist_two,hh]; decide⟩
    let z := (twistBase*(baseUnit:RingEleven)^i.val)*v^6
    have hz : z.im = -2 := (twist_im i v).trans hi
    have hN : z.norm = 5*(t:ℤ)^6 := (twist_norm i v).trans (by rw [hn])
    rw [Zsqrtd.norm_def,hz] at hN
    exact ⟨z.re,by linear_combination hN⟩

#print axioms either_diagonal_cube_iff_sextics


/-- X-coordinates in the positive-k table of Bennett and Ghadermarzi, row 1100. -/
def Mordell1100RowComplete : Prop :=
  ∀ X Y : ℤ, Y^2 = X^3+1100 → X = -10 ∨ X = 5 ∨ X = 14 ∨ X = 245

/-- The numerical completeness premise is separate from the kernel proof. -/
theorem cube_roots_of_mordell_row (row : Mordell1100RowComplete) (t : ℕ) :
    ((∃ n, t^3 = lucasFibonacciSum n) ∨ IsLowerNeighborValue (t^3)) ↔ t=1 ∨ t=7 := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := (cube_norm_iff t).mp h
    have hm := row (5*(t:ℤ)^2) (5*x) (by linear_combination 25*hx)
    rcases hm with h | h | h | h
    · nlinarith [sq_nonneg (t:ℤ)]
    · left; zify; nlinarith [sq_nonneg ((t:ℤ)-1)]
    · omega
    · right; zify; nlinarith [sq_nonneg ((t:ℤ)-7)]
  · rintro (rfl | rfl)
    · exact Or.inl ⟨0,by decide⟩
    · exact Or.inr (Or.inr ⟨10,by decide⟩)

/-- With the published integral-point row, the only cube on the pinned upper
diagonal is its initial 1. The lower diagonal has precisely 343 at actual index 12. -/
theorem cube_indices_of_mordell_row (row : Mordell1100RowComplete) (n m t : ℕ) :
    (lucasFibonacciSum n = t^3 ↔ n=0 ∧ t=1) ∧
    (lowerNeighborAtAddTwo m = t^3 ↔ m=10 ∧ t=7) := by
  have upper : StrictMono lucasFibonacciSum := by
    apply strictMono_nat_of_lt_succ
    intro j
    have h₁ := Nat.fib_add_two_strictMono (Nat.lt_succ_self j)
    have h₂ := Nat.fib_mono (Nat.le_succ j)
    change Nat.fib j ≤ Nat.fib (j+1) at h₂
    change Nat.fib (j+2) < Nat.fib (j+1+2) at h₁
    simp only [lucasFibonacciSum]; omega
  have lower : StrictMono lowerNeighborAtAddTwo := by
    apply strictMono_nat_of_lt_succ
    intro j
    have h₁ := Nat.fib_add_two_strictMono (Nat.lt_succ_self j)
    have h₂ := Nat.fib_mono (Nat.le_succ j)
    change Nat.fib j ≤ Nat.fib (j+1) at h₂
    change Nat.fib (j+2) < Nat.fib (j+1+2) at h₁
    simp only [lowerNeighborAtAddTwo]; omega
  constructor
  · constructor
    · intro h
      rcases (cube_roots_of_mordell_row row _).mp (Or.inl ⟨n,h.symm⟩) with rfl | rfl
      · exact ⟨upper.injective (h.trans (by decide)),rfl⟩
      · have hh := (both_diagonals_iff_five (7^3)).mp ⟨⟨n,h.symm⟩,Or.inr ⟨10,by decide⟩⟩
        norm_num at hh
    · rintro ⟨rfl,rfl⟩; decide
  · constructor
    · intro h
      rcases (cube_roots_of_mordell_row row _).mp (Or.inr (Or.inr ⟨m,h.symm⟩)) with rfl | rfl
      · have hh := (both_diagonals_iff_five (1^3)).mp ⟨⟨0,by decide⟩,Or.inr ⟨m,h.symm⟩⟩
        norm_num at hh
      · exact ⟨lower.injective (h.trans (by decide)),rfl⟩
    · rintro ⟨rfl,rfl⟩; decide

#print axioms cube_roots_of_mordell_row
#print axioms cube_indices_of_mordell_row


open Polynomial
open scoped Polynomial

private def translatedCoeffs (j : Bool) : Fin 7 → ℤ :=
  if j then ![-71180,-98940,-57300,-17700,-3075,-285,-11]
  else ![-20,-660,300,-300,75,-15,1]

private lemma translated_irreducible (j : Bool) :
    Irreducible ((ofFn 7 (translatedCoeffs j)).map (Int.castRingHom ℚ)) := by
  let P := ofFn 7 (translatedCoeffs j)
  have hc (i : Fin 7) : P.coeff i.val = translatedCoeffs j i :=
    ofFn_coeff_eq_val_of_lt _ i.isLt
  have h6 := hc 6
  change P.coeff 6 = _ at h6
  have h5 := hc 5
  change P.coeff 5 = _ at h5
  have hd : P.natDegree = 6 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
    · rw [h6]; cases j <;> decide
  have hI : (Ideal.span {(5:ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr (by decide)
  have hE : P.IsEisensteinAt (Ideal.span {(5:ℤ)}) := by
    constructor
    · rw [leadingCoeff,hd,h6,Ideal.mem_span_singleton]; cases j <;> decide
    · intro n hn
      rw [hd] at hn
      rw [Ideal.mem_span_singleton,show P.coeff n = _ from hc (⟨n,by omega⟩ : Fin 7)]
      exact (by decide : ∀ j : Bool, ∀ i : Fin 7, i.val < 6 → (5:ℤ) ∣ translatedCoeffs j i) _ _ hn
    · rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton,show P.coeff 0 = _ from hc 0]
      cases j <;> decide
  have hprim : P.IsPrimitive := by
    rw [isPrimitive_iff_isUnit_of_C_dvd]
    intro d hdvd
    have h := (C_dvd_iff_dvd_coeff _ _).mp hdvd
    have ha := h 6; rw [h6] at ha
    have hb := h 5; rw [h5] at hb
    apply isUnit_iff_dvd_one.mpr
    cases j
    · exact ha
    · change d ∣ -11 at ha; change d ∣ -285 at hb
      exact (show (-285:ℤ) - (-11)*26 = 1 by decide) ▸ dvd_sub hb (dvd_mul_of_dvd_left ha 26)
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    (hE.irreducible hI hprim (by omega))

/-- After translating X by 1, each dehomogenized sextic is Eisenstein at 5. -/
theorem sextics_irreducible :
    Irreducible (formZero (X : ℚ[X]) 1) ∧ Irreducible (formTwo (X : ℚ[X]) 1) := by
  let E := algEquivAevalXAddC (1:ℚ)
  have h (j : Bool) : E (if j then formTwo X 1 else formZero X 1) =
      (ofFn 7 (translatedCoeffs j)).map (Int.castRingHom ℚ) := by
    rw [ofFn_eq_sum_monomial]
    cases j <;>
      norm_num [formZero,formTwo,sexticReal,sexticHalf,E,algEquivAevalXAddC_apply,
        translatedCoeffs,Fin.sum_univ_succ,← C_mul_X_pow_eq_monomial] <;>
      simp only [map_ofNat] <;> ring
  have hi (j : Bool) : Irreducible (if j then formTwo (X : ℚ[X]) 1 else formZero X 1) := by
    apply (MulEquiv.irreducible_iff (f:=E)).mp
    rw [h]; exact translated_irreducible j
  exact ⟨hi false,hi true⟩

#print axioms sextics_irreducible

end Arxiv.«2211.10788».HosoyaCubes
