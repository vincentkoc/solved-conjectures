import ThetaReciprocalCutoff
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Fourier.ZMod

/-! Parity cancellation in the residue fibers of the rational theta remainder. -/

namespace Arxiv.«2501.03234».ThetaReciprocalFibers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

private lemma coprime_sieve {m : ℕ} (hm : m≠0) (y : ℕ) :
    (if y.Coprime m then (1:ℤ) else 0) =
      ∑ e ∈ m.divisors, if e ∣ y then μ e else 0 := by
  have hg : y.gcd m ≠ 0 := (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hm)).ne'
  have H : m.divisors.filter (· ∣ y) = (y.gcd m).divisors := by
    ext e; simp only [mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
    tauto
  rw [← sum_filter,H,← coe_mul_zeta_apply,moebius_mul_coe_zeta,one_apply]

private lemma abs_alternating (n : ℕ) : |∑ j ∈ range n, (-1:ℤ)^j| ≤ 1 := by
  have h := geom_sum_mul (-1:ℤ) n
  rcases Nat.even_or_odd n with he|ho
  · rw [he.neg_one_pow] at h
    rw [abs_le]; constructor <;> linarith
  · rw [ho.neg_one_pow] at h
    rw [abs_le]; constructor <;> linarith

private lemma sum_one_class (f : ℕ → ℤ) {e m r : ℕ} (he : 0<e) (hem : e∣m) (hr : r<e) :
    ∑ i ∈ (range m).filter (fun i => i%e=r), f i = ∑ j ∈ range (m/e), f (r+e*j) := by
  apply sum_bij (fun i _ => i/e)
  · intro i hi
    have hh := mem_range.mp (mem_filter.mp hi).1
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul he).mpr (by rwa [Nat.div_mul_cancel hem]))
  · intro a ha b hb hab
    have h₁ := (mem_filter.mp ha).2
    have h₂ := (mem_filter.mp hb).2
    have ha' := Nat.mod_add_div a e
    have hb' := Nat.mod_add_div b e
    rw [h₁,hab] at ha'; rw [h₂] at hb'; omega
  · intro j hj
    have hj' := mem_range.mp hj
    have hlt := Nat.mul_le_mul_left e (show j + 1 ≤ m / e by omega)
    rw [Nat.mul_div_cancel' hem] at hlt
    have hi : r+e*j < m := by nlinarith
    refine ⟨r+e*j,mem_filter.mpr ⟨mem_range.mpr hi,by simp [Nat.mod_eq_of_lt hr]⟩,?_⟩
    simp [Nat.add_mul_div_left _ _ he,Nat.div_eq_of_lt hr]
  · intro i hi
    congr 1
    have h := Nat.mod_add_div i e
    rw [(mem_filter.mp hi).2] at h
    exact h.symm

private lemma divisibility_class {b q e : ℕ} (h : b.Coprime q) {j : ℕ} (hj : e∣b+q*j)
    (i : ℕ) : e∣b+q*i ↔ i%e=j%e := by
  have hy : (b+q*j).Coprime q := by simpa using h
  have hqe : q.Coprime e := (hy.coprime_dvd_left hj).symm
  have hunit := (ZMod.unitOfCoprime q hqe).isUnit
  have hu : IsUnit (q:ZMod e) := by simpa only [ZMod.coe_unitOfCoprime] using hunit
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hj
  rw [← ZMod.natCast_eq_zero_iff,Nat.cast_add,Nat.cast_mul]
  push_cast at hz
  change _ ↔ i ≡ j [MOD e]
  rw [← ZMod.natCast_eq_natCast_iff]
  constructor
  · intro H; apply hu.mul_left_cancel; linear_combination H-hz
  · intro H; rwa [H]

private lemma divisor_wave {m q e b : ℕ} (hm : m%2=1) (hq : q%2=1) (hb : b.Coprime q)
    (hem : e∣m) :
    |∑ i ∈ (range m).filter (fun i => e∣b+q*i), (-1:ℤ)^(b+q*i)| ≤ 1 := by
  by_cases ha : ((range m).filter (fun i => e∣b+q*i)).Nonempty
  · obtain ⟨j,hj⟩ := ha
    have hclass := divisibility_class hb (mem_filter.mp hj).2
    have he : 0<e := Nat.pos_of_dvd_of_pos hem (by omega)
    have heodd : Odd e := (Nat.odd_iff.mpr hm).of_dvd_nat hem
    simp_rw [hclass]
    rw [sum_one_class _ he hem (Nat.mod_lt _ he)]
    have hh (k : ℕ) : (-1:ℤ)^(b+q*(j%e+e*k)) = (-1)^(b+q*(j%e)) * (-1)^k := by
      rw [show b+q*(j%e+e*k)=(b+q*(j%e))+(q*e)*k by ring,pow_add,pow_mul,
        ((Nat.odd_iff.mpr hq).mul heodd).neg_one_pow]
    simp_rw [hh]
    rw [← mul_sum,abs_mul]; simpa [abs_pow] using abs_alternating (m/e)
  · simp [not_nonempty_iff_eq_empty.mp ha]

/-- A residue class of step q has bounded signed unit mass in the odd modulus q*m. -/
theorem coprime_fiber_bound {m q b : ℕ} (hm : m%2=1) (hq : q%2=1) (hb : b.Coprime q) :
    |∑ i ∈ range m, if (b+q*i).Coprime m then (-1:ℤ)^(b+q*i) else 0| ≤ m.divisors.card := by
  have he (i : ℕ) : (if (b+q*i).Coprime m then (-1:ℤ)^(b+q*i) else 0) =
      ∑ e ∈ m.divisors, μ e * (if e∣b+q*i then (-1:ℤ)^(b+q*i) else 0) := by
    rw [show (if (b+q*i).Coprime m then (-1:ℤ)^(b+q*i) else 0) =
      (if (b+q*i).Coprime m then 1 else 0) * (-1:ℤ)^(b+q*i) by split_ifs <;> simp,
      coprime_sieve (by omega : m≠0),sum_mul]
    apply sum_congr rfl; intro e _; split_ifs <;> simp
  simp_rw [he]; rw [sum_comm]
  simp_rw [← mul_sum,← sum_filter]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ e ∈ m.divisors, (1:ℤ) := by
      apply sum_le_sum; intro e he
      rw [abs_mul]
      have hμ : |μ e|≤1 := by rcases moebius_eq_or e with h|h|h <;> rw [h] <;> norm_num
      exact (mul_le_mul hμ (divisor_wave hm hq hb (Nat.dvd_of_mem_divisors he))
        (abs_nonneg _) zero_le_one).trans (by norm_num)
    _ = _ := by simp

private abbrev unitsMod (n : ℕ) := (ZMod n)ˣ

/-- Reduction of units from modulus `q*m` to modulus `q`. -/
def reduceUnit (q m : ℕ) : unitsMod (q*m) →* unitsMod q :=
  Units.map (ZMod.castHom (Nat.dvd_mul_right q m) (ZMod q)).toMonoidHom

private lemma reduce_val (q m : ℕ) [NeZero (q*m)] (x : unitsMod (q*m)) :
    (reduceUnit q m x : ZMod q) = (((x : ZMod (q*m)).val : ℕ) : ZMod q) := by
  change ZMod.castHom _ _ (x : ZMod (q*m)) = _
  rw [← ZMod.natCast_zmod_val (x : ZMod (q*m)),map_natCast,ZMod.natCast_zmod_val]

/-- Sum over the least nonnegative representatives of all units. -/
theorem unit_sum_nat {A : Type*} [AddCommMonoid A] {n : ℕ} [NeZero n] (f : ℕ → A) :
    ∑ x : unitsMod n, f (x : ZMod n).val = ∑ j ∈ (range n).filter (·.Coprime n), f j := by
  apply sum_bij (fun (x : unitsMod n) _ => (x : ZMod n).val)
  · intro x _
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime x⟩
  · intro x _ y _ he
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun z : ℕ => (z : ZMod n)) he
  · intro j hj
    obtain ⟨hlt,hc⟩ := mem_filter.mp hj
    exact ⟨ZMod.unitOfCoprime j hc, mem_univ _, by rw [ZMod.coe_unitOfCoprime,
      ZMod.val_natCast_of_lt (mem_range.mp hlt)]⟩
  · intros; rfl

/-- Sum an arbitrary integer weight over a fixed reduced residue fiber. -/
theorem sum_unit_fiber {q m : ℕ} [NeZero q] [NeZero (q*m)] (b : (ZMod q)ˣ) (f : ℕ → ℤ) :
    (∑ x : (ZMod (q*m))ˣ, if reduceUnit q m x = b then f (x : ZMod (q*m)).val else 0) =
    ∑ i ∈ range m, if ((b : ZMod q).val+q*i).Coprime m
      then f ((b : ZMod q).val+q*i) else 0 := by
  let r := (b : ZMod q).val
  have hr : r<q := ZMod.val_lt _
  have hb : r.Coprime q := ZMod.val_coe_unit_coprime _
  have htest (x : unitsMod (q*m)) : reduceUnit q m x = b ↔ (x : ZMod (q*m)).val%q=r := by
    rw [← Units.val_inj,reduce_val]
    constructor
    · intro H; simpa only [ZMod.val_natCast] using congrArg ZMod.val H
    · intro H; apply_fun (fun j : ℕ => (j : ZMod q)) at H
      simpa only [ZMod.natCast_mod,ZMod.natCast_zmod_val,r] using H
  simp_rw [htest]
  rw [unit_sum_nat (fun j => if j%q=r then f j else 0),sum_filter]
  have hs (j : ℕ) : (if j.Coprime (q*m) then (if j%q=r then f j else 0) else 0) =
      (if j%q=r then (if j.Coprime (q*m) then f j else 0) else 0) := by
    split_ifs <;> rfl
  simp_rw [hs]; rw [← sum_filter,sum_one_class _ (NeZero.pos _) (Nat.dvd_mul_right q m) hr,
    Nat.mul_div_cancel_left _ (NeZero.pos q)]
  apply sum_congr rfl; intro i _
  change (if (r+q*i).Coprime (q*m) then _ else _) = (if (r+q*i).Coprime m then _ else _)
  have hc : (r+q*i).Coprime q := by simpa using hb
  by_cases h : (r+q*i).Coprime m
  · rw [if_pos (Nat.coprime_mul_iff_right.mpr ⟨hc,h⟩),if_pos h]
  · rw [if_neg (fun H => h (Nat.coprime_mul_iff_right.mp H).2),if_neg h]

/-- Reciprocal multiplication permutes units. Each reduced residue fiber of its parity
sign has discrepancy at most the number of divisors of the quotient modulus. -/
theorem reciprocal_unit_fiber {q m : ℕ} [NeZero q] [NeZero (q*m)] (hm : m%2=1) (hq : q%2=1)
    (v : (ZMod (q*m))ˣ) (a : (ZMod q)ˣ) :
    |∑ x : (ZMod (q*m))ˣ, if reduceUnit q m x = a then
      (-1:ℤ)^((↑(v/x) : ZMod (q*m)).val) else 0| ≤ m.divisors.card := by
  classical
  let b := reduceUnit q m v/a
  have h (x : unitsMod (q*m)) : reduceUnit q m (v/x) = a ↔ reduceUnit q m x = b := by
    rw [map_div]; dsimp [b]; rw [div_eq_iff_eq_mul,eq_div_iff_mul_eq',mul_comm a,eq_comm]
  have H : (∑ x : unitsMod (q*m), if reduceUnit q m x = a then (-1:ℤ)^((↑(v/x) : ZMod (q*m)).val) else 0) =
      ∑ x : unitsMod (q*m), if reduceUnit q m x = b then (-1:ℤ)^(x : ZMod (q*m)).val else 0 := by
    have inv : Function.Involutive (fun x : unitsMod (q*m) => v/x) := by intro x; exact div_div_cancel v x
    apply Fintype.sum_bijective (fun x => v/x) inv.bijective
    intro x
    have hh := h (v/x)
    rw [show v/(v/x)=x by exact inv x] at hh
    simp only [hh]
  rw [H,sum_unit_fiber _ (fun j => (-1:ℤ)^j)]
  exact coprime_fiber_bound hm hq (ZMod.val_coe_unit_coprime b)

private lemma neg_residue_sign {p t u v : ℕ} (hu : u%2=1) (hv : 0<v) (hvu : v<u)
    (hc : p.Coprime u) (ht : u ∣ t+p) :
    ThetaCotangentTriangle.reciprocalSign t u v = -ThetaCotangentTriangle.reciprocalSign p u v := by
  let : NeZero u := ⟨by omega⟩
  have htp : (t : ZMod u) = -(p : ZMod u) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [Nat.cast_add] using (ZMod.natCast_eq_zero_iff _ _).mpr ht
  have hmul := ZMod.coe_mul_inv_eq_one p hc
  have hi : (t : ZMod u)⁻¹ = -(p : ZMod u)⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [htp,neg_mul_neg,hmul]
  let y := (v : ZMod u)*(p : ZMod u)⁻¹
  have hy : y ≠ 0 := by
    intro H
    have h := congrArg (·*(p : ZMod u)) H
    dsimp [y] at h
    rw [mul_assoc,mul_comm ((p : ZMod u)⁻¹),hmul,mul_one,zero_mul] at h
    have hh := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hvu,ZMod.val_zero] at hh; omega
  let : NeZero y := ⟨hy⟩
  unfold ThetaCotangentTriangle.reciprocalSign
  rw [hi,mul_neg]
  change (if (-y).val%2=1 then _ else _) = -(if y.val%2=1 then _ else _)
  rw [ZMod.val_neg_of_ne_zero y]
  have := ZMod.val_lt y
  split_ifs <;> omega

/-- On any complete system of reduced residues modulo a common multiple of the odd
denominators, negation reverses the full rational cutoff. Numerators need not be units. -/
theorem rationalPrefix_neg {L J : ℕ} [NeZero L]
    (hL : ∀ j < J, 2*j+1 ∣ L) (a : (ZMod L)ˣ) :
    ThetaReciprocalCutoff.rationalPrefix (↑(-a) : ZMod L).val J =
      -ThetaReciprocalCutoff.rationalPrefix (a : ZMod L).val J := by
  have hzero : L ∣ (↑(-a) : ZMod L).val + (a : ZMod L).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simp
  unfold ThetaReciprocalCutoff.rationalPrefix
  rw [← sum_neg_distrib]
  apply sum_congr rfl; intro j hj
  rw [← sum_neg_distrib]
  apply sum_congr rfl; intro k hk
  have hj' := mem_range.mp hj
  have hk' := mem_range.mp hk
  rw [neg_residue_sign (by omega) (by omega) (by omega)
    ((ZMod.val_coe_unit_coprime a).coprime_dvd_right (hL j hj')) ((hL j hj').trans hzero)]
  push_cast; ring

/-- The signed first moment of the rational cutoff over a complete unit group is exactly zero. -/
theorem rationalPrefix_unit_mean {L J : ℕ} [NeZero L] (hL : ∀ j < J, 2*j+1 ∣ L) :
    ∑ a : (ZMod L)ˣ, ThetaReciprocalCutoff.rationalPrefix (a : ZMod L).val J = 0 := by
  let f (a : (ZMod L)ˣ) := ThetaReciprocalCutoff.rationalPrefix (a : ZMod L).val J
  have he : ∑ a, f a = ∑ a, f (-a) :=
    (Fintype.sum_equiv (Equiv.neg _) (fun a => f (-a)) f (by intros; rfl)).symm
  have hf (a : (ZMod L)ˣ) : f (-a) = -f a := rationalPrefix_neg hL a
  simp_rw [hf] at he
  rw [sum_neg_distrib] at he
  change ∑ a, f a = 0
  linarith

open scoped ComplexConjugate

private lemma orthogonal {q : ℕ} [NeZero q] (a : ZMod q) :
    ∑ h : ZMod q, ZMod.stdAddChar (a*h) = if a=0 then (q : ℂ) else 0 := by
  split_ifs with ha
  · simp [ha,ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ha)

private lemma conj_char {q : ℕ} [NeZero q] (x : ZMod q) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply,← Circle.coe_inv_eq_conj,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv]

/-- Parseval for an integer weight on the additive residues, with an unnormalized transform. -/
theorem integer_parseval {q : ℕ} [NeZero q] (f : ZMod q → ℤ) :
    ∑ h : ZMod q, ‖∑ a : ZMod q, (f a : ℂ)*ZMod.stdAddChar (a*h)‖^2 =
      (q : ℝ)*∑ a : ZMod q, (f a : ℝ)^2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj',map_sum,map_mul,map_intCast,conj_char,sum_mul,mul_sum]
  have he (a b h : ZMod q) :
      (f a : ℂ)*ZMod.stdAddChar (a*h)*((f b : ℂ)*ZMod.stdAddChar (-(b*h))) =
        ((f a : ℂ)*f b)*ZMod.stdAddChar ((a-b)*h) := by
    rw [sub_mul,sub_eq_add_neg,AddChar.map_add_eq_mul]; ring
  simp_rw [he]
  rw [sum_comm]
  simp_rw [sum_comm (f := fun h b : ZMod q => _ * ZMod.stdAddChar ((_ - b)*h)),
    ← mul_sum,orthogonal,sub_eq_zero,mul_ite,mul_zero,sum_ite_eq,mem_univ,if_true]
  rw [mul_sum]
  apply sum_congr rfl; intro a _; ring

private noncomputable def fiberMass (q m : ℕ) [NeZero (q*m)]
    (v : (ZMod (q*m))ˣ) (a : ZMod q) : ℤ :=
  ∑ x : (ZMod (q*m))ˣ, if (reduceUnit q m x : ZMod q)=a then
    (-1:ℤ)^((↑(v/x) : ZMod (q*m)).val) else 0

private lemma fiberMass_bound {q m : ℕ} [NeZero q] [NeZero (q*m)]
    (hm : m%2=1) (hq : q%2=1) (v : (ZMod (q*m))ˣ) (a : ZMod q) :
    |fiberMass q m v a| ≤ m.divisors.card := by
  by_cases ha : IsUnit a
  · obtain ⟨b,rfl⟩ := ha
    simpa only [fiberMass,Units.val_inj] using reciprocal_unit_fiber hm hq v b
  · have he (x : (ZMod (q*m))ˣ) : (reduceUnit q m x : ZMod q) ≠ a :=
      fun H => ha (H ▸ (reduceUnit q m x).isUnit)
    simp [fiberMass,he]

/-- Normalized coefficient of the reciprocal parity sign at a frequency of denominator q.
The sign is positive on odd least representatives; nonunits have zero weight. -/
noncomputable def reciprocalCoeff (q m : ℕ) [NeZero q] [NeZero (q*m)]
    (v : (ZMod (q*m))ˣ) (h : ZMod q) : ℂ :=
  -(∑ x : (ZMod (q*m))ˣ, ((-1 : ℤ)^((↑(v/x) : ZMod (q*m)).val) : ℂ) *
    ZMod.stdAddChar ((reduceUnit q m x : ZMod q)*h)) / ((q : ℂ)*m)

private lemma coeff_as_fibers {q m : ℕ} [NeZero q] [NeZero (q*m)]
    (v : (ZMod (q*m))ˣ) (h : ZMod q) :
    reciprocalCoeff q m v h =
    -(∑ a : ZMod q, (fiberMass q m v a : ℂ)*ZMod.stdAddChar (a*h)) / ((q : ℂ)*m) := by
  unfold reciprocalCoeff fiberMass
  congr 2
  push_cast
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro x _
  simp

/-- The total squared Fourier mass seen at a projected denominator is at most
`(τ(m)/m)^2`, uniformly in the primitive numerator, the cutoff and q. -/
theorem reciprocalCoeff_energy {q m : ℕ} [NeZero q] [NeZero (q*m)]
    (hm : m%2=1) (hq : q%2=1) (v : (ZMod (q*m))ˣ) :
    ∑ h : ZMod q, ‖reciprocalCoeff q m v h‖^2 ≤ ((m.divisors.card : ℝ)/m)^2 := by
  simp_rw [coeff_as_fibers,norm_div,norm_neg,norm_mul,Complex.norm_natCast,div_pow,
    ← sum_div,integer_parseval]
  have hh : ∑ a : ZMod q, (fiberMass q m v a : ℝ)^2 ≤ q * (m.divisors.card : ℝ)^2 := by
    calc
      _ ≤ ∑ a : ZMod q, (m.divisors.card : ℝ)^2 := by
        apply sum_le_sum; intro a _
        have h : |(fiberMass q m v a : ℝ)| ≤ m.divisors.card := by exact_mod_cast fiberMass_bound hm hq v a
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = _ := by simp [ZMod.card]
  have hq' : 0<(q : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hm' : 0<(m : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hq'.le (sq_nonneg (m : ℝ))) (sub_nonneg.mpr hh)]

/-- Cancelling a common odd factor of numerator and modulus preserves the reciprocal
parity sign whenever the argument is a unit modulo the original modulus. -/
theorem reciprocalSign_cancel {p g d w : ℕ} (hg : g%2=1) (hd : 0<d)
    (hc : p.Coprime (g*d)) :
    ThetaCotangentTriangle.reciprocalSign p (g*d) (g*w) =
      ThetaCotangentTriangle.reciprocalSign p d w := by
  have hg' : 0<g := by omega
  let : NeZero (g*d) := ⟨(Nat.mul_pos hg' hd).ne'⟩
  let : NeZero d := ⟨hd.ne'⟩
  let t := ((p : ZMod (g*d))⁻¹).val
  have hcast : (t : ZMod (g*d)) = (p : ZMod (g*d))⁻¹ := ZMod.natCast_zmod_val _
  let ρ := ZMod.castHom (dvd_mul_left d g) (ZMod d)
  have h₀ : (p : ZMod d)*(t : ZMod d)=1 := by
    have h : (p : ZMod (g*d))*(t : ZMod (g*d))=1 := hcast ▸ (ZMod.coe_mul_inv_eq_one p hc)
    simpa only [map_mul,map_natCast,map_one] using congrArg ρ h
  have h₁ : (p : ZMod d)⁻¹=(t : ZMod d) := ZMod.inv_eq_of_mul_eq_one _ _ _ h₀
  unfold ThetaCotangentTriangle.reciprocalSign
  rw [← hcast,h₁,← Nat.cast_mul,← Nat.cast_mul,ZMod.val_natCast,ZMod.val_natCast,
    Nat.mul_assoc,Nat.mul_mod_mul_left,Nat.mul_mod _ _ 2,hg,one_mul,Nat.mod_mod]


end Arxiv.«2501.03234».ThetaReciprocalFibers
#print axioms Arxiv.«2501.03234».ThetaReciprocalFibers.coprime_fiber_bound
#print axioms Arxiv.«2501.03234».ThetaReciprocalFibers.unit_sum_nat
#print axioms Arxiv.«2501.03234».ThetaReciprocalFibers.reciprocal_unit_fiber
#print axioms Arxiv.«2501.03234».ThetaReciprocalFibers.rationalPrefix_neg
#print axioms Arxiv.«2501.03234».ThetaReciprocalFibers.rationalPrefix_unit_mean
#print axioms Arxiv.«2501.03234».ThetaReciprocalFibers.integer_parseval
#print axioms Arxiv.«2501.03234».ThetaReciprocalFibers.reciprocalCoeff_energy
#print axioms Arxiv.«2501.03234».ThetaReciprocalFibers.reciprocalSign_cancel
#print axioms Arxiv.«2501.03234».ThetaReciprocalFibers.sum_unit_fiber
