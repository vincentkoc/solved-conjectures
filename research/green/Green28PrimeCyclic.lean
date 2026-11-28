import Green28SupportCompression
import Mathlib.Data.ZMod.Basic

/-! Rectification of a small list of sites modulo a prime. -/

namespace Green28PrimeCyclic

/-- Congruence of the pair sums is equivalent to integer equality for these
particular small representatives after multiplication by a nonzero scalar. -/
theorem pair_iff {p : ℕ} [Fact p.Prime] {q w x y z : ZMod p} (qnz : q ≠ 0)
    {a b c d' : ℤ} (ha : (a : ZMod p)=q*w ∧ 5*|a| < (p:ℤ))
    (hb : (b : ZMod p)=q*x ∧ 5*|b| < (p:ℤ))
    (hc : (c : ZMod p)=q*y ∧ 5*|c| < (p:ℤ))
    (hd' : (d' : ZMod p)=q*z ∧ 5*|d'| < (p:ℤ)) :
    w+x=y+z ↔ a+b=c+d' := by
  let d := a+b-c-d'
  have dc : (d : ZMod p) = q*((w+x)-(y+z)) := by dsimp [d]; push_cast; rw [ha.1,hb.1,hc.1,hd'.1]; ring
  constructor
  · intro eq
    have dz : (d : ZMod p) = 0 := by rw [dc,eq,sub_self,mul_zero]
    have divides := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp dz
    have l : -(p:ℤ) < d ∧ d < (p:ℤ) := by
      dsimp [d]
      have e (z : ℤ) : -|z| ≤ z ∧ z ≤ |z| := ⟨neg_abs_le z,le_abs_self z⟩
      have := ha.2; have := hb.2; have := hc.2; have := hd'.2
      have := e (a); have := e (b); have := e (c); have := e (d')
      omega
    have zero : d = 0 := by
      rcases le_or_gt 0 d with hd|hd
      · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hd l.2 divides
      · have := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ -d) (by omega : -d < p) (dvd_neg.mpr divides)
        omega
    dsimp [d] at zero; omega
  · intro eq
    have dz : d = 0 := by dsimp [d]; omega
    rw [dz,Int.cast_zero] at dc
    exact sub_eq_zero.mp ((mul_eq_zero.mp dc.symm).resolve_left qnz)

/-- Multiplication by a nonzero residue puts all sites in an interval of radius
less than one fifth of the modulus. Every equality of two pair sums lifts. -/
theorem rectify {p k : ℕ} [Fact p.Prime] (large : 5^k < p) (x : Fin k → ZMod p) :
    ∃ r : Fin k → ℤ, (∀ i j u v, x i+x j=x u+x v ↔ r i+r j=r u+r v) ∧
      ∃ q : ℕ, 0 < q ∧ q < p ∧ ∀ i, ((r i : ℤ) : ZMod p) = q*x i ∧
        5*|r i| < (p : ℤ) := by
  obtain ⟨q,hq,qu,b,approx⟩ := Green28SupportCompression.simultaneous_fifths
    (fun i => ((x i).val : ℝ)/p)
  have qp := lt_of_le_of_lt qu large
  have pp : 0 < p := (Fact.out : p.Prime).pos
  have pr : (0:ℝ) < p := by exact_mod_cast pp
  let r (i : Fin k) : ℤ := (q:ℤ)*(x i).val-(p:ℤ)*b i
  have cast (i) : ((r i : ℤ) : ZMod p) = q*x i := by simp [r]
  have rad (i) : 5*|r i| < (p : ℤ) := by
    have eq : (r i : ℝ) = ((q:ℝ)*((x i).val/p)-b i)*p := by
      dsimp [r]
      push_cast
      field_simp
    have lt := mul_lt_mul_of_pos_right (approx i) pr
    have e := congrArg abs eq
    rw [abs_mul,abs_of_pos pr] at e
    have : (5:ℝ)*|(r i : ℝ)| < (p:ℝ) := by linarith
    exact_mod_cast this
  have qnz : (q : ZMod p) ≠ 0 := by
    intro eq
    have dvd := (ZMod.natCast_eq_zero_iff q p).mp eq
    exact qp.not_ge (Nat.le_of_dvd hq dvd)
  refine ⟨r,?_,q,hq,qp,fun i => ⟨cast i,rad i⟩⟩
  exact fun i j u v => pair_iff qnz ⟨cast i,rad i⟩ ⟨cast j,rad j⟩ ⟨cast u,rad u⟩ ⟨cast v,rad v⟩

#print axioms rectify

end Green28PrimeCyclic
