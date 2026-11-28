import ThetaUnitExposure

/-! Contributions from revealing one prime power in the unit filtration. -/
namespace Arxiv.«2501.03234».ThetaExposureLayers
open Finset Real ThetaFiniteExposure ThetaSmoothFiltration ThetaUnitExposure
open ThetaPrimeTailTransfer ThetaSmoothConditionalModel
noncomputable section

def value (Y : ℕ) (V : Window) (t : ℕ) [NeZero Y.factorial] (x : (ZMod Y.factorial)ˣ) : ℝ :=
  proj (key (modulus Y.factorial t)) (fun u : (ZMod Y.factorial)ˣ => rowModel Y V (u:ZMod Y.factorial).val) x

theorem baseline {Y t : ℕ} [NeZero Y.factorial] (hY : 2≤Y) (ht : 2≤t)
    (hl : 1≤log t) (V : Window) (x : (ZMod Y.factorial)ˣ) :
    |value Y V t x| ≤ envelope*(238*(log t)^2) := by
  have hm := pos (Nat.factorial_pos Y) t
  let : NeZero (modulus Y.factorial t) := ⟨hm.ne'⟩
  rw [value,project (divides (Nat.factorial_pos Y) t)]
  exact smooth_bound (two_le hY ht) (Nat.mod_lt _ hm) (key_unit (divides (Nat.factorial_pos Y) t) x)
    (divides (Nat.factorial_pos Y) t) (by omega) hl (prime_bound _ _) V

theorem oscillation {Y t : ℕ} [NeZero Y.factorial] (hl : 1≤log (t+1:ℕ))
    (V : Window) (x y : (ZMod Y.factorial)ˣ) (he : key (modulus Y.factorial t) x=key (modulus Y.factorial t) y) :
    |value Y V (t+1) x-value Y V (t+1) y| ≤ 544*envelope*(log (t+1:ℕ))^2/(t+1:ℕ) := by
  let P := Y.factorial
  let m := modulus P (t+1)
  let n := modulus P t
  let q := t+1
  have hm := pos (Nat.factorial_pos Y) (t+1)
  have hn := pos (Nat.factorial_pos Y) t
  have hd := divides (Nat.factorial_pos Y) (t+1)
  have hh : m=n*q^P.factorization q := next _ _
  have hnm : n∣m := hh ▸ dvd_mul_right ..
  by_cases ha : P.factorization q=0
  · have heq : m=n := by simpa only [ha,pow_zero,mul_one] using hh
    change |proj (key m) _ x-proj (key m) _ y|≤_
    rw [heq]
    change key n x=key n y at he
    simp only [proj,he,sub_self,abs_zero]
    positivity [envelope_nonneg]
  · have hq := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr ha : q∈P.primeFactors)
    let : NeZero (modulus Y.factorial (t+1)) := ⟨hm.ne'⟩
    rw [value,value,project hd,project hd]
    apply ThetaPrimeCoordinate.smooth_oscillation hq (Nat.pos_of_ne_zero ha) hh hn hd
      (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) (key_unit hd x) (key_unit hd y) _ hl
      (prime_bound _ _) V
    simpa only [Nat.ModEq,key,Nat.mod_mod_of_dvd _ hnm] using he

theorem one_step {Y t : ℕ} [NeZero Y.factorial] (hl : 1≤log (t+1:ℕ))
    (V : Window) {v a : ℝ} (ha : 544*envelope*(log (t+1:ℕ))^2/(t+1:ℕ)≤a)
    (hs : |v| * a≤1) :
    (∑ x,exp (v*value Y V (t+1) x)) ≤ exp (v^2*a^2)*∑ x,exp (v*value Y V t x) := by
  have hd : modulus Y.factorial t∣modulus Y.factorial (t+1) := by rw [next]; exact dvd_mul_right ..
  apply step _ _ _ (refine hd) (le_trans (by positivity [envelope_nonneg]) ha) hs
  exact fun x y he => (oscillation hl V x y he).trans ha

#print axioms baseline
#print axioms one_step
end
end Arxiv.«2501.03234».ThetaExposureLayers
