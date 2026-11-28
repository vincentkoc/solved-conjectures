import HosoyaTargetLiftIsometry
import LucasFibonacciProgressionClosure

/-! A finite lifting threshold for each integer target on an affine index progression. -/

namespace Arxiv.«2211.10788».LocalPower

open ProgressionClosure

private abbrev U (n : ℕ) : ℤ := lucasFibonacciSum n

/-- One level beyond both target discriminant valuations, with a minimum base
of two for sharp Fibonacci lifting at the prime two. -/
def targetDepth (p : ℕ) (y : ℤ) : ℕ :=
  max 2 (max ((5*y^2+44).natAbs.factorization p) ((5*y^2-44).natAbs.factorization p) + 1)

private lemma valuation_congr {p K : ℕ} (hp : p.Prime) {x y : ℤ}
    (h : x ≡ y [ZMOD (p:ℤ)^K]) (hy0 : y.natAbs ≠ 0) (hy : y.natAbs.factorization p < K) :
    x.natAbs ≠ 0 ∧ x.natAbs.factorization p = y.natAbs.factorization p := by
  let v := y.natAbs.factorization p
  have test (b : ℕ) (hb : b ≤ K) : p^b ∣ x.natAbs ↔ p^b ∣ y.natAbs := by
    have hi := (h.of_dvd (pow_dvd_pow (p:ℤ) hb)).dvd_iff
    simpa only [← Int.natAbs_dvd_natAbs,Int.natAbs_pow,Int.natAbs_natCast] using hi
  have sharp : ¬p^(v+1) ∣ x.natAbs := fun hx =>
    Nat.pow_succ_factorization_not_dvd hy0 hp ((test (v+1) hy).mp hx)
  have hx0 : x.natAbs ≠ 0 := fun hz => sharp (hz ▸ dvd_zero _)
  have low : p^v ∣ x.natAbs := (test v hy.le).mpr (Nat.ordProj_dvd ..)
  refine ⟨hx0,le_antisymm ?_ ((hp.pow_dvd_iff_le_factorization hx0).mp low)⟩
  exact Nat.le_of_not_gt (fun hh => sharp ((hp.pow_dvd_iff_le_factorization hx0).mpr hh))

/-- A hit through the discriminant threshold determines the exact valuation of
its companion. In particular an odd discriminant valuation excludes that parity. -/
theorem target_companion_valuation {p n : ℕ} (hp : p.Prime) (y : ℤ)
    (hit : U n ≡ y [ZMOD (p:ℤ)^(targetDepth p y)]) :
    (coordinate n).natAbs ≠ 0 ∧
      2*(coordinate n).natAbs.factorization p = (5*y^2+44*(-1:ℤ)^n).natAbs.factorization p ∧
      (coordinate n).natAbs.factorization p < targetDepth p y := by
  let D := 5*y^2+44*(-1:ℤ)^n
  have casesD : D = 5*y^2+44 ∨ D = 5*y^2-44 := by
    rcases Nat.even_or_odd n with he|ho
    · exact Or.inl (by simp [D,he.neg_one_pow])
    · exact Or.inr (by simp [D,ho.neg_one_pow]; ring)
  have nz : D ≠ 0 := by rcases casesD with e|e <;> rw [e] <;> omega
  have bound : D.natAbs.factorization p < targetDepth p y := by
    rcases casesD with e|e <;> rw [e] <;> dsimp [targetDepth] <;> omega
  have pell : coordinate n^2 ≡ D [ZMOD (p:ℤ)^(targetDepth p y)] := by
    rw [show coordinate n^2 = 5*(U n)^2+44*(-1:ℤ)^n from PrimeObstruction.upper_signed_pell n]
    exact ((hit.pow 2).mul_left 5).add_right _
  obtain ⟨non,eq⟩ := valuation_congr hp pell (Int.natAbs_ne_zero.mpr nz) bound
  rw [Int.natAbs_pow, Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] at eq
  have hn : (coordinate n).natAbs ≠ 0 := by rw [Int.natAbs_pow] at non; exact fun h => non (by simp [h])
  exact ⟨hn,eq,by omega⟩

#print axioms target_companion_valuation

/-- Twice a Fibonacci return half-step. The extra factor p preserves reduced
parameter classes when their period is multiplied by powers of p. -/
def targetPeriod (p : ℕ) [Fact p.Prime] (y : ℤ) : ℕ :=
  4*p*fibStatePeriod (p^(targetDepth p y))

def targetStepOrder (p : ℕ) [Fact p.Prime] (d : ℕ) (y : ℤ) : ℕ :=
  (Nat.fib (2*d*p*fibStatePeriod (p^(targetDepth p y)))).factorization p

def companionOrder (p n : ℕ) : ℕ := (coordinate n).natAbs.factorization p

/-- Test just the representative of a parameter class at its own lifting depth. -/
def targetGood (p : ℕ) [Fact p.Prime] (r d : ℕ) (y : ℤ) (i : ℕ) : Prop :=
  Hit d r (p^(targetStepOrder p d y+companionOrder p (r+d*i))) y i

theorem targetPeriod_spec (p : ℕ) [Fact p.Prime] (y : ℤ) :
    0 < targetPeriod p y ∧ p ∣ targetPeriod p y := by
  have hp := (Fact.out : p.Prime).pos
  have hT := (midpoint_period (p^(targetDepth p y))).1
  exact ⟨by dsimp [targetPeriod]; positivity,
    (dvd_mul_left p 4).trans (dvd_mul_right _ _)⟩

#print axioms targetPeriod_spec

/-- On each parameter class a single finite test decides all higher powers.
A successful class contributes one residue of the displayed period at each level. -/
theorem fixed_target_branch (p : ℕ) [Fact p.Prime] (r d : ℕ) (hd : 0 < d) (y : ℤ) (i : ℕ) :
    let K := targetDepth p y
    let a := targetStepOrder p d y
    let P := targetPeriod p y
    let v := companionOrder p (r+d*i)
    (¬targetGood p r d y i → ∀ b n : ℕ, ¬Hit d r (p^(a+K+b)) y (i+P*n)) ∧
    (targetGood p r d y i → v < K ∧ ∀ b : ℕ, ∃ z < p^(K-v+b),
      ∀ n : ℕ, Hit d r (p^(a+K+b)) y (i+P*n) ↔ n ≡ z [MOD p^(K-v+b)]) := by
  have hp : p.Prime := Fact.out
  let K := targetDepth p y
  let T := fibStatePeriod (p^K)
  let j := 2*d*p*T
  let a := targetStepOrder p d y
  let P := targetPeriod p y
  let s := r+d*i
  let v := companionOrder p s
  let f (n : ℕ) := U (r+d*(i+P*n))
  have f0 : f 0 = U s := by simp [f,s]
  have feq (n : ℕ) : r+d*(i+P*n) = s+2*j*n := by dsimp [s,j,P,targetPeriod,T,K]; ring
  obtain ⟨hT,hfib,hperiod⟩ := midpoint_period (p^K)
  have hTp : 0 < T := hT
  have hfst : 0 < Nat.fib j := Nat.fib_pos.mpr (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hd) hp.pos) hTp)
  have ha : K ≤ a := by
    apply (hp.pow_dvd_iff_le_factorization hfst.ne').mp
    exact hfib.trans (Nat.fib_dvd _ j (dvd_mul_left T _))
  have h2 : 2 ≤ K := le_max_left ..
  have hf : p^a ∣ Nat.fib j := Nat.ordProj_dvd ..
  have sharp : ¬p^(a+1) ∣ Nat.fib j := Nat.pow_succ_factorization_not_dvd hfst.ne' hp
  have je : Even j := by dsimp [j]; exact ((even_two.mul_right d).mul_right p).mul_right T
  have base (n : ℕ) : f n ≡ U s [ZMOD (p:ℤ)^K] := by
    have eq : r+d*(i+P*n) = s+T*(4*d*p*n) := by dsimp [s,P,targetPeriod,T,K]; ring
    have e := (hperiod s (4*d*p*n)).2
    change (lucasFibonacciSum (r+d*(i+P*n)) : ℤ) ≡ _ [ZMOD _]
    rw [eq]
    simpa only [Nat.cast_pow] using (ZMod.intCast_eq_intCast_iff _ _ (p^K)).mp
      (by simpa only [Int.cast_natCast] using e : ((U (s+T*(4*d*p*n)) : ℤ) : ZMod (p^K)) = (U s : ZMod (p^K)))
  have isom (hit : U s ≡ y [ZMOD (p:ℤ)^K]) : v < K ∧ ∀ b n m : ℕ,
      f n ≡ f m [ZMOD (p:ℤ)^(a+v+b)] ↔ n ≡ m [MOD p^b] := by
    obtain ⟨nz,_,hsmall⟩ := target_companion_valuation hp y hit
    refine ⟨hsmall,fun b n m => ?_⟩
    simp only [f,feq]
    apply midpoint_class_congruence hp je (h2.trans ha) hf sharp
    intro u
    have eq : s+j*u = s+T*(2*d*p*u) := by dsimp [j]; ring
    have hc := (ZMod.intCast_eq_intCast_iff ..).mp (hperiod s (2*d*p*u)).1
    rw [eq]
    exact valuation_congr hp (by simpa only [Nat.cast_pow] using hc) nz hsmall
  have test : targetGood p r d y i ↔ U s ≡ y [ZMOD (p:ℤ)^(a+v)] := by
    simp only [targetGood,Hit,Nat.cast_pow,s,a,v,companionOrder,U]
  have hi (b n : ℕ) : Hit d r (p^(a+K+b)) y (i+P*n) ↔ f n ≡ y [ZMOD (p:ℤ)^(a+K+b)] := by
    simp only [Hit,Nat.cast_pow,f,U]
  constructor
  · intro bad b n hit
    have h := (hi b n).mp hit
    have low : U s ≡ y [ZMOD (p:ℤ)^K] := (base n).symm.trans (h.of_dvd (pow_dvd_pow _ (by omega)))
    obtain ⟨lt,iso⟩ := isom low
    have same := (iso 0 0 n).mpr (by simp [Nat.ModEq,Nat.mod_one])
    rw [f0,Nat.add_zero] at same
    exact bad (test.mpr (same.trans (h.of_dvd (pow_dvd_pow _ (by omega)))))
  · intro good
    have h := test.mp good
    obtain ⟨lt,iso⟩ := isom (h.of_dvd (pow_dvd_pow _ (by omega)))
    refine ⟨lt,fun b => ?_⟩
    obtain ⟨z,hz,ok⟩ := lift_class_of_isometry hp.pos f iso (f0 ▸ h) (K-v+b)
    refine ⟨z,hz,fun n => ?_⟩
    rw [hi,show a+K+b=a+v+(K-v+b) by omega]
    exact ok n

#print axioms fixed_target_branch

end Arxiv.«2211.10788».LocalPower
