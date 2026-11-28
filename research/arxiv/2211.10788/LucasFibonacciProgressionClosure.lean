import HosoyaProgressionDetection

/-! An effective local-global criterion for the canonical upper sequence on any index progression. -/

namespace Arxiv.«2211.10788».ProgressionClosure

open CongruenceClosure

/-- The same detecting modulus works for every offset of a given positive step. -/
def modulus (d : ℕ) (y : ℤ) := Nat.lcm 11 (lucas (window d y))

/-- Number of progression terms sufficient for testing that modulus. -/
def testCount (y : ℤ) := 40*((threshold y).log2+1)

/-- A congruence for the canonical nonnegative-index sequence on the progression. -/
def Hit (d r M : ℕ) (y : ℤ) (t : ℕ) : Prop :=
  (lucasFibonacciSum (r+d*t) : ℤ) ≡ y [ZMOD M]

private lemma modulus_pos {d : ℕ} (hd : 0 < d) (y : ℤ) : 0 < modulus d y :=
  Nat.lcm_pos (by decide) (Nat.zero_lt_of_lt (window_size hd y))

private lemma split_hit {d r t : ℕ} {y : ℤ} :
    Hit d r (modulus d y) y t ↔ Hit d r 11 y t ∧ Hit d r (lucas (window d y)) y t :=
  (Int.modEq_and_modEq_iff_modEq_lcm (m := 11) (n := (lucas (window d y) : ℤ))).symm

private lemma hit_cast {d r M t : ℕ} {y : ℤ} :
    Hit d r M y t ↔ (signed ((r+d*t:ℕ):ℤ) : ZMod M) = y := by
  rw [signed_nat]
  exact (ZMod.intCast_eq_intCast_iff ..).symm

private lemma bounded_test {d r t : ℕ} {y : ℤ} (hit : Hit d r (modulus d y) y t) :
    Hit d r (modulus d y) y (t%testCount y) := by
  let P := testCount y
  let q := t/P
  let x := r+d*(t%P)
  let h := window d y
  have ht : t%P+P*q = t := Nat.mod_add_div _ _
  have e : x+(d*P)*q = r+d*t := by
    dsimp [x]
    calc _ = r+d*(t%P+P*q) := by ring
         _ = _ := by rw [ht]
  obtain ⟨a,b⟩ := split_hit.mp hit
  apply split_hit.mpr
  constructor
  · apply hit_cast.mpr
    have ha := hit_cast.mp a
    simp only [signed_nat,Int.cast_natCast,upper_mod_eleven] at ha ⊢
    change (4 : ZMod 11)^x = y
    rw [←e,pow_add,show d*P*q = 5*(8*d*((threshold y).log2+1)*q) by dsimp [P,testCount]; ring,
      pow_mul,show (4 : ZMod 11)^5 = 1 by decide,one_pow,mul_one] at ha
    exact ha
  · apply hit_cast.mpr
    have hb := hit_cast.mp b
    have even : Even h := ⟨d*((threshold y).log2+1),by dsimp [h,window]; omega⟩
    have ep : ((r+d*t:ℕ):ℤ) = (x:ℤ)+(5*q:ℤ)*(4*h) := by
      rw [←e]; dsimp [P,testCount,h,window]; ring
    rw [ep] at hb
    exact ((lucas_period even).int_mul (5*q) (x:ℤ)).symm.trans hb

/-- One modular hit recovers an exact signed hit in the prescribed class and bounded window. -/
theorem modulus_hit_lifts {d r t : ℕ} (hd : 0 < d) {y : ℤ}
    (hit : Hit d r (modulus d y) y t) :
    ∃ w : ℤ, w ≡ r [ZMOD d] ∧ w.natAbs ≤ window d y ∧ signed w = y := by
  let b := (threshold y).log2+1
  have hp : 0 < window d y := by dsimp [window]; positivity
  have he : Even (window d y) := ⟨d*b, by dsimp [window,b]; omega⟩
  obtain ⟨h11,hL⟩ := split_hit.mp hit
  obtain ⟨w,q,eq,hw,hy⟩ := lift_at_lucas hp he (window_size hd y)
    (hit_cast.mp h11) (hit_cast.mp hL)
  refine ⟨w,Int.modEq_iff_dvd.mpr ⟨4*(b:ℤ)*q-t,?_⟩,hw,hy⟩
  change ((r+d*t:ℕ):ℤ) = w+2*(2*(d*b):ℕ)*q at eq
  push_cast at eq
  linarith

private lemma all_hits_of_signed {d r : ℕ} {y w : ℤ}
    (hw : w ≡ r [ZMOD d]) (hy : signed w = y) :
    ∀ M > 0, ∃ t, Hit d r M y t := by
  intro M hM
  let : NeZero M := ⟨hM.ne'⟩
  obtain ⟨k,hk⟩ := hw.dvd
  have he : w = r+d*(-k) := by linarith
  obtain ⟨t,ht⟩ := signed_progression_hit M d r (-k)
  refine ⟨t,hit_cast.mpr ?_⟩
  simpa only [signed_nat,Int.cast_natCast,←he,hy] using ht

/-- All-moduli solvability on a forward progression equals exact bilateral solvability in its class. -/
theorem progression_local_global {d : ℕ} (hd : 0 < d) (r : ℕ) (y : ℤ) :
    (∀ M > 0, ∃ t, Hit d r M y t) ↔ ∃ w : ℤ, w ≡ r [ZMOD d] ∧ signed w = y := by
  constructor
  · intro all
    obtain ⟨t,ht⟩ := all _ (modulus_pos hd y)
    obtain ⟨w,hw,_,hy⟩ := modulus_hit_lifts hd ht
    exact ⟨w,hw,hy⟩
  · rintro ⟨w,hw,hy⟩
    exact all_hits_of_signed hw hy

/-- One modulus and a number of progression terms independent of the step and offset suffice. -/
theorem progression_finite_test {d : ℕ} (hd : 0 < d) (r : ℕ) (y : ℤ) :
    (∀ M > 0, ∃ t, Hit d r M y t) ↔ ∃ t < testCount y, Hit d r (modulus d y) y t := by
  constructor
  · intro all
    obtain ⟨t,ht⟩ := all _ (modulus_pos hd y)
    exact ⟨_,Nat.mod_lt _ (by dsimp [testCount]; positivity),bounded_test ht⟩
  · rintro ⟨t,_,ht⟩
    obtain ⟨w,hw,_,hy⟩ := modulus_hit_lifts hd ht
    exact all_hits_of_signed hw hy

#print axioms modulus_hit_lifts
#print axioms progression_local_global
#print axioms progression_finite_test

end Arxiv.«2211.10788».ProgressionClosure
