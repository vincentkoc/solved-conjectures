import FormalConjectures.Arxiv.«1104.1579».CunninghamChain
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

/-! Affine families on one Cunningham orbit with prescribed composite positions. -/

namespace CunninghamChain.PrimeReturns
open Finset

/-- With center x, the seeds are x−1 for the first kind and x+1 for the second. -/
def orbitValue (first : Bool) (x i : ℕ) : ℕ :=
  if first then 2^i*x-1 else 2^i*x+1

private def offset (first : Bool) (R : Type*) [Ring R] : R :=
  if first then -1 else 1

private theorem cast_orbit (first : Bool) (R : Type*) [Ring R] (x i : ℕ) (hx : 0<x) :
    (orbitValue first x i : R) = (2:R)^i*x + offset first R := by
  have hp : 1 ≤ 2^i*x := Nat.mul_pos (by positivity) hx
  cases first <;> simp [orbitValue, offset, Nat.cast_sub hp, sub_eq_add_neg]

/-- Restart the pinned recurrence at any site. This also identifies the natural
subtraction at the second-kind step for every allowed center. -/
theorem orbit_restart (first : Bool) {x : ℕ} (hx : 2 ≤ x) (i d : ℕ) :
    (if first then firstKindTerm else secondKindTerm) (orbitValue first x i) d =
      orbitValue first x (i+d) := by
  induction d with
  | zero => cases first <;> simp [firstKindTerm, secondKindTerm]
  | succ d ih =>
    have hp : 1 ≤ 2^(i+d)*x := Nat.mul_pos (by positivity) (by omega)
    have he : 2^(i+(d+1))*x=2*(2^(i+d)*x) := by rw [show i+(d+1)=(i+d)+1 by omega, pow_succ]; ring
    cases first <;> simp only [Bool.false_eq_true, if_false, if_true] at ih ⊢
    · rw [secondKindTerm, ih]
      simp only [orbitValue, Bool.false_eq_true, if_false, he]
      omega
    · rw [firstKindTerm, ih]
      simp only [orbitValue, if_true, he]
      omega

/-- A prime larger than the largest power of two in a window can kill at most
one position of an orbit in that window. -/
theorem unique_zero_position (first : Bool) {q x i j D : ℕ} (hq : q.Prime)
    (hbig : 2^D < q) (hx : 0<x) (hi : i≤D) (hj : j≤D)
    (hzi : q ∣ orbitValue first x i) (hzj : q ∣ orbitValue first x j) : i=j := by
  let : Fact q.Prime := ⟨hq⟩
  have h₁ := (ZMod.natCast_eq_zero_iff ..).mpr hzi
  have h₂ := (ZMod.natCast_eq_zero_iff ..).mpr hzj
  rw [cast_orbit first _ _ _ hx] at h₁ h₂
  have hx' : (x : ZMod q) ≠ 0 := by
    intro he
    rw [he, mul_zero, zero_add] at h₁
    cases first <;> simp [offset] at h₁
  have hpow : (2 : ZMod q)^i=(2:ZMod q)^j := by
    apply mul_right_cancel₀ hx'
    linear_combination h₁-h₂
  have hm : 2^i ≡ 2^j [MOD q] := (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using hpow)
  have he := hm.eq_of_lt_of_lt ((Nat.pow_le_pow_right (by decide : 0<2) hi).trans_lt hbig)
    ((Nat.pow_le_pow_right (by decide : 0<2) hj).trans_lt hbig)
  exact pow_right_injective₀ (by decide : 0 < (2:ℕ)) (by decide) he

#print axioms orbit_restart
#print axioms unique_zero_position

theorem affine_orbit (first : Bool) {B : ℕ} (hB : 0 < B) (W n i : ℕ) :
    orbitValue first (W*n+B) i = (2^i*W)*n + orbitValue first B i := by
  have hp : 1 ≤ 2^i*B := Nat.mul_pos (by positivity) hB
  cases first <;> simp only [orbitValue, Bool.false_eq_true, if_false, if_true, mul_add, ← mul_assoc] <;> omega

theorem affine_nondegenerate (first : Bool) {B W i j : ℕ} (hB : 0 < B) (hW : 0 < W) (hne : i ≠ j) :
    (2^i*W)*orbitValue first B j ≠ (2^j*W)*orbitValue first B i := by
  intro h
  have e := congrArg (fun v : ℕ => (v : ℤ)) h
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, cast_orbit first ℤ _ _ hB] at e
  have hpow : (2:ℤ)^i=(2:ℤ)^j := by
    have hw : (W : ℤ) ≠ 0 := by exact_mod_cast hW.ne'
    apply mul_right_cancel₀ hw
    cases first <;> simp only [offset, Bool.false_eq_true, if_false, if_true] at e
    · linear_combination e
    · linear_combination -e
  exact hne (pow_right_injective₀ (by decide : 0<(2:ℤ)) (by decide) hpow)

/-- A single progression of centers forces compositeness at every unselected
index through D. The values at the selected indices remain jointly admissible. -/
theorem composite_mask (first : Bool) (A : Finset ℕ) (D : ℕ) (hA : ∀ i ∈ A, i≤D) :
    ∃ W B : ℕ, 0 < W ∧ 2 ≤ B ∧
      (∀ n j, j ≤ D → j ∉ A → ¬(orbitValue first (W*n+B) j).Prime) ∧
      ∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ i ∈ A, ¬p ∣ orbitValue first (W*n+B) i := by
  classical
  let F := range (D+1) \ A
  let q (j : ℕ) := Nat.nth Nat.Prime (2^D+3+j)
  have hprime (j : ℕ) : (q j).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have hinc : StrictMono q := fun _ _ h => Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)
  have hbig (j : ℕ) : 2^D < q j ∧ 2 < q j := by
    have hl : 2^D+3+j ≤ q j := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le _
    have := Nat.one_le_two_pow (n:=D)
    omega
  have localRoot (j : ℕ) : ∃ r : ℕ, (2 : ZMod (q j))^j*r + offset first _ = 0 := by
    let : Fact (q j).Prime := ⟨hprime j⟩
    have htwo : (2 : ZMod (q j)) ≠ 0 := by
      exact_mod_cast (ZMod.natCast_eq_zero_iff 2 (q j)).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (hbig j).2)
    obtain ⟨r,hr⟩ := ZMod.natCast_zmod_surjective (-offset first (ZMod (q j))/(2:ZMod (q j))^j)
    refine ⟨r,?_⟩
    rw [hr]
    field_simp
    ring
  choose r hr using localRoot
  let b := Nat.chineseRemainderOfFinset r q F (fun j _ => (hprime j).ne_zero)
    (fun i _ j _ hij => (Nat.coprime_primes (hprime i) (hprime j)).mpr (hinc.injective.ne hij))
  let W := ∏ j ∈ F, q j
  let B := b.val+3*W
  have hW : 0 < W := prod_pos fun j _ => (hprime j).pos
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hdiv (j : ℕ) (hj : j ∈ F) : q j ∣ W := dvd_prod_of_mem _ hj
  have hzero (n j : ℕ) (hj : j ∈ F) : q j ∣ orbitValue first (W*n+B) j := by
    have hw := (ZMod.natCast_eq_zero_iff ..).mpr (hdiv j hj)
    have hb := (ZMod.natCast_eq_natCast_iff ..).mpr (b.property j hj)
    apply (ZMod.natCast_eq_zero_iff ..).mp
    rw [cast_orbit first _ _ _ (by omega)]
    dsimp only [B]
    push_cast
    rw [hw,hb]
    simpa using hr j
  refine ⟨W,B,hW,hB,?_,?_⟩
  · intro n j hj hnot hp
    have hmem : j ∈ F := mem_sdiff.mpr ⟨mem_range.mpr (by omega), hnot⟩
    have hqW := Nat.le_of_dvd hW (hdiv j hmem)
    have heq := (Nat.prime_dvd_prime_iff_eq (hprime j) hp).mp (hzero n j hmem)
    have hv : W*n+B ≤ 2^j*(W*n+B) := Nat.le_mul_of_pos_left _ (by positivity)
    dsimp [B] at hv heq
    cases first <;> simp only [orbitValue, Bool.false_eq_true, if_false, if_true] at heq <;> omega
  · intro p hp
    by_cases hd : p ∣ W
    · obtain ⟨j,hj,hpj⟩ := (hp.prime.dvd_finsetProd_iff q).mp hd
      have heq := (Nat.prime_dvd_prime_iff_eq hp (hprime j)).mp hpj
      subst p
      refine ⟨0,?_⟩
      intro i hi hbad
      have ji := unique_zero_position first (hprime j) (hbig j).1 (by omega : 0 < W*0+B)
        (by have := mem_range.mp (mem_sdiff.mp hj).1; omega : j≤D) (hA i hi) (hzero 0 j hj) hbad
      exact (mem_sdiff.mp hj).2 (ji ▸ hi)
    · let : Fact p.Prime := ⟨hp⟩
      have hw := (ZMod.natCast_eq_zero_iff W p).not.mpr hd
      obtain ⟨n,hn⟩ := ZMod.natCast_zmod_surjective (-(B : ZMod p)/(W : ZMod p))
      have hc : ((W*n+B : ℕ) : ZMod p)=0 := by push_cast; rw [hn]; field_simp; ring
      refine ⟨n,?_⟩
      intro i _ hbad
      have hh := (ZMod.natCast_eq_zero_iff ..).mpr hbad
      rw [cast_orbit first _ _ _ (by omega),hc,mul_zero,zero_add] at hh
      cases first <;> simp [offset] at hh

#print axioms affine_nondegenerate
#print axioms composite_mask

end CunninghamChain.PrimeReturns
