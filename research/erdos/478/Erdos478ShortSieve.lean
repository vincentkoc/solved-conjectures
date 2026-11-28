import Erdos478SievedIntervals
import Erdos478SchurLocalMass

/-!
# A short interval escaping every excluded prime

There are at most `D` forbidden classes per prime. The length depends on the
number of primes and their local degree bound, independently of their product.
-/

namespace Erdos478.SchurSieve
open Finset

def depth (D L : ℕ) := 2*(D*L)+1
def errorBudget (D L : ℕ) := (2*depth D L+2)*(2^(2*L))^(2*depth D L+1)
def window (D L : ℕ) := 2*(errorBudget D L+2)*2^(D*L)

theorem window_le (D L : ℕ) : window D L ≤ 2^(32*(D+1)*(L+1)^2) := by
  let m := 2*depth D L+1
  have hw : errorBudget D L ≤ 2^(m+1+2*L*m) := by
    change (m+1)*(2^(2*L))^m ≤ _
    rw [pow_add (2:ℕ) (m+1) (2*L*m),pow_mul (2:ℕ) (2*L) m]
    exact Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)
  have hpos : 2 ≤ 2^(m+1+2*L*m) := by
    exact Nat.le_self_pow (by omega) _
  have hsum := Nat.add_le_add hw hpos
  rw [← two_mul,← pow_succ'] at hsum
  dsimp only [window]
  calc
    _ ≤ 2*2^((m+1+2*L*m)+1)*2^(D*L) := by gcongr
    _ = 2^((m+1+2*L*m+1)+1+D*L) := by rw [pow_add (2:ℕ) _ (D*L),pow_succ' (2:ℕ) (m+1+2*L*m+1)]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp [m,depth]
      ring_nf
      omega

/-- A positive simultaneous survivor of all the forbidden residue conditions. -/
theorem positive_survivor (Q : Finset ℕ) (D L : ℕ) (B : (q : ℕ) → Finset (ZMod q))
    (hp : ∀ q ∈ Q, q.Prime) (hQ : ∀ q ∈ Q, D < q) (hν : ∀ q ∈ Q, (B q).card ≤ D)
    (hs : Q.card+1 ≤ 2^L) (hd : D+1 ≤ 2^L) :
    ∃ x, 0 < x ∧ x < window D L ∧ ∀ q ∈ Q, (x : ZMod q) ∉ B q := by
  classical
  let u := density B
  let P := ∏ q ∈ Q, (1-u q)
  let K : ℝ := 2^(D*L)
  let r := depth D L
  let m := 2*r+1
  let N := window D L
  let E := errorBudget D L
  have hU (q) (hq : q ∈ Q) : 0≤u q ∧ u q≤1 := by
    have hh : (B q).card ≤ q := (hν q hq).trans (hQ q hq).le
    dsimp [u,density]
    exact ⟨by positivity,(div_le_one (by exact_mod_cast (hp q hq).pos)).mpr (by exact_mod_cast hh)⟩
  have hP0 : 0<P := prod_pos (fun q hq => sub_pos.mpr ((div_lt_one (by exact_mod_cast (hp q hq).pos :
      (0:ℝ)<q)).mpr (by exact_mod_cast lt_of_le_of_lt (hν q hq) (hQ q hq))))
  have hk : 1 ≤ K*P := by
    apply (local_mass Q D (fun q => (B q).card) hQ hν).trans
    refine mul_le_mul_of_nonneg_right ?_ hP0.le
    dsimp [K]
    rw [Nat.mul_comm D L,pow_mul]
    exact_mod_cast Nat.pow_le_pow_left hs D
  have hscale : (2:ℝ) ≤ 2^m*P^3 := by
    have hb : 2*K^3 ≤ (2:ℝ)^m := by
      dsimp [K,m,r,depth]
      rw [← pow_mul,← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hcube := one_le_pow₀ hk (n := 3)
    calc
      2 ≤ 2*(K*P)^3 := by linarith
      _ ≤ 2^m*P^3 := by rw [mul_pow,← mul_assoc]; gcongr
  have htail : 2*moment Q u m ≤ P := by
    have ht := CunninghamChain.sieve_symmetric_tail_bound Q u m hU
    change ((2:ℝ)^m*moment Q u m)*P^2 ≤ 1 at ht
    apply le_of_mul_le_mul_right (a := (2:ℝ)^m*P^2) _ (by positivity)
    nlinarith only [ht,hscale]
  have he : (∑ j ∈ range (m+1), ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, ((B q).card : ℝ)) ≤ E := by
    exact_mod_cast (truncation_error Q (fun q => (B q).card) D m hν).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show (Q.card+1)*(D+1) ≤ 2^(2*L) by
        rw [two_mul,pow_add]; exact Nat.mul_le_mul hs hd) m))
  have low := finite_lower B N Q hp hU r
  have hN : (N:ℝ) = 2*((E:ℝ)+2)*K := by simp [N,E,K,window]
  have hc : 2 ≤ (survivors B N Q).card := by
    change (N:ℝ)*(P-moment Q u m) - _ ≤ _ at low
    have main := mul_le_mul_of_nonneg_left hk (show 0 ≤ (E:ℝ)+2 by positivity)
    have main' := mul_le_mul_of_nonneg_left htail (show 0 ≤ ((E:ℝ)+2)*K by positivity)
    rw [hN] at low
    exact_mod_cast (by nlinarith only [low,main,main',he] : (2:ℝ) ≤ (survivors B N Q).card)
  obtain ⟨x,hx,hx0⟩ : ∃ x ∈ survivors B N Q, x ≠ 0 := by
    by_contra! hall
    have sub : survivors B N Q ⊆ {0} := fun x h => mem_singleton.mpr (hall x h)
    have := card_le_card sub
    simp at this
    omega
  obtain ⟨hxN,havoid⟩ := mem_filter.mp hx
  exact ⟨x,Nat.pos_of_ne_zero hx0,mem_range.mp hxN,havoid⟩

#print axioms window_le
#print axioms positive_survivor

end Erdos478.SchurSieve
