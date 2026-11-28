import Erdos722ArrayTruncation
import Erdos722DerivedAffine

/-!
# Adjacent ingredients from affine pair designs

Write the affine order as `k^e = (k-1)m + 1`. Arrays of orders
`k^e-1` and `k^e` produce designs with group counts `km` and `km+1`.
-/

namespace Erdos722.PairDesign
open Erdos722.Quartet

def Local (k u : ℕ) := Has (· = k) ((k-1)*u+1)

def Adjacent (k s : ℕ) := Local k s ∧ Local k (s+1)

theorem grow {k s t r a : ℕ} (hk : 2 ≤ k) (A : ArrayAt (s+1) t)
    (hs : Adjacent k s) (hr : r ≤ t) (ha : a ≤ 1)
    (ht : Local k (t+a)) (h : Local k (r+a)) : Local k (s*t+r+a) := by
  have C := array_truncate A hr ha (fun _ => hs.1) hs.2 (Has.single ht) (Has.single h)
  have H := inflate_uniform (by omega : 0 < k-1) C.some (by
    intro n hn
    simpa only [Local,show k-1+1=k by omega] using hn)
  simpa only [Local,show k-1+1=k by omega,Fintype.card_fin] using H

private def rep (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | e+1 => k*rep k e+1

private theorem rep_order {k : ℕ} (hk : 1 ≤ k) (e : ℕ) : (k-1)*rep k e+1=k^e := by
  obtain ⟨w,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  induction e with
  | zero => simp [rep]
  | succ e ih =>
    simp only [rep,Nat.add_one_sub_one,pow_succ] at *
    nlinarith only [congrArg (·*(w+1)) ih]

private theorem rep_large {k : ℕ} (hk : 1 ≤ k) (e : ℕ) : e ≤ rep k e := by
  induction e with
  | zero => simp [rep]
  | succ e ih =>
    dsimp [rep]
    have := Nat.mul_le_mul_right (rep k e) hk
    omega

private theorem affine {k : ℕ} (hk : IsPrimePow k) {e : ℕ} (he : 0<e) :
    Has (· = k) (k^e) := by
  obtain ⟨p,a,hp,ha,rfl⟩ := (isPrimePow_nat_iff _).mp hk
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨H,hH⟩ := Cyclotomy.affine_power_design p a e ha he
  exact ⟨Cover.ofDesign hH⟩

private theorem affine_adjacent {k : ℕ} (hpp : IsPrimePow k) (hk : 2 ≤ k) :
    ∃ N, ∀ e ≥ N, Adjacent k (k*rep k e) := by
  obtain ⟨N,arr⟩ := eventual_arrays hk
  refine ⟨N+1,?_⟩
  intro e he
  let m := rep k e
  let t := (k-1)*m
  have ht : t+1=k^e := rep_order (by omega) e
  have hm := rep_large (by omega : 1≤k) e
  have hlow : N ≤ t := by
    have := Nat.mul_le_mul_right m (by omega : 1 ≤ k-1)
    dsimp [t,m] at *
    omega
  have hH := affine hpp (by omega : 0<e)
  rw [← ht] at hH
  have h₀ := array_fill (by omega : 0<k) (arr t hlow) (S:=(· = k)) rfl (a:=1) le_rfl hH
  have h₁ := array_fill (by omega : 0<k) (arr (t+1) (by omega)) (S:=(· = k)) rfl (a:=0) (by decide) hH
  have hpred : k-1+1=k := by omega
  constructor
  · change Has (· = k) ((k-1)*(k*m)+1)
    rw [show (k-1)*(k*m)+1=k*t+1 by unfold t; ring]
    exact h₀
  · change Has (· = k) ((k-1)*(k*m+1)+1)
    rw [show (k-1)*(k*m+1)+1=k*(t+1)+0 by unfold t; nlinarith only [hpred]]
    exact h₁

/-- Successive affine dimensions give adjacent ingredients at both of the
two widths `km` and `k(km+1)`, with `m` arbitrarily large. -/
theorem affine_widths {k : ℕ} (hpp : IsPrimePow k) (hk : 2 ≤ k) (B : ℕ) :
    ∃ m ≥ B, Adjacent k (k*m) ∧ Adjacent k (k*(k*m+1)) := by
  obtain ⟨N,hN⟩ := affine_adjacent hpp hk
  let e := max B N
  exact ⟨rep k e,(le_max_left ..).trans (rep_large (by omega) e),
    hN e (le_max_right ..),hN (e+1) ((le_max_right ..).trans (Nat.le_succ _))⟩

theorem adjacent_heights {k : ℕ} (hpp : IsPrimePow k) (hk : 2 ≤ k) (s B : ℕ) (hs : 0<s) :
    ∃ t ≥ B, Adjacent k t ∧ ArrayAt (s+1) t ∧ ArrayAt (s+1) (t+1) := by
  obtain ⟨N,hN⟩ := eventual_arrays (by omega : 2≤s+1)
  obtain ⟨m,hm,h,_⟩ := affine_widths hpp hk (max B N)
  have hg : m ≤ k*m := by simpa using Nat.mul_le_mul_right m (by omega : 1≤k)
  have hT := hm.trans hg
  exact ⟨_,(le_max_left ..).trans hT,h,hN _ ((le_max_right ..).trans hT),
    hN _ (((le_max_right ..).trans hT).trans (Nat.le_succ _))⟩

#print axioms affine_widths
#print axioms adjacent_heights
end Erdos722.PairDesign
