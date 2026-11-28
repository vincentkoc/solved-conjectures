import Erdos478GapVariance

/-!
# Divergence of the factorial deficit in prime-weighted density

For every fixed threshold, the primes missing fewer factorial residues have
vanishing relative mass with weights log(p)/p. The proof uses the second
moment over a fixed finite set of distinct prime gap lengths before sending
the reciprocal mass of the set to infinity.
-/

namespace Erdos478.GapDensity
noncomputable section
open Finset Filter Topology MeanDeficit RootMoments GapVariance

def below (D : ℕ) (p : ℕ) : ℝ := if deficit p < D then 1 else 0

theorem below_nonneg (D p : ℕ) : 0 ≤ below D p := by unfold below; split <;> norm_num

private theorem tail_bound (S : Finset Nat.Primes) (D : ℕ) (hD : (D : ℝ) ≤ mass S / 2)
    (hM : 0 < mass S) : ∃ B : ℕ, ∀ p, p.Prime →
      (mass S/2)^2*(if B<p then below D p else 0) ≤ majorSum S p := by
  obtain ⟨B,hB⟩ := centered_bound S
  refine ⟨B,?_⟩
  intro p hp
  have hb := square_le S p hp
  by_cases hlarge : B<p
  · rw [if_pos hlarge]
    by_cases hd : deficit p < D
    · rw [below,if_pos hd,mul_one]
      apply le_trans _ hb
      have hr := hB p hlarge hp
      have hdef : (deficit p : ℝ) < D := by exact_mod_cast hd
      have hneg : mass S/2 ≤ -(∑ i ∈ S, centered i p) := by linarith
      nlinarith [mul_self_le_mul_self (div_nonneg hM.le (by norm_num) : 0 ≤ mass S/2) hneg]
    · rw [below,if_neg hd,mul_zero]
      exact (sq_nonneg _).trans hb
  · rw [if_neg hlarge,mul_zero]
    exact (sq_nonneg _).trans hb

/-- Every averaging operator with the degree-one moment property assigns
vanishing mass to primes below a fixed factorial-deficit threshold. -/
theorem vanishing_for_average (A : PrimeAverage) (D : ℕ) :
    Tendsto (fun X => A.avg X (below D)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun X => lt_of_lt_of_le ha (by
      simpa using A.mono X (a := 0) (b := below D) (fun p _ => below_nonneg D p))
  · intro ε hε
    obtain ⟨S,hS⟩ := unbounded_mass (max (2*(D:ℝ)) (24/ε))
    let M := mass S
    have hD : (D:ℝ) ≤ M/2 := by have := (le_max_left _ _).trans_lt hS; dsimp [M]; linarith
    have hs : 24/ε < M := (le_max_right _ _).trans_lt hS
    have hM : 0<M := (div_pos (by norm_num) hε).trans hs
    have hmε : 12/M < ε/2 := by
      apply (div_lt_iff₀ hM).mpr
      have := (div_lt_iff₀ hε).mp hs
      linarith
    obtain ⟨B,hB⟩ := tail_bound S D hD hM
    let tail := fun p : ℕ => if B<p then below D p else 0
    have he := A.finite_change (a := below D) (b := tail) B (by intro p hp _; simp [tail,hp])
    have hV := (major_limit A S).eventually_lt_const (show 2*mass S < 3*M by change 2*M<3*M; linarith)
    filter_upwards [hV,he.eventually_lt_const (show (0:ℝ)<ε/2 by positivity)] with X hX hE
    have hm := A.mono X (a := (M/2)^2 • tail) (b := majorSum S) (fun p hp => hB p hp)
    rw [map_smul,smul_eq_mul] at hm
    have hb : A.avg X tail < 12/M := by
      apply (lt_div_iff₀ hM).mpr
      apply lt_of_mul_lt_mul_left (a := M)
      · nlinarith [hm.trans_lt hX]
      · exact hM.le
    linarith

/-- The unconditional log(p)/p mass below the threshold is little-o of log X. -/
theorem vanishing_below (D : ℕ) : Tendsto (fun X => mean X (below D)) atTop (𝓝 0) :=
  vanishing_for_average mertensAverage D

/-- The complementary primes carry asymptotically all log(p)/p weight. -/
theorem density_one (D : ℕ) :
    Tendsto (fun X : ℕ =>
      (∑ p ∈ (Nat.primesLE X).filter (fun p => D ≤ deficit p), Real.log p / p) / Real.log X)
      atTop (𝓝 1) := by
  have h := (constant_mean mertensAverage).sub (vanishing_below D)
  change Tendsto (fun X => mean X 1 - mean X (below D)) atTop (𝓝 (1-0)) at h
  rw [sub_zero] at h
  apply h.congr
  intro X
  rw [← map_sub]
  change (∑ p ∈ Nat.primesLE X, (1-below D p)*Real.log p/p)/Real.log X = _
  rw [sum_filter]
  congr 1
  apply sum_congr rfl
  intro p _
  by_cases hd : D ≤ deficit p <;> simp [below,hd,not_lt.mpr,lt_of_not_ge]

#print axioms vanishing_below
#print axioms density_one

end
end Erdos478.GapDensity
