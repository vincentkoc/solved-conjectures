import ThetaTernaryVertexDeletion

/-! A positive fraction of the primes can be retained in disjoint triples after
removing a sufficiently small fraction of the window's prime supply. -/
namespace Arxiv.«2501.03234».ThetaResilientCentralTriples
open Finset ThetaTernaryDeletion ThetaTernaryPacking ThetaTernaryIncidence
open ThetaFivePrimeMoment ThetaTernaryVertexDeletion

theorem original (A E : Finset ℕ) (n : ℕ) {R L b C : ℝ}
    (hR : 0<R) (hL : 0<L) (hb : 0<b) (hC : 0<C)
    (hcount : b*R^2≤((triples A A A n).card:ℝ)*L^3)
    (hmom : (five A n:ℝ)*L^5≤C*R^3)
    (hE : (E.card:ℝ)*L≤b^2*R/(144*C))
    (hdiag : 3*(A.card:ℝ)*L^3≤b*R^2/4) :
    ∃ D ⊆ distinctTriples (A\E) n,separated D ∧ b^2*R/(108*C*L)≤D.card := by
  let T := distinctTriples (A\E) n
  let J := lost A E n
  have hs : (J.card:ℝ)^2 ≤ (E.card:ℝ)*(9*(five A n:ℝ)) := by exact_mod_cast square A E n
  have hmix := mul_le_mul hE hmom (show 0≤(five A n:ℝ)*L^5 by positivity) (by positivity)
  have hcoef : b^2*R/(144*C)*(C*R^3)=b^2*R^4/144 := by field_simp
  rw [hcoef] at hmix
  have hs' := mul_le_mul_of_nonneg_right hs (show 0≤L^6 by positivity)
  have hloss : (J.card:ℝ)*L^3 ≤ b*R^2/4 := by
    have hh : ((J.card:ℝ)*L^3)^2 ≤ (b*R^2/4)^2 := by linarith only [hmix,hs']
    exact le_of_sq_le_sq hh (by positivity)
  have hsurv : ((triples A A A n).card:ℝ)≤(T.card:ℝ)+J.card+3*A.card := by
    exact_mod_cast survive A E n
  have hlower : b*R^2≤2*(T.card:ℝ)*L^3 := by
    linarith only [hcount,hloss,hdiag,mul_le_mul_of_nonneg_right hsurv (pow_pos hL 3).le]
  have hsub : T⊆triples A A A n := by
    intro t ht
    obtain ⟨ha,hb,hc,hn⟩ := mem.mp (mem_filter.mp ht).1
    exact mem.mpr ⟨(mem_sdiff.mp ha).1,(mem_sdiff.mp hb).1,(mem_sdiff.mp hc).1,hn⟩
  obtain ⟨D,hD,hsep,hf⟩ := extraction A n T hsub
  have h₁ := pow_le_pow_left₀ (mul_nonneg hb.le (sq_nonneg R)) hlower 2
  have hfin : (T.card:ℝ)^2≤3*(D.card:ℝ)*(9*(five A n:ℝ)) := by
    exact_mod_cast hf.trans (Nat.mul_le_mul_left _ (moment_le A n))
  have h₂ := mul_le_mul_of_nonneg_right hfin (show 0≤4*L^6 by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hmom (show 0≤108*(D.card:ℝ)*L by positivity)
  have hh : b^2*R*R^3≤(108*C*L*D.card)*R^3 := by linarith only [h₁,h₂,h₃]
  have hfinal := (mul_le_mul_iff_left₀ (pow_pos hR 3)).mp hh
  refine ⟨D,hD,hsep,(div_le_iff₀ (by positivity)).mpr ?_⟩
  linarith only [hfinal]

#print axioms original
end Arxiv.«2501.03234».ThetaResilientCentralTriples
