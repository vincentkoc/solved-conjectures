import ThetaTernaryIncidence

/-! Optimal-order packing from two ordinary short-interval prime estimates. -/
namespace Arxiv.«2501.03234».ThetaDisjointCentralPrimeTriples
open Finset Real Filter ThetaTernaryWindows ThetaTernaryErrorBudget
open ThetaTernaryDeletion ThetaTernaryTransfer ThetaTernaryIncidence
open ThetaAlmostEqualPrimeTriples
noncomputable section

/-- Ordinary second moment of the number of representation incidences at a prime. -/
def OrdinaryMoment (θ B : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,Odd n →
    (moment (window n θ) n:ℝ)*(width n)^5 ≤ B*((n:ℝ)^θ)^3

/-- For every large odd target, a family of at least a constant times
n^θ/(1+log n) disjoint, almost equal, theta-accurate prime representations. -/
theorem original {θ ε b B : ℝ} (control : Control θ) (hε : 0<ε)
    (hb : 0<b) (hB : 0<B) (ho : Ordinary θ 3 b) (hmom : OrdinaryMoment θ B) :
    ∀ᶠ n : ℕ in atTop, Odd n →
      ∃ D ⊆ distinctTriples (selected n θ ε) n,separated D ∧
        b^2*(n:ℝ)^θ/(12*B*width n) ≤ D.card := by
  filter_upwards [ho,hmom,retain control hε (show 0<(1/2:ℝ) by norm_num) hb ho,
    control hε hb 3] with n hcount hm hretain hs hodd
  let A := window n θ
  let T := distinctTriples (selected n θ ε) n
  let R := (n:ℝ)^θ
  let L := width n
  have hL : 0<L := hs.1.1
  have hR : 0<R := hs.1.2
  have hsub : T⊆triples A A A n := by
    intro t ht
    obtain ⟨h₁,h₂,h₃,h₄⟩ := mem.mp (mem_filter.mp ht).1
    exact mem.mpr ⟨(mem_sdiff.mp h₁).1,(mem_sdiff.mp h₂).1,(mem_sdiff.mp h₃).1,h₄⟩
  obtain ⟨D,hD,hd,hfin⟩ := extraction A n T hsub
  refine ⟨D,hD,hd,?_⟩
  have hlow : b*R^2 ≤ 2*(T.card:ℝ)*L^3 := by
    have h := mul_le_mul_of_nonneg_right (hretain hodd) (pow_pos hL 3).le
    linarith only [h,hcount hodd]
  have h₁ := pow_le_pow_left₀ (mul_nonneg hb.le (sq_nonneg R)) hlow 2
  have hc : (T.card:ℝ)^2 ≤ 3*(D.card:ℝ)*moment A n := by exact_mod_cast hfin
  have h₂ := mul_le_mul_of_nonneg_right hc (show 0≤4*L^6 by positivity)
  have hm' : (moment A n:ℝ)*L^5≤B*R^3 := hm hodd
  have h₃ := mul_le_mul_of_nonneg_left hm' (show 0≤12*(D.card:ℝ)*L by positivity)
  have hh : b^2*R*R^3≤(12*B*L*D.card)*R^3 := by linarith only [h₁,h₂,h₃]
  have hfinal := (mul_le_mul_iff_left₀ (pow_pos hR 3)).mp hh
  apply (div_le_iff₀ (by change 0<12*B*L;positivity)).mpr
  linarith only [hfinal]

#print axioms original
end
end Arxiv.«2501.03234».ThetaDisjointCentralPrimeTriples
