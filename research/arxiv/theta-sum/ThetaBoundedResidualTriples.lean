import ThetaCentralResidualBudget
import ThetaResilientCentralTriples
import ThetaWeilShortIntervals

/-! Disjoint near-central prime triples with an absolute bound for every residual. -/
namespace Arxiv.«2501.03234».ThetaBoundedResidualTriples
open Real Filter Finset ThetaTernaryErrorBudget ThetaTernaryWindows ThetaTernaryPacking
open ThetaTernaryDeletion ThetaTernaryIncidence ThetaTernaryTransfer ThetaCharacterPrimeMeans
open ThetaAlmostEqualPrimeTriples ThetaFivePrimeMoment ThetaCentralResidualBudget
noncomputable section
open scoped Classical

def outliers (A : Finset ℕ) (B : ℝ) := A.filter (fun p => B≤|residual p|)

theorem tail (A : Finset ℕ) {B : ℝ} (hB : 1≤B) :
    ((outliers A B).card:ℝ)*B≤∑ p∈A,(residual p)^2 := by
  let E := outliers A B
  have h := sum_le_sum (s:=E) (f:=fun _ => B) (g:=fun p => (residual p)^2) (by
    intro p hp
    have hv := (mem_filter.mp hp).2
    change B≤|residual p| at hv
    rw [←sq_abs]
    nlinarith only [hv,mul_nonneg (abs_nonneg (residual p)) (sub_nonneg.mpr (hB.trans hv))])
  simp only [sum_const,nsmul_eq_mul] at h
  exact h.trans (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; positivity))

def Statement (θ b C : ℝ) := ∃ B : ℝ, 0<B ∧ ∀ᶠ n : ℕ in atTop, Odd n →
  ∃ D : Finset Triple, b^2*(n:ℝ)^θ/(108*C*(1+log n))≤D.card ∧ separated D ∧
    ∀ t∈D,t.1+t.2.1+t.2.2=n ∧ t.1≠t.2.1 ∧ t.1≠t.2.2 ∧ t.2.1≠t.2.2 ∧
      ∀ p∈vertices t, p.Prime ∧ |(p:ℝ)-(n:ℝ)/3|≤(n:ℝ)^θ ∧
        |(S p:ℝ)/p-log p/2|<B

theorem diagonal_budget {θ b : ℝ} (ctrl : Control θ) (hb : 0<b) :
    ∀ᶠ n : ℕ in atTop, (0<width n ∧ 0<(n:ℝ)^θ) ∧
      3*((window n θ).card:ℝ)*(width n)^3≤b*((n:ℝ)^θ)^2/4 := by
  filter_upwards [ctrl (show (0:ℝ)<1 by norm_num) (show 0<b/96 by positivity) 3] with n hctl
  let A := window n θ
  let R := (n:ℝ)^θ
  let L := width n
  have hL : 0<L := hctl.1.1
  have hR : 0<R := hctl.1.2
  have hdiag : 3*(A.card:ℝ)*L^3 ≤ b*R^2/4 := by
    have hs : 1≤((errors n θ 1).card:ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) (errors n θ 1).card]
    have hsmall : L^3≤b/96*R :=
      (show L^3≤(((errors n θ 1).card:ℝ)+1)*L^3 by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (pow_pos hL 3).le).trans hctl.2.2
    have hA : (A.card:ℝ)≤8*R := hctl.2.1
    have hp := mul_le_mul hA hsmall (pow_pos hL 3).le (by positivity)
    linarith only [hp]
  exact ⟨hctl.1,hdiag⟩

theorem from_second {θ b C : ℝ} (hb : 0<b) (hC : 0<C)
    (ctrl : Control θ) (hs : Second θ) (ho : Ordinary θ 3 b) (hf : FivePrimeUpper θ C) :
    Statement θ b C := by
  obtain ⟨K,hK,hk⟩ := hs
  let δ := b^2/(144*C)
  let B := 1+K/δ
  have hδ : 0<δ := by dsimp [δ];positivity
  have hB₁ : 1≤B := by dsimp [B];linarith only [div_pos hK hδ]
  have hB : 0<B := zero_lt_one.trans_le hB₁
  have hKB : K≤B*δ := by dsimp [B];field_simp;linarith
  refine ⟨B,hB,?_⟩
  filter_upwards [ho,hf,hk,diagonal_budget ctrl hb]
    with n hn hm hk hctl hodd
  let A := window n θ
  let E := outliers A B
  let R := (n:ℝ)^θ
  let L := width n
  have hR : 0<R := hctl.1.2
  have hL : 0<L := hctl.1.1
  have ht := mul_le_mul_of_nonneg_right (tail A hB₁) hL.le
  have hE' : B*((E.card:ℝ)*L)≤B*(δ*R) := by
    change (E.card:ℝ)*B*L≤_ at ht
    change (∑ p∈A,(residual p)^2)*L≤K*R at hk
    linarith only [ht,hk,mul_le_mul_of_nonneg_right hKB hR.le]
  have hE := (mul_le_mul_iff_right₀ hB).mp hE'
  have hdiag := hctl.2
  obtain ⟨D,hD,hsep,hlo⟩ := ThetaResilientCentralTriples.original A E n hR hL hb hC
    (hn hodd) (hm hodd) (by simpa only [δ,div_mul_eq_mul_div] using hE) hdiag
  refine ⟨D,hlo,hsep,?_⟩
  intro t ht
  obtain ⟨hh,hd⟩ := mem_filter.mp (hD ht)
  obtain ⟨h₁,h₂,h₃,hn'⟩ := mem.mp hh
  refine ⟨hn',hd.1,hd.2.1,hd.2.2,?_⟩
  intro p hp
  have hmem : p∈A\E := by
    simp only [vertices,mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl;exact h₁;exact h₂;exact h₃
  obtain ⟨ha,hnot⟩ := mem_sdiff.mp hmem
  exact ⟨(Nat.mem_primesLE.mp (mem_filter.mp ha).1).2,(mem_filter.mp ha).2,
    lt_of_not_ge (fun hh => hnot (mem_filter.mpr ⟨ha,hh⟩))⟩

theorem original {e : ℕ} (he : 32≤e) (ht : e≤48) (hk : ThetaCalibratedCone.Kernel e)
    {β θ b C : ℝ} (hβ : (e:ℝ)/64<β) (hθ : β<θ) (htop : θ<1)
    (ord : ThetaLocalPrimeCounts.Ordinary β) (hb : 0<b) (hC : 0<C)
    (ho : Ordinary θ 3 b) (hf : FivePrimeUpper θ C) : Statement θ b C :=
  from_second hb hC (of_power (by positivity) (hβ.trans hθ) htop
    (ThetaShortPrimeInterval.exceptional_for he ht hk)) (centered he ht hk hβ hθ htop ord) ho hf

#print axioms from_second
#print axioms original
end
end Arxiv.«2501.03234».ThetaBoundedResidualTriples
