import ThetaGapBiasThree
import ThetaDistinctPrimeQuadruples

/-! Group actual nearby prime pairs by their individual displacement. -/
namespace Arxiv.«2501.03234».ThetaGapFibres
open Filter Finset Real ThetaPairEmpirical ThetaGapBiasThree ThetaLocalPrimeCounts
open ThetaShortPrimeInterval ThetaPairTestTruncation
noncomputable section

def shifts (d H : ℕ) := (Icc 1 H).filter (fun h => h%3=d)
def fibre (X H h : ℕ) := (pairs X H).filter (fun z => z.2-z.1=h)
def value (X H h : ℕ) (g : ℝ×ℝ → ℝ) := ∑ z∈fibre X H h,g (observe z)

private theorem bounds {X H : ℕ} {z : Σ _ : ℕ,ℕ} (hz : z∈pairs X H) :
    X<z.1 ∧ z.1≤X+X ∧ z.1.Prime ∧ z.1<z.2 ∧ z.2≤z.1+H ∧ z.2.Prime := by
  obtain ⟨hp,hl⟩ := mem_sigma.mp hz
  simp only [sample,mem_primes,mem_Ioc,and_true] at hp hl
  exact ⟨hp.1.1,hp.1.2,hp.2,hl.1.1,hl.1.2,hl.2⟩

theorem group (d X H : ℕ) (g : ℝ×ℝ → ℝ) :
    (∑ h∈shifts d H,value X H h g)=total (gap d X H) g := by
  classical
  unfold total gap
  have hm := sum_fiberwise_eq_sum_filter (pairs X H) (shifts d H) (fun z : Σ _ : ℕ,ℕ => z.2-z.1)
    (fun z => g (observe z))
  change _=∑ z∈(pairs X H).filter (fun z => (z.2-z.1)%3=d),g (observe z)
  apply hm.trans
  congr 1
  ext z
  simp only [mem_filter,shifts,mem_Icc]
  by_cases hz : z∈pairs X H
  · have h := bounds hz
    simp only [hz,true_and]
    omega
  · simp [hz]

theorem size {d H : ℕ} : (shifts d H).card≤H := by
  exact (card_le_card (filter_subset ..)).trans (by simp)

theorem inject {X H h : ℕ} (hH : H≤X) :
    (fibre X H h).card≤(ThetaDistinctPrimeQuadruples.pairs (4*X) h).card := by
  apply card_le_card_of_injOn (fun z : Σ _ : ℕ,ℕ => z.1)
  · intro z hz
    obtain ⟨h₁,h₂⟩ := mem_filter.mp hz
    obtain ⟨_,hp,hp',hl,hl',hprime⟩ := bounds h₁
    have he : z.1+h=z.2 := by omega
    change z.1∈ThetaDistinctPrimeQuadruples.pairs (4*X) h
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega,hp'⟩,he ▸ Nat.mem_primesLE.mpr ⟨by omega,hprime⟩⟩
  · rintro ⟨p,l⟩ ha ⟨p',l'⟩ hb he
    obtain ⟨ha₁,ha₂⟩ := mem_filter.mp ha
    obtain ⟨hb₁,hb₂⟩ := mem_filter.mp hb
    have h₁ := (bounds ha₁).2.2.2.1
    have h₂ := (bounds hb₁).2.2.2.1
    simp only at ha₂ hb₂ he h₁ h₂
    congr 1 <;> omega

#print axioms group
#print axioms inject
end
end Arxiv.«2501.03234».ThetaGapFibres
