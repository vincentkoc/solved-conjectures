import ThetaClassPairLaws

/-! An ordinary interval sieve bounds both degrees of the directed prime-pair
graph. Each nonnegative one-prime test controls either corresponding marginal. -/
namespace Arxiv.«2501.03234».ThetaPairMarginals
open Finset Real Filter ThetaPairEmpirical ThetaLocalPrimeCounts ThetaClassPairLaws
open ThetaPrimeStartDensity ThetaPrimeIntervalSieve ThetaAlmostPeriodicWindows ThetaShortClassMeans
open ThetaShortPrimeInterval ThetaLocalIntervalTests
open scoped Topology
noncomputable section

def box (X : ℕ) := Nat.primesLE (4*X)
def incoming (X H l : ℕ) := (sample X X).filter (fun p => l∈sample p H)

private theorem mem {n H p : ℕ} : p∈sample n H ↔ n<p ∧ p≤n+H ∧ p.Prime := by
  simp only [sample,mem_primes,mem_Ioc,and_true,and_assoc]

theorem outer_sub (X : ℕ) : sample X X ⊆ box X := by
  intro p hp
  obtain ⟨_,h₁,h₂⟩ := mem.mp hp
  exact Nat.mem_primesLE.mpr ⟨by omega,h₂⟩

theorem inner_sub {X H p : ℕ} (hH : H≤X) (hp : p∈sample X X) : sample p H ⊆ box X := by
  intro l hl
  obtain ⟨_,hp',_⟩ := mem.mp hp
  obtain ⟨_,hl',hlp⟩ := mem.mp hl
  exact Nat.mem_primesLE.mpr ⟨by omega,hlp⟩

theorem incoming_sub (X H l : ℕ) : incoming X H l ⊆ marks (max X (l-H)) H := by
  intro p hp
  obtain ⟨h₁,h₂⟩ := mem_filter.mp hp
  obtain ⟨hx,_,hp'⟩ := mem.mp h₁
  obtain ⟨hl,hh,_⟩ := mem.mp h₂
  simp only [marks,mem_filter,mem_Ico]
  exact ⟨⟨by omega,by omega⟩,hp'⟩

theorem reverse_sum {X H : ℕ} (hH : H≤X) (f : ℕ → ℝ) :
    (∑ z∈pairs X H,f z.2)=∑ l∈box X,((incoming X H l).card:ℝ)*f l := by
  rw [pairs,sum_sigma]
  calc
    _ = ∑ p∈sample X X,∑ l∈box X,if l∈sample p H then f l else 0 := by
      apply sum_congr rfl;intro p hp
      rw [←sum_filter]
      congr 1
      ext l
      simp only [mem_filter]
      exact ⟨fun hl => ⟨inner_sub hH hp hl,hl⟩,And.right⟩
    _ = _ := by
      rw [sum_comm];apply sum_congr rfl;intro l _
      rw [←sum_filter,sum_const,nsmul_eq_mul];rfl

theorem degrees {θ : ℝ} (hθ : 0<θ) : ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,
    ∀ H : ℕ,Admits θ X H → ∀ f : ℕ → ℝ,(∀ p,0≤f p) →
    ((∑ z∈pairs X H,f z.1)*log X≤(C*H)*(∑ p∈box X,f p)) ∧
    ((∑ z∈pairs X H,f z.2)*log X≤(C*H)*(∑ p∈box X,f p)) := by
  obtain ⟨C,hC,hh⟩ := sieve hθ
  refine ⟨C,hC,?_⟩
  filter_upwards [hh,eventually_ge_atTop (1:ℕ)] with X hs hx
  intro H hH f hf
  have hl : 0≤log X := log_nonneg (Nat.one_le_cast.mpr hx)
  constructor
  · rw [pairs,sum_sigma,sum_mul]
    apply le_trans (sum_le_sum (g:=fun p => C*H*f p) ?_) ?_
    · intro p hp
      have h := hs H (p+1) (by have := (mem.mp hp).1;have := hH.2.1;omega) hH.2.2
      rw [←ThetaPairComparison.shift_marks] at h
      simp only [sum_const,nsmul_eq_mul]
      nlinarith only [mul_le_mul_of_nonneg_right h (hf p)]
    · rw [←mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (outer_sub X) (fun p _ _ => hf p)) (by positivity)
  · rw [reverse_sum hH.2.1,sum_mul,mul_sum]
    apply sum_le_sum
    intro l _
    have h := hs H (max X (l-H)) (le_trans hH.2.1 (le_max_left ..)) hH.2.2
    have hsub : ((incoming X H l).card:ℝ)≤((marks (max X (l-H)) H).card:ℝ) := by
      exact_mod_cast card_le_card (incoming_sub X H l)
    nlinarith only [mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hsub hl).trans h) (hf l)]

#print axioms degrees
end
end Arxiv.«2501.03234».ThetaPairMarginals
