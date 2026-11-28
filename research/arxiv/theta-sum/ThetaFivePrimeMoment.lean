import ThetaDisjointCentralPrimeTriples

/-! Express the incidence input using a five-prime correlation in three variables. -/
namespace Arxiv.«2501.03234».ThetaFivePrimeMoment
open Finset Filter Real ThetaTernaryWindows ThetaTernaryErrorBudget
open ThetaTernaryDeletion ThetaTernaryPacking ThetaTernaryTransfer ThetaTernaryIncidence
open ThetaAlmostEqualPrimeTriples ThetaDisjointCentralPrimeTriples
noncomputable section

def completions (A : Finset ℕ) (n p : ℕ) :=
  A.filter (fun q => p+q≤n ∧ n-p-q∈A)

/-- Counts (p,q,r) with p,q,n-p-q,r,n-p-r all in A. -/
def five (A : Finset ℕ) (n : ℕ) := ∑ p∈A,(completions A n p).card^2

private theorem fibre (A : Finset ℕ) (n v : ℕ) :
    (incident (triples A A A n) v).card ≤ 3*(completions A n v).card := by
  let T := triples A A A n
  let F := T.filter (fun t => t.1=v)
  let G := T.filter (fun t => t.2.1=v)
  let H := T.filter (fun t => t.2.2=v)
  have hsub : incident T v ⊆ (F∪G)∪H := by
    intro t ht
    obtain ⟨ht,hv⟩ := mem_filter.mp ht
    simp only [vertices,mem_insert,mem_singleton] at hv
    simp only [F,G,H,mem_union,mem_filter,ht,true_and]
    tauto
  have hf : F.card≤(completions A n v).card := by
    apply card_le_card_of_injOn (fun t : Triple => t.2.1)
    · rintro ⟨a,b,c⟩ ht
      obtain ⟨ht,ha⟩ := mem_filter.mp ht
      obtain ⟨_,hb,hc,hs⟩ := mem.mp ht
      change a=v at ha
      change a+b+c=n at hs
      change b∈completions A n v
      apply mem_filter.mpr
      refine ⟨hb,by omega,?_⟩
      rw [show n-v-b=c by omega]
      exact hc
    · rintro ⟨a,b,c⟩ hx ⟨d,e,f⟩ hy he
      obtain ⟨hx,ha⟩ := mem_filter.mp hx
      obtain ⟨hy,hd⟩ := mem_filter.mp hy
      have h₁ := (mem.mp hx).2.2.2
      have h₂ := (mem.mp hy).2.2.2
      change a+b+c=n at h₁
      change d+e+f=n at h₂
      change a=v at ha;change d=v at hd;change b=e at he
      have h : a=d := by omega
      have h' : c=f := by omega
      simp [h,he,h']
  have hg : G.card≤F.card := by
    apply card_le_card_of_injOn (fun t : Triple => (t.2.1,t.1,t.2.2))
    · rintro ⟨a,b,c⟩ ht
      obtain ⟨ht,hv⟩ := mem_filter.mp ht
      obtain ⟨ha,hb,hc,hn⟩ := mem.mp ht
      exact mem_filter.mpr ⟨mem.mpr ⟨hb,ha,hc,by simpa [add_comm b a] using hn⟩,hv⟩
    · rintro ⟨a,b,c⟩ _ ⟨d,e,f⟩ _ he
      simpa [Prod.ext_iff,and_comm,and_left_comm,and_assoc] using he
  have hh : H.card≤F.card := by
    apply card_le_card_of_injOn (fun t : Triple => (t.2.2,t.2.1,t.1))
    · rintro ⟨a,b,c⟩ ht
      obtain ⟨ht,hv⟩ := mem_filter.mp ht
      obtain ⟨ha,hb,hc,hn⟩ := mem.mp ht
      exact mem_filter.mpr ⟨mem.mpr ⟨hc,hb,ha,by simpa [add_comm,add_left_comm,add_assoc] using hn⟩,hv⟩
    · rintro ⟨a,b,c⟩ _ ⟨d,e,f⟩ _ he
      simpa [Prod.ext_iff,and_comm,and_left_comm,and_assoc] using he
  have h₁ := (card_le_card hsub).trans (card_union_le _ _)
  have h₂ := card_union_le F G
  change (incident T v).card≤_
  omega

theorem moment_le (A : Finset ℕ) (n : ℕ) : moment A n ≤ 9*five A n := by
  unfold moment five
  rw [mul_sum]
  apply sum_le_sum
  intro v _
  calc _ ≤ (3*(completions A n v).card)^2 := Nat.pow_le_pow_left (fibre A n v) _
       _ = _ := by ring

/-- This ordinary upper bound involves five prime forms with gradients
(1,0,0), (0,1,0), (-1,-1,0), (0,0,1), (-1,0,-1). -/
def FivePrimeUpper (θ C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,Odd n → (five (window n θ) n:ℝ)*(width n)^5 ≤ C*((n:ℝ)^θ)^3

theorem lift {θ C : ℝ} (h : FivePrimeUpper θ C) : OrdinaryMoment θ (9*C) := by
  filter_upwards [h,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop 1] with n hn hn₁ hodd
  have hw : 0≤width n := by unfold width;linarith only [log_nonneg hn₁]
  have hh : (moment (window n θ) n:ℝ)≤9*(five (window n θ) n:ℝ) := by
    exact_mod_cast moment_le (window n θ) n
  have h₁ := mul_le_mul_of_nonneg_right hh (pow_nonneg hw 5)
  linarith only [h₁,hn hodd]

#print axioms moment_le
#print axioms lift
end
end Arxiv.«2501.03234».ThetaFivePrimeMoment
