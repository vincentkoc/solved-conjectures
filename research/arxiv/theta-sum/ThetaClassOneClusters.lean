import ThetaPrimeClusterTransfer

/-! Transfer the count of ordinary clusters in the class 1 modulo 8 to the original S. -/
namespace Arxiv.«2501.03234».ThetaClassOneClusters
open Finset Filter Real ThetaPrimeClusterTransfer
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Ordinary primes only. This quantified lower bound follows from Theorem 3.4 of
Maynard by dilating a fixed admissible tuple into the class one modulo eight. -/
def Ordinary (m D k : ℕ) (α : ℝ) : Prop :=
  ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, (X:ℝ)^(2/3:ℝ)≤H → H≤X →
    α*H/(1+log X)^k ≤ (((Ioc X (X+H)).filter (classCluster m D)).card:ℝ)

/-- The interval has m primes one modulo eight and every prime in it exceeds
the chosen lower bound for the canonical signed sum. -/
def positive (c : ℝ) (m D n : ℕ) :=
  classCluster m D n ∧ ∀ p∈Icc n (n+D),p.Prime → c*p*log p<(S p:ℝ)

/-- Many bounded clusters survive in every sufficiently long short interval.
Maynard's ordinary-prime input is explicit. -/
theorem original {m D k : ℕ} {α c : ℝ} (hα : 0<α) (hc : c<1/2) (ordinary : Ordinary m D k α) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
      K*(X:ℝ)^(3/4:ℝ)*(1+log X)^(8+k)≤H → D≤H → H+D≤X →
      (α/2)*H/(1+log X)^k≤(((Ioc X (X+H)).filter (positive c m D)).card:ℝ) := by
  obtain ⟨K,hK,htransfer⟩ := transfer (sub_pos.mpr hc) hα m D k
  refine ⟨K+1,by positivity,?_⟩
  filter_upwards [ordinary,htransfer,eventually_ge_atTop 1] with X hbase ht hX
  intro H hsize hD hHX
  have hx : 1≤(X:ℝ) := by exact_mod_cast hX
  have hV : 1≤1+log (X:ℝ) := by linarith only [log_nonneg hx]
  have hW : 0≤(X:ℝ)^(3/4:ℝ) := by positivity
  have hVK := one_le_pow₀ (n:=8+k) hV
  have hsize' : K*(X:ℝ)^(3/4:ℝ)*(1+log X)^(8+k)≤H :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : K≤K+1) hW)
      (by linarith only [hVK])).trans hsize
  have hlen : (X:ℝ)^(2/3:ℝ)≤H := calc
    _ ≤ (X:ℝ)^(3/4:ℝ) := rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ ≤ (K+1)*(X:ℝ)^(3/4:ℝ) := le_mul_of_one_le_left hW (by linarith)
    _ ≤ _ := (le_mul_of_one_le_right (by positivity) hVK).trans hsize
  apply (ht H hD hHX hsize' (hbase H hlen (by omega))).trans
  apply Nat.cast_le.mpr (card_le_card ?_)
  intro n hn
  obtain ⟨hn,hcl,hgood⟩ := mem_filter.mp hn
  apply mem_filter.mpr
  refine ⟨hn,hcl,?_⟩
  intro p hp hpr
  have h := (abs_lt.mp (hgood p hp hpr)).1
  linarith only [h]

#print axioms original
end
end Arxiv.«2501.03234».ThetaClassOneClusters
