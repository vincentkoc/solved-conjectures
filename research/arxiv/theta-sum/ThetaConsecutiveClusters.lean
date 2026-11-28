import ThetaConsecutiveProgression
import ThetaShortPositiveClusters

/-! Bounded runs of consecutive positive theta primes in the class one modulo eight. -/
namespace Arxiv.«2501.03234».ThetaConsecutiveClusters
open Finset Filter Real ThetaPrimeClusterTransfer ThetaWeilShortIntervals ThetaShortPositiveClusters
open ThetaConsecutiveProgression ThetaMaynardClusters ThetaAffineSieveInterval
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def slope (k : ℕ) := 8*period (diameter k)
def cost (k : ℕ) := 4*slope k

/-- Ordinary prime-tuple estimate after restriction to the fixed composite-forcing
progression. The forms are admissible by ThetaConsecutiveProgression.admissible. -/
def Sieve (m k : ℕ) (A : ℝ) := Count (fun n => m≤((range k).filter (fun j =>
    (form k (period (diameter k)*n+shift (diameter k)) j).Prime)).card) k A

def allOne (D n : ℕ) := ∀ p∈Icc n (n+D),p.Prime → p%8=1

private theorem cost_ge (k : ℕ) : 32≤cost k := by
  have h : 1≤period (diameter k) := by rw [period_eq];omega
  dsimp [cost,slope];omega

theorem ordinary {m k : ℕ} {A : ℝ} (hA : 0<A) (sieve : Sieve m k A) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, (cost k:ℝ)*(X:ℝ)^(21/40:ℝ)≤H → H≤X →
    A/(cost k:ℝ)*H/(1+log X)^k≤ (((Ioc X (X+(H-diameter k))).filter
      (fun n => classCluster m (diameter k) n ∧ allOne (diameter k) n)).card:ℝ) := by
  let D := diameter k
  let P := fun n => m≤((range k).filter (fun j => (form k (period D*n+shift D) j).Prime)).card
  let V := fun n => classCluster m D n ∧ allOne D n
  have hL : 8 ≤ slope k := by have := cost_ge k;dsimp [cost] at this;omega
  have maps : ∀ᶠ n : ℕ in atTop, P n → V (slope k*n+8*shift D) := by
    filter_upwards [eventually_ge_atTop (2+factor D D)] with n hn hp
    have hb : slope k*n+8*shift D=base D n := by dsimp [slope,base,D];ring
    rw [hb]
    refine ⟨class_of_forms m k _ hp,?_⟩
    intro p h hp
    exact covers D n hn hp (mem_Icc.mp h).1 (mem_Icc.mp h).2
  filter_upwards [dilate (P:=P) (V:=V) (D:=D) hL hA sieve maps] with X hX
  intro H hlen htop
  apply (hX H hlen htop).trans
  apply Nat.cast_le.mpr (card_le_card ?_)
  intro n hn
  simp only [mem_filter] at hn ⊢
  exact hn

/-- These disjoint intervals each contain at least m ordinary consecutive primes;
every prime there is one modulo eight and is close to the signed theta main term. -/
theorem original (weil : Weil) {m k : ℕ} {A ε : ℝ} (hA : 0<A) (he : 0<ε)
    (sieve : Sieve m k A) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, (cost k:ℝ)*(X:ℝ)^(21/40:ℝ)≤H → H≤X →
    ∃ G : Finset ℕ, A/(2*(cost k:ℝ))*H/(1+log X)^k≤((diameter k+1:ℕ):ℝ)*G.card ∧
      (∀ n∈G, X<n ∧ n+diameter k≤X+H ∧ goodCluster ε m (diameter k) n ∧ allOne (diameter k) n) ∧
      ∀ i∈G, ∀ j∈G, i<j → i+diameter k<j := by
  let D := diameter k
  let L := (cost k:ℝ)
  have hL : 1≤L := by dsimp only [L];exact_mod_cast (show 1≤cost k by have := cost_ge k;omega)
  have hL₀ : 0<L := by linarith
  let δ := A/(2*L)
  have hδ : 0<δ := by dsimp [δ];positivity
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<21/40)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ordinary hA sieve,loss weil he hδ D k,ht.eventually_ge_atTop (D:ℝ)] with X hs hl hW
  intro H hlen htop
  have hwidth : (X:ℝ)^(21/40:ℝ)≤H := (le_mul_of_one_le_left (rpow_nonneg (Nat.cast_nonneg X) _) hL).trans hlen
  have hD : D≤H := by exact_mod_cast hW.trans hwidth
  let C := (Ioc X (X+(H-D))).filter (fun n => goodCluster ε m D n ∧ allOne D n)
  have h₁ := hs H hlen htop
  have h₂ := hl H hD hwidth htop
  have h₃ := (Nat.cast_le (α:=ℝ)).mpr (lost_where ε m D X (H-D) (allOne D))
  rw [Nat.cast_add] at h₃
  have heq : A/L*(H:ℝ)/(1+log X)^k=2*(δ*H/(1+log X)^k) := by dsimp [δ];ring
  rw [show A/(cost k:ℝ)*(H:ℝ)/(1+log X)^k=2*(δ*H/(1+log X)^k) from heq] at h₁
  have hc : δ*H/(1+log X)^k≤(C.card:ℝ) := by
    dsimp [C,D] at h₁ h₂ h₃ ⊢
    linarith only [h₁,h₂,h₃]
  obtain ⟨G,hsub,hpack,hsep⟩ := pack C D
  refine ⟨G,hc.trans (by exact_mod_cast hpack),?_,hsep⟩
  intro n hn
  obtain ⟨hn,hg,hr⟩ := mem_filter.mp (hsub hn)
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hn
  exact ⟨hlo,by change n+D≤X+H;omega,hg,hr⟩

#print axioms ordinary
#print axioms original
end
end Arxiv.«2501.03234».ThetaConsecutiveClusters
