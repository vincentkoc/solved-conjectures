import ThetaAffineSieveInterval

/-! The Alweiss–Luo short-interval tuple estimate in the class one modulo eight. -/
namespace Arxiv.«2501.03234».ThetaShortAffineTuples
open Finset Real Filter ThetaPrimeClusterTransfer ThetaClassOneClusters ThetaMaynardClusters
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Prime-count consequence of Alweiss–Luo, Theorem 1.1, for the fixed admissible
forms 8n+1+8k!j. Their additional roughness condition can be discarded. -/
def BackwardTuples (m k : ℕ) (A : ℝ) : Prop :=
  ThetaAffineSieveInterval.Count (fun n => m≤((range k).filter (fun j => (form k n j).Prime)).card) k A

/-- Inject the backward sieve bases at scale X/8 into (X,X+H-D] so that the
whole prime cluster is inside the original forward interval. -/
theorem ordinary {m k : ℕ} {A : ℝ} (hA : 0<A) (sieve : BackwardTuples m k A) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, 32*(X:ℝ)^(21/40:ℝ)≤H → H≤X →
    A/32*H/(1+log X)^k≤
      (((Ioc X (X+(H-diameter k))).filter (classCluster m (diameter k))).card:ℝ) := by
  have hm : ∀ᶠ n : ℕ in atTop, m≤((range k).filter (fun j => (form k n j).Prime)).card →
      classCluster m (diameter k) (8*n+0) :=
    Eventually.of_forall (fun n hn => by simpa only [Nat.add_zero] using class_of_forms m k n hn)
  have hs : ThetaAffineSieveInterval.Count
      (fun n => m≤((range k).filter (fun j => (form k n j).Prime)).card) k A := sieve
  have h := ThetaAffineSieveInterval.dilate (P:=fun n => m≤((range k).filter
    (fun j => (form k n j).Prime)).card) (V:=classCluster m (diameter k)) (k:=k)
    (B:=0) (D:=diameter k) (by decide : 8≤8) hA hs hm
  norm_num only [Nat.reduceMul,Nat.cast_ofNat] at h
  exact h

#print axioms ordinary
end
end Arxiv.«2501.03234».ThetaShortAffineTuples
