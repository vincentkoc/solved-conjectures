import ThetaShortAffineTuples

/-! Positive bounded prime clusters at the Alweiss–Luo exponent 21/40. -/
namespace Arxiv.«2501.03234».ThetaShortPositiveClusters
open Finset Real Filter ThetaPrimeClusterTransfer ThetaShortAffineTuples ThetaMaynardClusters
open ThetaWeilShortIntervals ThetaShortPrimeInterval ThetaStrongOriginalTail ThetaStrongDeviation
open ThetaCalibratedCone
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- At the ordinary-prime sieve scale, removing every pattern that meets a theta
exception costs an arbitrarily small multiple of H/(1+log X)^k. -/
theorem loss (weil : Weil) {ε η : ℝ} (he : 0<ε) (hη : 0<η) (D k : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, D≤H → (X:ℝ)^(21/40:ℝ)≤H → H≤X →
    ((contaminated ε X (H-D) D).card:ℝ)≤η*H/(1+log X)^k := by
  let d := ((D+1:ℕ):ℝ)
  have hd : 0<d := by dsimp [d];positivity
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [original_of_bound (square_root weil) he,absorb_log_power (div_pos hd hη)
    (by norm_num : (0:ℝ)<2048) k,hl.eventually_ge_atTop 1,eventually_ge_atTop 1] with X hcnt ha hL hX
  intro H hD hsize htop
  change 1≤log (X:ℝ) at hL
  have hx : 1≤(X:ℝ) := by exact_mod_cast hX
  have hp : 0<(X:ℝ) := by linarith
  have hr : exp (rate X/512)≤(X:ℝ)^(1/512:ℝ) := by
    rw [rpow_def_of_pos hp];apply exp_le_exp.mpr;linarith only [rate_le hL]
  have hwidth : (X:ℝ)^(1/2:ℝ)*exp (rate X/512)≤H := by
    apply (mul_le_mul_of_nonneg_left hr (by positivity)).trans
    rw [←rpow_add hp]
    exact (rpow_le_rpow_of_exponent_le hx (by norm_num : (1/2:ℝ)+1/512≤21/40)).trans hsize
  let V := 1+log (X:ℝ)
  let F := exp (rate X/2048)
  have hV : 0<V := by dsimp [V];linarith
  have hF : 0<F := exp_pos _
  have h₁ := Nat.cast_le (α:=ℝ) |>.mpr (count ε X (H-D) D)
  rw [Nat.sub_add_cancel hD,Nat.cast_mul] at h₁
  have hb := h₁.trans (mul_le_mul_of_nonneg_left (hcnt H hwidth htop) hd.le)
  rw [show -rate X/2048 = -(rate X/2048) by ring,exp_neg] at hb
  have hcoef : d*F⁻¹ ≤ η/V^k := by
    apply (le_div_iff₀ (pow_pos hV k)).mpr
    rw [←div_eq_mul_inv,div_mul_eq_mul_div,div_le_iff₀ hF]
    change (d/η)*V^k≤F at ha
    rw [div_mul_eq_mul_div,div_le_iff₀ hη] at ha
    linarith only [ha]
  apply hb.trans
  have hH := div_le_self (Nat.cast_nonneg (α:=ℝ) H) hL
  calc
    d*((H:ℝ)/log X*F⁻¹) ≤ d*(H*F⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hH (inv_nonneg.mpr hF.le)) hd.le
    _ = d*F⁻¹*H := by ring
    _ ≤ η/V^k*H := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    _ = _ := by dsimp [V];ring

/-- Every prime between the cluster endpoints satisfies the original two-sided
theta estimate. At least m of them lie in the class one modulo eight. -/
theorem original (weil : Weil) {m k : ℕ} {ε A : ℝ} (he : 0<ε) (hA : 0<A)
    (sieve : BackwardTuples m k A) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, 32*(X:ℝ)^(21/40:ℝ)≤H → H≤X →
    A/64*H/(1+log X)^k≤
      (((Ioc X (X+(H-diameter k))).filter (goodCluster ε m (diameter k))).card:ℝ) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<21/40)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ordinary hA sieve,loss weil he (by positivity : 0<A/64) (diameter k) k,
    ht.eventually_ge_atTop (diameter k:ℝ)] with X hord hbad hw
  intro H hlen hX
  change (diameter k:ℝ)≤(X:ℝ)^(21/40:ℝ) at hw
  have hpow := rpow_nonneg (Nat.cast_nonneg (α:=ℝ) X) (21/40:ℝ)
  have hmin : (X:ℝ)^(21/40:ℝ)≤H := by linarith only [hlen,hpow]
  have hD : diameter k≤H := by exact_mod_cast hw.trans hmin
  have hb := hbad H hD hmin hX
  have hcount := (Nat.cast_le (α:=ℝ)).mpr (lost ε m (diameter k) X (H-diameter k))
  rw [Nat.cast_add] at hcount
  have hmain := hord H hlen hX
  have hdouble : A/32*(H:ℝ)/(1+log X)^k=2*(A/64*H/(1+log X)^k) := by ring
  rw [hdouble] at hmain
  linarith only [hmain,hcount,hb]

/-- A single residue class of bases packs disjoint closed intervals of width D. -/
theorem pack (B : Finset ℕ) (D : ℕ) : ∃ G⊆B, B.card≤(D+1)*G.card ∧
    ∀ i∈G, ∀ j∈G, i<j → i+D<j := by
  let bins := range (D+1)
  let cells (r : ℕ) := B.filter (fun n => n%(D+1)=r)
  obtain ⟨r,hr,hmax⟩ := bins.exists_max_image (fun a => (cells a).card)
    (show bins.Nonempty by exact ⟨0,mem_range.mpr (Nat.succ_pos _)⟩)
  refine ⟨cells r,filter_subset _ _,?_,?_⟩
  · have hsum : B.card = ∑ a∈bins,(cells a).card := card_eq_sum_card_fiberwise
      (fun n _ => mem_range.mpr (Nat.mod_lt n (Nat.succ_pos D)))
    rw [hsum]
    exact (sum_le_sum hmax).trans_eq (by simp [bins])
  · intro i hi j hj hij
    have hmod : i ≡ j [MOD D+1] := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
    have h := Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hmod.dvd'
    omega

/-- Distinct bounded intervals, all inside the specified window; each contains
m primes one modulo eight and every intervening prime obeys the theta estimate. -/
theorem disjoint_clusters (weil : Weil) {m k : ℕ} {ε A : ℝ} (he : 0<ε) (hA : 0<A)
    (sieve : BackwardTuples m k A) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, 32*(X:ℝ)^(21/40:ℝ)≤H → H≤X →
    ∃ G : Finset ℕ, A/64*H/(1+log X)^k≤((diameter k+1:ℕ):ℝ)*G.card ∧
    (∀ n∈G, X<n ∧ n+diameter k≤X+H ∧ goodCluster ε m (diameter k) n) ∧
      ∀ i∈G, ∀ j∈G, i<j → i+diameter k<j := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<21/40)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [original weil he hA sieve,ht.eventually_ge_atTop (diameter k:ℝ)] with X hB hw
  intro H hlen htop
  change (diameter k:ℝ)≤(X:ℝ)^(21/40:ℝ) at hw
  have hD : diameter k≤H := by
    exact_mod_cast (by linarith only [hw,hlen,rpow_nonneg (Nat.cast_nonneg (α:=ℝ) X) (21/40:ℝ)] :
      (diameter k:ℝ)≤H)
  let B := (Ioc X (X+(H-diameter k))).filter (goodCluster ε m (diameter k))
  obtain ⟨G,hsub,hcard,hsep⟩ := pack B (diameter k)
  refine ⟨G,(hB H hlen htop).trans (by exact_mod_cast hcard),?_,hsep⟩
  intro n hn
  obtain ⟨hn,hgood⟩ := mem_filter.mp (hsub hn)
  obtain ⟨hl,hu⟩ := mem_Ioc.mp hn
  exact ⟨hl,by omega,hgood⟩

#print axioms pack
#print axioms disjoint_clusters
#print axioms loss
#print axioms original
end
end Arxiv.«2501.03234».ThetaShortPositiveClusters
