import Erdos478MertensGapBands
import Erdos478DistinctBandEndpoints

/-!
# A finite bound for a shortfall of distinct factorial endpoints

When every length is at least M, fewer than D distinct endpoints imply
that the omitted-set weight is at least 1−D/M outside a fixed finite set.
Its prime mean is the product of the local factors 1−1/ℓ.
-/

namespace Erdos478.GapBands
open Finset Filter Topology GapSieve GapVariance GapDensity RootMoments
open scoped Classical
noncomputable section

private theorem retain_eq (i : Nat.Primes) (p : ℕ) : retain i p=observation i p/i.val := by
  change (1/(i.val:ℝ))*observation i p=_
  ring

private theorem retain_interval (i : Nat.Primes) {p : ℕ} (hp : p.Prime) :
    0≤retain i p ∧ retain i p≤1 := by
  rw [retain_eq]
  have hi : (0:ℝ) < (i.val:ℝ) := by exact_mod_cast i.property.pos
  exact ⟨div_nonneg (Nat.cast_nonneg _) hi.le,(div_le_one hi).mpr (GapVariance.bound i p hp)⟩

private theorem omitted_lower (s : Finset Nat.Primes) {p : ℕ} (hp : p.Prime) :
    1-(∑ i ∈ s, retain i p)≤∏ i ∈ s, (1-retain i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi,prod_insert hi]
    have h := retain_interval i hp
    have mul := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr h.2)
    have hs := sum_nonneg (fun i (_ : i∈s) => (retain_interval i hp).1)
    nlinarith only [mul,mul_nonneg h.1 hs]

private theorem actual_bound {s : Finset Nat.Primes} {p D M : ℕ} (hp : p.Prime)
    (hM : 0<M) (hs : ∀ i∈s, M ≤ i.val)
    (he : ((joined s p).card:ℝ)=∑ i ∈ s, observation i p) (hf : (joined s p).card<D) :
    1-(D:ℝ)/M ≤ pattern retain ∅ s p := by
  have hsum : (M:ℝ)*(∑ i ∈ s, retain i p)≤∑ i ∈ s, observation i p := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    calc (M:ℝ)*retain i p ≤ (i.val:ℝ)*retain i p :=
           mul_le_mul_of_nonneg_right (by exact_mod_cast hs i hi) (retain_interval i hp).1
         _ = _ := by rw [retain_eq]; field_simp [show (i.val:ℝ)≠0 by exact_mod_cast i.property.ne_zero]
  have hd : ((joined s p).card:ℝ)≤D := by exact_mod_cast hf.le
  have hle : (∑ i ∈ s, retain i p)≤(D:ℝ)/M := by
    apply (le_div_iff₀ (by exact_mod_cast hM : (0:ℝ)<M)).mpr
    rw [mul_comm]
    exact hsum.trans (he ▸ hd)
  have h := (sub_le_sub_left hle 1).trans (omitted_lower s hp)
  simpa [pattern,prod_apply] using h

private theorem ordinary_indicator (X : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ordinary X (fun p => if P p then 1 else 0)=fraction X P := by
  classical
  change (Nat.primeCounting X : ℝ)⁻¹*(∑ p ∈ Nat.primesLE X, if P p then 1 else 0)=_
  rw [fraction,← Nat.primesLE_card_eq_primeCounting,div_eq_inv_mul]
  congr 1
  rw [card_filter]
  push_cast
  rfl

/-- The error can be made arbitrarily small in the prime-counting cutoff
for each fixed family, minimum length and requested number of endpoints. -/
theorem finite_shortfall (pit : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes)
    {M D : ℕ} (hM : 0<M) (hs : ∀ i∈s, M ≤ i.val) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X in atTop, (1-(D:ℝ)/M)*fraction X (fun p => (joined s p).card<D)<euler s+ε := by
  classical
  let A := countingAverage pit
  let w := pattern retain ∅ s
  let ind := fun p => if (joined s p).card<D then (1:ℝ) else 0
  obtain ⟨B,he⟩ := eventual_endpoint_sum s
  let cap := fun p => if B<p then w p else (1:ℝ)
  have hm : Tendsto (fun X => A.avg X w) atTop (𝓝 (euler s)) := by
    simpa [w,euler,pattern] using pattern_mean A ∅ s (by simp)
  have change' := A.finite_change (a:=cap) (b:=w) B (fun p hp _ => if_pos hp)
  have lim := change'.add hm
  simp only [sub_add_cancel,zero_add] at lim
  filter_upwards [lim.eventually_lt_const (by linarith : euler s<euler s+ε)] with X hX
  have bound : ∀ p, p.Prime → ((1-(D:ℝ)/M) • ind) p≤cap p := by
    intro p hp
    simp only [Pi.smul_apply,smul_eq_mul,ind,cap]
    split_ifs with hf hb hb
    · simpa [w] using actual_bound hp hM hs (he p hb hp) hf
    · have : (0:ℝ)≤(D:ℝ)/M := by positivity
      linarith
    · simp only [mul_zero]
      simp only [w,pattern,prod_empty,one_mul,prod_apply,Pi.sub_apply,Pi.one_apply]
      exact prod_nonneg fun i _ => sub_nonneg.mpr (retain_interval i hp).2
    · norm_num
  have h := (A.mono X bound).trans_lt hX
  rw [map_smul,smul_eq_mul] at h
  change (1-(D:ℝ)/M)*ordinary X ind<_ at h
  simpa only [ind,ordinary_indicator] using h

#print axioms finite_shortfall
end
end Erdos478.GapBands
