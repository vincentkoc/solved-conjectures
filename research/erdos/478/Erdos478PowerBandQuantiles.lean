import Erdos478WeightedBandSieve

/-!
# Power-sized deficits witnessed inside a prescribed band of prime gaps

For fixed exponents 0<a<b and every sufficiently large t, all but a
proportion at most a/b (up to an arbitrary error) of primes have at least
t^a distinct repeated upper endpoints using prime gaps in (t^a,t^b].
The cutoff in the prime count may depend on t.
-/

namespace Erdos478.GapBands
open Finset Filter Topology GapSieve GapVariance GapDensity
open scoped Classical
noncomputable section

/-- Distinct repeated endpoints in the specified band, together with the
deficit in the exact factorial image occurring in Erdős 478. -/
def witnessed (lo hi D p : ℕ) : Prop := D≤(joined (band lo hi) p).card ∧
  ((Ico 1 p).image (fun j => j.factorial%p)).card+D≤p-1

private theorem frac_le_one (X : ℕ) (P : ℕ → Prop) : fraction X P≤1 := by
  classical
  by_cases h : (Nat.primesLE X).card=0
  · simp [fraction,h]
  · rw [fraction,div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)]
    exact_mod_cast card_filter_le ..

private theorem comp_frac {X : ℕ} (hX : 2≤X) (s : Finset Nat.Primes) (D : ℕ)
    (lo hi : ℕ) (hs : s=band lo hi) :
    fraction X (fun p => (joined s p).card<D)+fraction X (witnessed lo hi D)=1 := by
  classical
  subst s
  have eq : witnessed lo hi D=fun p => ¬ (joined (band lo hi) p).card<D := by
    funext p
    apply propext
    rw [not_lt]
    exact ⟨And.left,fun h => ⟨h,(Nat.add_le_add_left h _).trans (joined_deficit _ _)⟩⟩
  have hp : 0<(Nat.primesLE X).card := card_pos.mpr ⟨2,Nat.mem_primesLE.mpr ⟨hX,Nat.prime_two⟩⟩
  rw [eq,fraction,fraction,← add_div,← Nat.cast_add,card_filter_add_card_filter_not,
    div_self (by exact_mod_cast hp.ne')]

private theorem frac_mono (X : ℕ) {P Q : ℕ → Prop} (h : ∀ p, P p → Q p) :
    fraction X P≤fraction X Q := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have sub : (Nat.primesLE X).filter P⊆(Nat.primesLE X).filter Q := by
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1,h p (mem_filter.mp hp).2⟩
  exact_mod_cast card_le_card sub

theorem finite_band_bound (pit : DegreeOnePrimeIdealTheorem) {M K D : ℕ} (hM : 0<M)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X in atTop, fraction X (fun p => (joined (band M K) p).card<D) <
      euler (band M K)+(D:ℝ)/M+ε := by
  classical
  have hs : ∀ i∈band M K, M ≤ i.val := by
    intro i hi
    exact (lt_of_not_ge (fun h => (mem_sdiff.mp hi).2 (mem_through.mpr h))).le
  filter_upwards [finite_shortfall pit _ hM hs (D:=D) hε] with X hx
  have hu := frac_le_one X (fun p => (joined (band M K) p).card<D)
  nlinarith only [hx,mul_le_mul_of_nonneg_left hu (show 0≤(D:ℝ)/M by positivity)]

/-- Transfer a limiting band product to endpoint counts at every positive
integral scale D, for arbitrary upper cutoffs K. -/
theorem frequency_of_band_limits (pit : DegreeOnePrimeIdealTheorem) (D K : ℕ → ℕ)
    (hpos : ∀ᶠ t in atTop, 0<D t) {μ : ℝ}
    (hlim : ∀ C : ℕ, 0<C → Tendsto (fun t => euler (band (C*D t) (K t))) atTop (𝓝 μ))
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ t : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      1-μ-ε < fraction X (witnessed (D t) (K t) (D t)) := by
  classical
  obtain ⟨C,hC⟩ := exists_nat_gt (3/ε)
  have hC' : (0:ℝ)<C := lt_trans (by positivity) hC
  have hCN : 0<C := by exact_mod_cast hC'
  have small : 1/(C:ℝ)<ε/3 := by
    have h := (div_lt_iff₀ hε).mp hC
    apply (div_lt_iff₀ hC').mpr
    nlinarith only [h]
  have e := (hlim C hCN).eventually_lt_const (show μ<μ+ε/3 by linarith)
  filter_upwards [e,hpos] with t he ht'
  have hlow : D t≤C*D t := by simpa using Nat.mul_le_mul_right (D t) hCN
  let s := band (D t) (K t)
  let u := band (C*D t) (K t)
  have sub : u⊆s := by
    intro i hi
    obtain ⟨hi,hj⟩ := mem_sdiff.mp hi
    exact mem_sdiff.mpr ⟨hi,fun h => hj (mem_through.mpr ((mem_through.mp h).trans hlow))⟩
  have frac (X : ℕ) : fraction X (fun p => (joined s p).card<D t)≤
      fraction X (fun p => (joined u p).card<D t) := by
    apply frac_mono
    intro p h
    have hsub : joined u p⊆joined s p := biUnion_subset_biUnion_of_subset_left _ sub
    exact lt_of_le_of_lt (card_le_card hsub) h
  have ratio : (D t:ℕ)/(C*D t:ℕ)=(1:ℝ)/C := by
    push_cast
    field_simp [show (D t:ℝ)≠0 by exact_mod_cast ht'.ne']
  filter_upwards [finite_band_bound pit (K:=K t) (D:=D t) (Nat.mul_pos hCN ht')
    (show 0<ε/3 by linarith),eventually_ge_atTop 2] with X hx hX
  rw [ratio] at hx
  have co := comp_frac hX s (D t) _ _ rfl
  change fraction X (fun p => (joined u p).card<D t)<_ at hx
  linarith only [he,small,frac X,hx,co]

/-- Uniform in the band scale after choosing the exponents and error.
The ordinary prime proportion is then evaluated for all sufficiently
large counting cutoffs, which may depend on the scale. -/
theorem power_band_of_inputs (pit : DegreeOnePrimeIdealTheorem) (hM : MertensProduct)
    {a b : ℕ} (ha : 0<a) (hab : a<b) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      1-(a:ℝ)/b-ε < fraction X (witnessed (t^a) (t^b) (t^a)) := by
  apply frequency_of_band_limits pit (fun t => t^a) (fun t => t^b) _ _ hε
  · filter_upwards [eventually_ge_atTop 1] with t ht
    exact pow_pos ht _
  · exact fun _ hC => band_limit hM hC ha hab

#print axioms frequency_of_band_limits
#print axioms finite_band_bound
#print axioms power_band_of_inputs
end
end Erdos478.GapBands
