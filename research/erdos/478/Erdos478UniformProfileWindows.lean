import Erdos478ProfileWindowLimit

/-! # A common prime cutoff for all positive-mass short factorial profiles -/

namespace Erdos478.LocalWitness
open Polynomial Finset Filter Topology BinaryGap FrobeniusCounts GapSieve GapDensity
open SplittingDensity FrobeniusBands BandWeights FirstCollision
open scoped Classical
noncomputable section

theorem all_prime_endpoint_bound {k p : ℕ} (hk : 2≤k) (hp : p.Prime) :
    (endpoints k p).card≤k := by
  let : Fact p.Prime := ⟨hp⟩
  have deg := gap_degree (by omega : 0<k)
  have le := (primeRoots_le deg.monic hp).trans_eq deg.natDegree_eq
  rw [endpoint_correction] at le
  omega

private abbrev Profile (b : Finset ℕ) := (i : b) → Fin (i.val+1)

private def project {b : Finset ℕ} (f : Profile b → Bool) (a : b → ℕ) : Prop :=
  f (fun i => ⟨min (a i) i.val,by have := min_le_right (a i) i.val; omega⟩)=true

private theorem fraction_on_primes (X : ℕ) {P Q : ℕ → Prop} (eq : ∀ p, p.Prime → (P p ↔ Q p)) :
    fraction X P=fraction X Q := by
  have h : (Nat.primesLE X).filter P=(Nat.primesLE X).filter Q :=
    filter_congr fun p hp => eq p (Nat.mem_primesLE.mp hp).2
  simp only [fraction,h]

private theorem window_on_primes (X : ℕ) {b : Finset ℕ} {P Q : (b → ℕ) → Prop}
    (eq : ∀ p, p.Prime → (realizes b P p ↔ realizes b Q p)) (s : Finset Nat.Primes) (θ : ℝ) :
    profileWindow X b P s θ=profileWindow X b Q s θ := by
  unfold profileWindow
  rw [fraction_on_primes X eq]
  congr 1
  exact fraction_on_primes X (fun p hp => and_congr_left' (eq p hp))

/-- The cutoff X may depend on K but is common to *all* predicates on the
short count vector, including unions of profiles chosen after X. -/
theorem uniform_window_of_inputs (pit : DegreeOnePrimeIdealTheorem) (input : countingInput broad (1/3))
    {H : ℕ → ℕ} {L b z A : ℝ} (hL : 1<L) (hw : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L))
    (hz : 0<z) (hz₁ : z≤1) (hA : A<b*Real.log z-(L-1)/3*Real.log ((1+z)/2)) :
    ∀ᶠ K : ℕ in atTop, ∀ᶠ X : ℕ in atTop, ∀ P : (short K → ℕ) → Prop, 0<density (short K) P →
      1-Real.exp (-A*K/Real.log K)<profileWindow X (short K) P (family K (H K)) (b*K/Real.log K) := by
  filter_upwards [ConditionalGaps.window_exponent input hL hw hA,eventually_ge_atTop 3] with K hr hK
  let s := family K (H K)
  let θ := b*K/Real.log K
  have hb (k : ℕ) (hk : k∈short K) : 2≤k := (mem_Icc.mp hk).1
  have one (f : Profile (short K) → Bool) : ∀ᶠ X : ℕ in atTop,
      0<density (short K) (project f) → 1-Real.exp (-A*K/Real.log K)<profileWindow X (short K) (project f) s θ := by
    by_cases pos : 0<density (short K) (project f)
    · obtain ⟨e,lim,low⟩ := profile_limit pit _ hb _ pos s
        (fun k hk i hi => (mem_Icc.mp hk).2.trans_lt (family_mem.mp hi).1)
        (fun i hi => ⟨(family_mem.mp hi).2.2,by have := (family_mem.mp hi).1; omega⟩) θ
      filter_upwards [lim.eventually_const_lt ((sub_lt_sub_left (Real.exp_lt_exp.mpr hr) 1).trans_le (low z hz hz₁))] with X hx
      exact fun _ => hx
    · exact Eventually.of_forall (fun _ he => (pos he).elim)
  filter_upwards [eventually_all.mpr one] with X all
  intro P pos
  let f (u : Profile (short K)) := decide (P (fun i => (u i).val))
  have eq (p : ℕ) (hp : p.Prime) : realizes (short K) (project f) p ↔ realizes (short K) P p := by
    change decide (P (fun i => min (endpoints i.val p).card i.val))=true ↔ _
    have same (i : short K) := min_eq_left (all_prime_endpoint_bound (hb i.val i.prop) hp)
    simp only [same,decide_eq_true_eq,realizes]
  have mass := density_congr pit hb hb (project f) P eq
  rw [← window_on_primes X eq]
  exact all f (mass.symm ▸ pos)

#print axioms all_prime_endpoint_bound
#print axioms uniform_window_of_inputs
end
end Erdos478.LocalWitness
