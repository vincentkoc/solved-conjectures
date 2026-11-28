import Erdos478CoprimeRootMoments
import Erdos478MeanDeficit
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Variance of factorial collisions at prime gap lengths

Distinct prime gap degrees have joint root moment one. Weight the centered
root counts by reciprocal degrees: each diagonal variance is then bounded by
twice the reciprocal degree, while the mixed terms tend to zero.
-/

namespace Erdos478.GapVariance
noncomputable section
open Polynomial Finset Filter Topology MeanDeficit RootMoments

def gap (k : ℕ) : ℤ[X] := descPochhammer ℤ k - 1
def weight (i : Nat.Primes) : ℝ := 1 / (i.val : ℝ)
def mass (S : Finset Nat.Primes) : ℝ := ∑ i ∈ S, weight i
def observation (i : Nat.Primes) := RootMoments.roots (gap i.val)
def centered (i : Nat.Primes) : ℕ → ℝ := weight i • (observation i - 1)

private theorem gap_degree (i : Nat.Primes) : (gap i.val).IsMonicOfDegree i.val := by
  have h : (descPochhammer ℤ i.val).IsMonicOfDegree i.val :=
    ⟨descPochhammer_natDegree _ _,monic_descPochhammer _ _⟩
  simpa only [gap,sub_eq_add_neg] using h.add_right (q := -(1 : ℤ[X])) (by simpa using i.property.pos)

private theorem gap_irr (i : Nat.Primes) : Irreducible ((gap i.val).map (algebraMap ℤ ℚ)) := by
  simpa [gap] using GapFamilies.irreducible_gap_rat i.property.pos

private theorem one_mean (A : PrimeAverage) (i : Nat.Primes) :
    Tendsto (fun X => A.avg X (observation i)) atTop (𝓝 1) :=
  first_mean A _ (gap_degree i).monic (gap_irr i)

private theorem two_mean (A : PrimeAverage) (i j : Nat.Primes) (h : i ≠ j) :
    Tendsto (fun X => A.avg X (observation i * observation j)) atTop (𝓝 1) := by
  apply joint_mean A _ _ (gap_degree i).monic (gap_degree j).monic (gap_irr i) (gap_irr j)
  rw [(gap_degree i).natDegree_eq,(gap_degree j).natDegree_eq]
  exact (Nat.coprime_primes j.property i.property).mpr (fun he => h (Subtype.ext he.symm))

private theorem nonneg (i : Nat.Primes) (p : ℕ) : 0 ≤ observation i p := Nat.cast_nonneg _

private theorem root_card (i : Nat.Primes) (p : ℕ) [Fact p.Prime] :
    Nat.card (RootPairs.solutions (gap i.val) (ZMod p)) ≤ (descPochhammer (ZMod p) i.val - 1).roots.card := by
  let f := (gap i.val).map (Int.castRingHom (ZMod p))
  have hf : f ≠ 0 := ((gap_degree i).monic.map _).ne_zero
  let e : RootPairs.solutions (gap i.val) (ZMod p) ≃ f.roots.toFinset :=
    Equiv.subtypeEquivRight (fun x => by simp [f,mem_roots hf,IsRoot,eval_map])
  have h := (Nat.card_congr e).trans (by rw [Nat.card_eq_fintype_card,Fintype.card_coe])
  rw [h]
  simpa [f,gap] using Multiset.toFinset_card_le f.roots

private theorem bound (i : Nat.Primes) (p : ℕ) (hp : p.Prime) : observation i p ≤ i.val := by
  let : Fact p.Prime := ⟨hp⟩
  change (Nat.card _ : ℝ) ≤ _
  exact_mod_cast (root_card i p).trans ((Polynomial.card_roots' _).trans
    ((natDegree_sub_le _ _).trans (by simp [descPochhammer_natDegree])))

private theorem weight_pos (i : Nat.Primes) : 0 < weight i :=
  one_div_pos.mpr (by exact_mod_cast i.property.pos)

private theorem weight_le_one (i : Nat.Primes) : weight i ≤ 1 := by
  apply (div_le_iff₀ (by exact_mod_cast i.property.pos : 0 < (i.val:ℝ))).mpr
  simpa using (show (1:ℝ) ≤ i.val by exact_mod_cast i.property.one_le)

private theorem weight_mul (i : Nat.Primes) : weight i * (i.val : ℝ) = 1 :=
  one_div_mul_cancel (by exact_mod_cast i.property.ne_zero)

/-- A pointwise upper bound for the contribution of a pair of gap lengths
to the square of the centered sum. -/
def major (i j : Nat.Primes) : ℕ → ℝ :=
  if i = j then weight i • (observation i + 1) else centered i * centered j

private theorem point_bound (i j : Nat.Primes) (p : ℕ) (hp : p.Prime) :
    centered i p * centered j p ≤ major i j p := by
  by_cases he : i = j
  · subst j
    simp only [major,if_pos rfl,centered,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Pi.one_apply,Pi.add_apply]
    have hw := (weight_pos i).le
    have hr := nonneg i p
    have h := mul_le_mul_of_nonneg_left (bound i p hp) hw
    rw [weight_mul] at h
    have hww := mul_le_mul_of_nonneg_left (weight_le_one i) hw
    nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hw hr),
      mul_nonneg (mul_nonneg hw hw) hr]
  · simp [major,he]

private theorem major_mean (A : PrimeAverage) (i j : Nat.Primes) :
    Tendsto (fun X => A.avg X (major i j)) atTop (𝓝 (if i=j then 2*weight i else 0)) := by
  by_cases he : i = j
  · subst j
    simp only [major,ite_true,map_smul,map_add,smul_eq_mul]
    simpa [two_mul,mul_add] using (tendsto_const_nhds (x := weight i)).mul ((one_mean A i).add (constant_mean A))
  · have eq : major i j = (weight i*weight j) •
        (observation i*observation j-observation i-observation j+1) := by
      ext p
      simp [major,he,centered]
      ring
    simp only [eq,if_neg he,map_smul,smul_eq_mul,map_add,map_sub]
    simpa using (tendsto_const_nhds (x := weight i*weight j)).mul
      ((((two_mean A i j he).sub (one_mean A i)).sub (one_mean A j)).add (constant_mean A))

def majorSum (S : Finset Nat.Primes) : ℕ → ℝ := ∑ i ∈ S, ∑ j ∈ S, major i j

theorem major_limit (A : PrimeAverage) (S : Finset Nat.Primes) :
    Tendsto (fun X => A.avg X (majorSum S)) atTop (𝓝 (2*mass S)) := by
  simp only [majorSum,map_sum]
  have h := tendsto_finsetSum S (fun i _ => tendsto_finsetSum S (fun j _ => major_mean A i j))
  convert! h using 2
  simp [mass,mul_sum]

theorem square_le (S : Finset Nat.Primes) (p : ℕ) (hp : p.Prime) :
    (∑ i ∈ S, centered i p)^2 ≤ majorSum S p := by
  simp only [majorSum,Finset.sum_apply,pow_two,sum_mul_sum]
  exact sum_le_sum fun i _ => sum_le_sum fun j _ => point_bound i j p hp

theorem unbounded_mass (c : ℝ) : ∃ S : Finset Nat.Primes, c < mass S := by
  by_contra! h
  exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun i => (weight_pos i).le) h)

/-- Outside a finite set of primes, the sampled collision count is bounded
by the actual number of missing residues in the pinned factorial image. -/
theorem centered_bound (S : Finset Nat.Primes) :
    ∃ B : ℕ, ∀ p > B, p.Prime → ∑ i ∈ S, centered i p ≤ (deficit p : ℝ) - mass S := by
  let T := S.map (Function.Embedding.subtype Nat.Prime)
  have ht : ∀ k ∈ T, 2 ≤ k := by
    rintro k hk
    obtain ⟨i,_,rfl⟩ := mem_map.mp hk
    exact i.property.two_le
  refine ⟨((GapFamilies.family ℤ T).resultant (GapFamilies.family ℤ T).derivative).natAbs,?_⟩
  intro p hp hprime
  let : Fact p.Prime := ⟨hprime⟩
  have h := GapFamilies.card_add_sum_gap_roots T ht hp
  have hsum : (∑ k ∈ T, (descPochhammer (ZMod p) k - 1).roots.card) =
      ∑ i ∈ S, (descPochhammer (ZMod p) i.val - 1).roots.card :=
    Finset.sum_map S (Function.Embedding.subtype Nat.Prime) (fun k => (descPochhammer (ZMod p) k - 1).roots.card)
  rw [hsum] at h
  have hle : ∑ i ∈ S, (descPochhammer (ZMod p) i.val - 1).roots.card ≤ deficit p := by
    unfold deficit
    omega
  have hm : ∑ i ∈ S, weight i*observation i p ≤ (deficit p : ℝ) := by
    calc
      _ ≤ ∑ i ∈ S, ((descPochhammer (ZMod p) i.val - 1).roots.card : ℝ) := by
        apply sum_le_sum
        intro i _
        exact (mul_le_of_le_one_left (nonneg i p) (weight_le_one i)).trans
          (by change (Nat.card _ : ℝ) ≤ _; exact_mod_cast root_card i p)
      _ ≤ _ := by exact_mod_cast hle
  simpa [centered,mul_sub,sum_sub_distrib,mass] using sub_le_sub_right hm (mass S)

#print axioms centered_bound
#print axioms major_limit
#print axioms square_le
#print axioms unbounded_mass

end
end Erdos478.GapVariance
