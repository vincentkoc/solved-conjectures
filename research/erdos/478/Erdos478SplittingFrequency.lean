import Erdos478DisjointGapFamilies
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Nth

/-!
# An elementary count of primes with prescribed factorial gaps

Finite Euler products bound the number of possible values of a polynomial
whose prime divisors lie in a given set.
-/

namespace Erdos478.SplittingFrequency

open Finset Nat Polynomial Filter

private noncomputable def weight (s : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-s)

private theorem weight_pow (s : ℝ) (p k : ℕ) :
    weight s (p ^ k) = (weight s p) ^ k := by
  simp only [weight, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _),
    mul_comm (k : ℝ), Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]

/-- A finite Euler product controls the mass supported on integers whose
prime factors all belong to the prescribed finite set. -/
theorem factored_mass (s : ℝ) (hs : 0 < s) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Summable (fun n : factoredNumbers P ↦ ((n : ℕ) : ℝ) ^ (-s)) ∧
    (∑' n : factoredNumbers P, ((n : ℕ) : ℝ) ^ (-s)) ≤
      Real.exp ((1 - (2 : ℝ) ^ (-s))⁻¹ * ∑ p ∈ P, (p : ℝ) ^ (-s)) := by
  let f := weight s
  have hf (p : ℕ) : 0 ≤ f p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlt {p : ℕ} (hp : p.Prime) : f p < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hgp {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ ↦ ‖f (p^k)‖) := by
    have he (k : ℕ) : ‖f (p^k)‖ = (f p)^k := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf _)]
      exact weight_pow s p k
    simpa only [he] using summable_geometric_of_lt_one (hf p) (hlt hp)
  have hm {a b : ℕ} (_ : a.Coprime b) : f (a*b) = f a * f b := by
    simp [f,weight,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  have one : f 1 = 1 := by simp [f,weight]
  have hsum := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    one (fun h ↦ hm h) (fun hp ↦ hgp hp) P).2
  refine ⟨hsum.summable, ?_⟩
  change (∑' n : factoredNumbers P, f n) ≤ Real.exp ((1 - f 2)⁻¹ * ∑ p ∈ P, f p)
  rw [hsum.tsum_eq, filter_eq_self.mpr hP, mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    exact tsum_nonneg fun k ↦ hf _
  intro p hp
  have heq : (∑' k : ℕ, f (p^k)) = (1-f p)⁻¹ := by
    simpa only [f, weight_pow] using tsum_geometric_of_lt_one (hf p) (hlt (hP p hp))
  have h2 : f p ≤ f 2 := by
    apply Real.rpow_le_rpow_of_nonpos (by norm_num)
    · exact_mod_cast (hP p hp).two_le
    · linarith
  have hpos := sub_pos.mpr (hlt (hP p hp))
  have hpos2 := sub_pos.mpr (hlt (by decide : Nat.Prime 2))
  rw [heq]
  calc
    (1 - f p)⁻¹ = (1 - f p)⁻¹ * f p + 1 := by field_simp; ring
    _ ≤ (1 - f 2)⁻¹ * f p + 1 := by gcongr; exact hf p
    _ ≤ _ := Real.add_one_le_exp _

/-- A convergent prime-power weight remains summable on the positive integers
generated multiplicatively by those primes. -/
theorem summable_supported {S : Set ℕ} (s : ℝ) (hs : 0 < s)
    (hS : Summable fun p : S ↦ ((p : ℕ) : ℝ) ^ (-s)) :
    Summable (fun n : {n : ℕ // n ≠ 0 ∧ ↑n.primeFactors ⊆ S} ↦ ((n : ℕ) : ℝ) ^ (-s)) := by
  classical
  let A := {n : ℕ // n ≠ 0 ∧ ↑n.primeFactors ⊆ S}
  let f := weight s
  have hf (n : ℕ) : 0 ≤ f n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  apply summable_of_sum_le (c := Real.exp ((1-f 2)⁻¹ * ∑' p : S, f p)) (fun n : A ↦ hf n)
  intro T
  let P := T.biUnion fun n : A ↦ (n : ℕ).primeFactors
  have hP (p) (hp : p ∈ P) : p.Prime := by
    obtain ⟨_,_,hm⟩ := mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors hm
  have hPS : ∀ p ∈ P, p ∈ S := by
    intro p hp
    obtain ⟨n,_,hm⟩ := mem_biUnion.mp hp
    exact n.property.2 hm
  have hTP (n : A) (hn : n ∈ T) : (n : ℕ) ∈ factoredNumbers P :=
    mem_factoredNumbers_of_primeFactors_subset n.property.1 (subset_biUnion_of_mem (fun x : A ↦ (x : ℕ).primeFactors) hn)
  let v : {x // x ∈ T} ↪ factoredNumbers P :=
    ⟨fun n ↦ ⟨(n.val : ℕ),hTP n.val n.property⟩, fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun z : factoredNumbers P ↦ (z : ℕ)) h))⟩
  have hmass := factored_mass s hs P hP
  have hval : ∑ n ∈ T, f n ≤ ∑' n : factoredNumbers P, f n := by
    rw [← sum_attach T (fun n : A ↦ f n)]
    have he (x : T) : (v x : ℕ) = ((x.val : A) : ℕ) := rfl
    have hh := hmass.1.sum_le_tsum (T.attach.map v) (fun x _ ↦ hf x)
    change (∑ i ∈ T.attach.map v, f i) ≤ ∑' n : factoredNumbers P, f n at hh
    simpa only [sum_map, he] using hh
  have hbound : ∑ p ∈ P, f p ≤ ∑' p : S, f p := by
    have h := hS.sum_le_tsum (P.subtype (· ∈ S)) (fun x _ ↦ hf x)
    rwa [← sum_subtype_map_embedding (g := f) (fun _ _ ↦ rfl), subtype_map_of_mem hPS] at h
  exact hval.trans (hmass.2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbound
    (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)))))))

private theorem eventually_positive (f : ℝ[X]) (hf : 0 < f.leadingCoeff) :
    ∀ᶠ x in atTop, 0 < f.eval x := by
  by_cases h : f.natDegree = 0
  · obtain ⟨c,rfl⟩ : ∃ c, f = C c := ⟨_,eq_C_of_natDegree_eq_zero h⟩
    exact Eventually.of_forall fun x ↦ by simpa using hf
  · exact (f.tendsto_atTop_of_leadingCoeff_nonneg
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero h)) hf.le).eventually_gt_atTop 0

/-- A monic polynomial of positive degree has an increasing positive tail.
The values grow at most as a constant times the leading power. -/
private theorem polynomial_tail (g : ℤ[X]) (hg : g.Monic) (hd : 0 < g.natDegree) :
    ∃ M : ℕ, (∀ n ≥ M, 0 < g.eval (n : ℤ)) ∧
      StrictMono (fun n : ℕ ↦ (g.eval ((n + M : ℕ) : ℤ)).natAbs) ∧
      ∀ᶠ n : ℕ in atTop, ((g.eval (n : ℤ)).natAbs : ℝ) ≤ 2 * (n : ℝ)^g.natDegree := by
  let F := g.map (Int.castRingHom ℝ)
  have hF : F.Monic := hg.map _
  have hdeg : F.natDegree = g.natDegree := hg.natDegree_map _
  have hder : 0 < F.derivative.leadingCoeff := by
    rw [leadingCoeff_derivative, hF.leadingCoeff, one_mul, hdeg]
    exact_mod_cast hd
  obtain ⟨a,ha⟩ := ((eventually_positive F (hF.leadingCoeff ▸ zero_lt_one)).and
    (eventually_positive _ hder)).exists_forall_of_atTop
  obtain ⟨M,hM⟩ := exists_nat_ge a
  have hmono : StrictMonoOn F.eval (Set.Ici a) :=
    strictMonoOn_of_deriv_pos (convex_Ici _) F.differentiable.continuous.continuousOn
      (fun x hx ↦ F.deriv ▸ (ha x (interior_subset hx)).2)
  have hv (n : ℕ) : F.eval (n : ℝ) = ((g.eval (n : ℤ) : ℤ) : ℝ) := by
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      (eval_map_apply (p := g) (Int.castRingHom ℝ) (n : ℤ))
  have hp {n : ℕ} (hn : M ≤ n) : 0 < g.eval (n : ℤ) := by
    have hh := (ha (n : ℝ) (hM.trans (by exact_mod_cast hn))).1
    rw [hv] at hh
    exact_mod_cast hh
  refine ⟨M,fun _ hn ↦ hp hn, ?_, ?_⟩
  · intro n m h
    have h' := hmono (a := ((n+M : ℕ) : ℝ)) (b := ((m+M : ℕ) : ℝ))
      (hM.trans (by norm_cast; omega)) (hM.trans (by norm_cast; omega)) (by exact_mod_cast Nat.add_lt_add_right h M)
    dsimp only at h'
    rw [hv,hv] at h'
    have hi : g.eval ((n+M : ℕ) : ℤ) < g.eval ((m+M : ℕ) : ℤ) := by exact_mod_cast h'
    have h1 := hp (show M ≤ n+M by omega)
    have h2 := hp (show M ≤ m+M by omega)
    dsimp only
    rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs, abs_of_pos h1, abs_of_pos h2]
    exact hi
  · have he := F.isEquivalent_atTop_lead.isLittleO.bound (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually he, eventually_ge_atTop M] with n hn hM'
    simp only [Pi.sub_apply, hF.leadingCoeff, one_mul, hdeg, hv, Real.norm_eq_abs] at hn
    have hnat : ((g.eval (n : ℤ)).natAbs : ℝ) = ((g.eval (n : ℤ) : ℤ) : ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (Int.cast : ℤ → ℝ)
        ((Int.natCast_natAbs _).trans (abs_of_pos (hp hM')))
    rw [hnat]
    simp only [abs_pow, abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)] at hn
    linarith [(abs_le.mp hn).2]

set_option maxHeartbeats 600000 in
/-- Prime divisors of the values of a positive-degree monic integer
polynomial have a divergent reciprocal-power sum at exponent one over
the degree. The prime set may be any superset of these divisors. -/
theorem polynomial_prime_divergence (g : ℤ[X]) (hg : g.Monic) (hd : 0 < g.natDegree)
    (S : Set ℕ) (hS : ∀ n p : ℕ, p.Prime → p ∣ (g.eval (n : ℤ)).natAbs → p ∈ S) :
    ¬ Summable (fun p : S ↦ ((p : ℕ) : ℝ) ^ (-(g.natDegree : ℝ)⁻¹)) := by
  intro h
  let s : ℝ := (g.natDegree : ℝ)⁻¹
  have hs : 0 < s := inv_pos.mpr (by exact_mod_cast hd)
  let a (n : ℕ) := (g.eval (n : ℤ)).natAbs
  obtain ⟨M,hpos,hmono,hub⟩ := polynomial_tail g hg hd
  let A := {n : ℕ // n ≠ 0 ∧ ↑n.primeFactors ⊆ S}
  have hin (n : ℕ) : a (n+M) ≠ 0 ∧ ↑(a (n+M)).primeFactors ⊆ S := by
    refine ⟨Int.natAbs_ne_zero.mpr (hpos (n+M) (by omega)).ne', ?_⟩
    intro p hp
    exact hS _ _ (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  let e : ℕ ↪ A :=
    ⟨fun n ↦ ⟨a (n+M),hin n⟩, fun _ _ he ↦ hmono.injective (congrArg (fun z : A ↦ z.val) he)⟩
  have hfull : Summable (fun n : ℕ ↦ (a n : ℝ)^(-s)) :=
    (summable_nat_add_iff (f := fun n ↦ (a n : ℝ)^(-s)) M).mp <|
      (summable_supported (S := S) s hs h).comp_injective (i := (e : ℕ → A)) e.injective
  have hc : 0 < (2:ℝ)^(-s) := Real.rpow_pos_of_pos (by norm_num) _
  have hless : Summable (fun n : ℕ ↦ (2:ℝ)^(-s) * (n:ℝ)^(-1:ℝ)) := by
    apply hfull.of_norm_bounded_eventually_nat
    filter_upwards [hub, eventually_ge_atTop (M+1)] with n hn hn'
    have hn0 : 0 < n := by omega
    have has : 0 < (a n : ℝ) := by
      exact_mod_cast Int.natAbs_pos.mpr (hpos n (by omega)).ne'
    have hb := Real.rpow_le_rpow_of_nonpos has hn (neg_nonpos.mpr hs.le)
    have hr : (2 * (n:ℝ)^g.natDegree)^(-s) = (2:ℝ)^(-s) * (n:ℝ)^(-1:ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul (Nat.cast_nonneg n)]
      have he : (g.natDegree : ℝ) * -s = -1 := by
        dsimp [s]
        field_simp [show (g.natDegree : ℝ) ≠ 0 by exact_mod_cast hd.ne']
      rw [he]
    rw [← hr, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact hb
  have harm : Summable (fun n : ℕ ↦ (n:ℝ)^(-1:ℝ)) := by
    simpa [hc.ne'] using hless.mul_left ((2:ℝ)^(-s))⁻¹
  exact (lt_irrefl _ (Real.summable_nat_rpow.mp harm))

/-- Divergence at exponent `s` forces the counting function to exceed
`X^(1/r)` at arbitrarily large cutoffs whenever `r*s > 1`. -/
theorem count_of_divergence (S : Set ℕ) [DecidablePred (· ∈ S)] {s r : ℝ}
    (hs : 0 < s) (hr : 1 < r*s)
    (h : ¬ Summable (fun p : S ↦ ((p : ℕ) : ℝ)^(-s))) (N : ℕ) :
    ∃ X > N, (X : ℝ) < ((Nat.count (· ∈ S) X : ℕ) : ℝ)^r := by
  classical
  by_contra! hh
  have hi : S.Infinite := fun hf ↦ h (hf.summable (fun n : ℕ ↦ (n:ℝ)^(-s)))
  let e := @Nat.Subtype.orderIsoOfNat S hi.to_subtype
  let a := Nat.nth (· ∈ S)
  have ha (j : ℕ) : a j = (e j : ℕ) := Nat.nth_apply_eq_orderIsoOfNat hi j
  have hsum : Summable (fun j : ℕ ↦ (a j : ℝ)^(-s)) := by
    apply (Real.summable_nat_rpow.mpr (show r * -s < -1 by linarith)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_gt_atTop N] with j hj
    have hja : j ≤ a j := (Nat.nth_strictMono hi).id_le j
    have hc := hh (a j) (by omega)
    change ((Nat.count (fun x ↦ x ∈ S) (Nat.nth (fun x ↦ x ∈ S) j) : ℕ) : ℝ)^r ≤ _ at hc
    rw [Nat.count_nth_of_infinite (p := fun x ↦ x ∈ S) hi] at hc
    have hj' : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have hbound := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hj' r) hc (neg_nonpos.mpr hs.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      Real.rpow_mul hj'.le]
    exact hbound
  apply h
  apply e.toEquiv.summable_iff.mp
  change Summable (fun j : ℕ ↦ ((e j : ℕ) : ℝ)^(-s))
  simpa only [ha] using hsum

private theorem summable_with_cutoff (S : Set ℕ) (B : ℕ) (s : ℝ)
    (h : Summable (fun p : S ↦ ((p : ℕ) : ℝ)^(-s))) :
    Summable (fun p : (Set.Iic B ∪ S : Set ℕ) ↦ ((p : ℕ) : ℝ)^(-s)) := by
  classical
  let f := weight s
  have h1 : Summable ((Set.Iic B).indicator f) :=
    summable_subtype_iff_indicator.mp ((Set.finite_Iic B).summable f)
  have h2 : Summable (S.indicator f) := summable_subtype_iff_indicator.mp h
  apply (summable_subtype_iff_indicator (f := f) (s := Set.Iic B ∪ S)).mpr
  apply (h1.add h2).of_nonneg_of_le
  · exact Set.indicator_nonneg (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
  intro n
  have hf : 0 ≤ f n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  by_cases hn : n ∈ Set.Iic B <;> by_cases hS : n ∈ S <;>
    simp [Set.indicator, hn, hS, f, weight] at hf ⊢
  linarith

/-- Every prime set containing the complete-splitting primes of a monic
integral polynomial beyond a fixed cutoff has a divergent reciprocal-power
sum. An explicit exponent is the reciprocal of the factorial of the degree. -/
theorem splitting_prime_divergence (t : ℤ[X]) (ht : t.Monic) (B : ℕ) (S : Set ℕ)
    (hS : ∀ p > B, p.Prime → (t.map (Int.castRingHom (ZMod p))).Splits → p ∈ S)
    (hpS : ∀ p ∈ S, p.Prime) :
    ¬ Summable (fun p : S ↦ ((p : ℕ) : ℝ)^(-(t.natDegree.factorial : ℝ)⁻¹)) := by
  intro h
  obtain ⟨g,hg,hd,hdeg,C,hC⟩ := FallingGap.splitting_test t ht
  let s : ℝ := (g.natDegree : ℝ)⁻¹
  have hsub : Summable (fun p : S ↦ ((p : ℕ) : ℝ)^(-s)) := by
    apply h.of_nonneg_of_le (fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    intro p
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (hpS p p.property).one_lt.le
    · change -(g.natDegree : ℝ)⁻¹ ≤ -(t.natDegree.factorial : ℝ)⁻¹
      exact neg_le_neg (inv_anti₀ (by exact_mod_cast hd) (by exact_mod_cast hdeg))
  apply polynomial_prime_divergence g hg hd (Set.Iic (max B C) ∪ S) _ (summable_with_cutoff S _ s hsub)
  intro n p hprime hdiv
  by_cases hsmall : p ≤ max B C
  · exact Or.inl hsmall
  have hbig := lt_of_not_ge hsmall
  have hroot : (g.map (Int.castRingHom (ZMod p))).IsRoot ((n : ℤ) : ZMod p) := by
    rw [IsRoot.def, eval_map, eval₂_at_intCast]
    exact (CharP.intCast_eq_zero_iff (ZMod p) p _).mpr (Int.ofNat_dvd_left.mpr hdiv)
  exact Or.inr (hS p (lt_of_le_of_lt (le_max_left _ _) hbig) hprime
    (hC p (lt_of_le_of_lt (le_max_right _ _) hbig) hprime ⟨_,hroot⟩))

/-- The primes for which the original factorial image has the prescribed
triangular deficit in the class one modulo `m`. -/
def witness (L m p : ℕ) : Prop :=
  p.Prime ∧ m ∣ p-1 ∧ ((Ico 1 p).image (fun n ↦ n.factorial % p)).card + (L+2).choose 2 ≤ p

instance (L m : ℕ) : DecidablePred (witness L m) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The degree of the product of the gap polynomials and the cyclotomic
polynomial bounds the degree of the splitting field by its factorial. -/
def degreeBound (L m : ℕ) := ((L+2).choose 2 - 1 + m.totient).factorial

theorem deficit_prime_divergence (L m : ℕ) (hm : 0 < m) :
    ¬ Summable (fun p : {p : ℕ // witness L m p} ↦ ((p : ℕ) : ℝ)^(-(degreeBound L m : ℝ)⁻¹)) := by
  obtain ⟨t,ht,hdeg,B,hB⟩ := GapFamilies.progression_splitting_test L m hm
  have h := splitting_prime_divergence t ht B {p | witness L m p}
    (fun p hp hprime hsplit ↦ by
      obtain ⟨hcong,_,_,hcard⟩ := hB p hp hprime hsplit
      exact ⟨hprime,hcong,hcard⟩) (fun _ h ↦ h.1)
  rw [hdeg] at h
  exact h

/-- For any real `r` above the explicit field-degree bound, arbitrarily
large cutoffs X have more than X^(1/r) deficit witnesses strictly below X. -/
theorem many_deficit_primes (L m : ℕ) (hm : 0 < m) (r : ℝ) (hr : degreeBound L m < r) (N : ℕ) :
    ∃ X > N, (X : ℝ) < ((Nat.count (witness L m) X : ℕ) : ℝ)^r := by
  have hD : (0:ℝ) < degreeBound L m := by exact_mod_cast Nat.factorial_pos _
  apply count_of_divergence {p | witness L m p} (inv_pos.mpr hD) _ (deficit_prime_divergence L m hm)
  rwa [← div_eq_mul_inv, one_lt_div hD]

#print axioms many_deficit_primes
#print axioms deficit_prime_divergence
#print axioms splitting_prime_divergence

#print axioms count_of_divergence
#print axioms polynomial_prime_divergence
#print axioms summable_supported
#print axioms factored_mass

end Erdos478.SplittingFrequency
