import CunninghamArtinBound
import CunninghamUnboundedPrefixes

/-! Lengths and spacing of Cunningham chains from a dyadic count of primitive-root primes. -/

namespace CunninghamChain.DyadicSpacing

open Filter Finset Real ArtinPrimitiveRootsConjecture
open scoped Topology

/-- Base two in the dyadic lower bound of *Primitive roots for every admissible integer base*.
Both endpoints of the interval are excluded. -/
def DyadicPrimitiveRootBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
    c * x / (log x)^2 ≤ (({p : ℕ | x < p ∧ (p : ℝ) < 2*x ∧ p ∈ S 2} : Set ℕ).ncard : ℝ)

/-- The logarithm of the product of forced prime divisors grows at least as fast as
a positive constant times n/log n. -/
theorem prime_product_weight (h : DyadicPrimitiveRootBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ≤ log (∏ q ∈ artinPrimes n, (q : ℝ)) * log n := by
  classical
  obtain ⟨b,hb,H⟩ := h
  obtain ⟨N,hN⟩ := eventually_atTop.mp H
  refine ⟨b/2,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max 4 ⌈2*N⌉₊)] with n hn
  have hn4 : 4 ≤ n := (le_max_left ..).trans hn
  have hnN : 2*N ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right ..).trans hn)
  let x := (n : ℝ)/2
  have hx : 1 < x := by
    dsimp [x]
    have : (4:ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  have hxn : 2*x=n := by dsimp [x]; ring
  have hlog := log_pos hx
  let D := (artinPrimes n).filter (fun p : ℕ => x < p ∧ (p : ℝ) < n)
  have he : ({p : ℕ | x < p ∧ (p : ℝ) < 2*x ∧ p ∈ S 2} : Set ℕ) = ↑D := by
    ext p
    simp only [Set.mem_ofPred_eq, mem_coe, D, mem_filter, artinPrimes, Nat.mem_primesLE, hxn]
    exact ⟨fun ⟨hx',hp,ha⟩ => ⟨⟨⟨by exact_mod_cast hp.le,ha.1⟩,ha⟩,hx',hp⟩,
      fun ⟨⟨_,ha⟩,hx',hp⟩ => ⟨hx',hp,ha⟩⟩
  have hc := hN x (by dsimp [x]; linarith)
  rw [he,Set.ncard_coe_finset] at hc
  let W := ∑ p ∈ artinPrimes n, log (p : ℝ)
  have hw : (D.card : ℝ)*log x ≤ W := by
    calc (D.card : ℝ)*log x = ∑ _p ∈ D, log x := by simp
         _ ≤ ∑ p ∈ D, log (p : ℝ) := sum_le_sum fun p hp =>
           log_le_log (by linarith) (mem_filter.mp (show p ∈ D from hp)).2.1.le
         _ ≤ W := sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun p _ _ => log_natCast_nonneg p
  have hlarge : b*x ≤ W*log n := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hlog)).mp hc
    have hlog' : log x ≤ log n := log_le_log (by linarith) (by linarith)
    have hW : 0 ≤ W := (mul_nonneg (Nat.cast_nonneg _) hlog.le).trans hw
    calc b*x ≤ ((D.card : ℝ)*log x)*log x := by nlinarith only [hh]
         _ ≤ W*log x := mul_le_mul_of_nonneg_right hw hlog.le
         _ ≤ W*log n := mul_le_mul_of_nonneg_left hlog' hW
  rw [Real.log_prod (fun p hp => by
    have hprime := (mem_filter.mp (show p ∈ artinPrimes n from hp)).2.1
    exact_mod_cast hprime.ne_zero)]
  dsimp [x] at hlarge
  linarith

#print axioms prime_product_weight

/-- A positive version of log d · log log d, also defined at small gaps. -/
noncomputable def lengthScale (d : ℕ) : ℝ :=
  let L := 1 + log ((d : ℝ)+1)
  L * (1 + log L)

private theorem lengthScale_ge_one (d : ℕ) : 1 ≤ lengthScale d := by
  have h := log_nonneg (show 1 ≤ (d : ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
  exact one_le_mul_of_one_le_of_one_le (by linarith) (by linarith [log_nonneg (show 1 ≤ 1+log ((d:ℝ)+1) by linarith)])

private theorem invert_length {A L x : ℝ} (hA : 1 ≤ A) (hL : 1 ≤ L)
    (hx : 1 ≤ x) (h : x ≤ A*L*log x) :
    x ≤ (2*A*(1+log (2*A)))*(L*(1+log L)) := by
  have hA' : 0 < A := by linarith
  have hL' : 0 < L := by linarith
  have hx' : 0 < x := by linarith
  have hspos := sqrt_pos.mpr hx'
  have hsq := sq_sqrt hx'.le
  have hlx : log x ≤ 2*√x := by
    have he := log_le_sub_one_of_pos hspos
    rw [log_sqrt hx'.le] at he
    linarith
  have hroot : √x ≤ 2*A*L := by
    apply (mul_le_mul_iff_left₀ hspos).mp
    calc √x*√x = x := by nlinarith only [hsq]
         _ ≤ A*L*log x := h
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hlx (mul_nonneg hA'.le hL'.le)]
  have he := log_le_log hspos hroot
  rw [log_sqrt hx'.le,log_mul (by positivity : 2*A≠0) hL'.ne'] at he
  have hlA := log_nonneg (show 1 ≤ 2*A by linarith)
  have hlL := log_nonneg hL
  calc x ≤ A*L*log x := h
       _ ≤ A*L*(2*((1+log (2*A))*(1+log L))) := by
         apply mul_le_mul_of_nonneg_left _ (by positivity)
         nlinarith only [he,hlA,hlL,mul_nonneg hlA hlL]
       _ = _ := by ring

/-- A single constant works for every positive multiple of the forced product.
It can therefore be applied to a shifted seed or the distance between two shifted seeds. -/
theorem length_bound_of_multiple (h : DyadicPrimitiveRootBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ k d : ℕ, 0 < d → (∏ q ∈ artinPrimes k, q) ∣ d →
      (k : ℝ) ≤ C * lengthScale d := by
  obtain ⟨c,hc,H⟩ := prime_product_weight h
  obtain ⟨N,hN⟩ := eventually_atTop.mp H
  let A := max 1 (1/c)
  have hA : 1 ≤ A := le_max_left ..
  let C := max ((N:ℝ)+1) (2*A*(1+log (2*A)))
  refine ⟨C,lt_of_lt_of_le (by positivity : 0 < (N:ℝ)+1) (le_max_left ..),?_⟩
  intro k d hd hdvd
  by_cases hk : k < max 1 N
  · have hc' : (k:ℝ) ≤ C := by
      apply le_trans _ (le_max_left ..)
      have : k ≤ N+1 := by omega
      exact_mod_cast this
    exact hc'.trans (le_mul_of_one_le_right (le_trans (Nat.cast_nonneg k) hc') (lengthScale_ge_one d))
  · have hk1 : 1 ≤ k := by omega
    have hp : 0 < ∏ q ∈ artinPrimes k, q :=
      prod_pos fun p hp => (mem_filter.mp (show p ∈ artinPrimes k from hp)).2.1.pos
    have hlog : log (∏ q ∈ artinPrimes k, (q : ℝ)) ≤ log ((d:ℝ)+1) := by
      rw [← Nat.cast_prod]
      apply log_le_log (by exact_mod_cast hp)
      have he : ((∏ q ∈ artinPrimes k, q : ℕ):ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd hd hdvd
      linarith
    have hlk := log_nonneg (show 1 ≤ (k:ℝ) by exact_mod_cast hk1)
    let L := 1 + log ((d:ℝ)+1)
    have hL : 1 ≤ L := by dsimp [L]; linarith [log_nonneg (show 1 ≤ (d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])]
    have hg := (hN k (by omega)).trans (mul_le_mul_of_nonneg_right hlog hlk)
    have h₁ : (k:ℝ) ≤ 1/c * (L*log k) := by
      rw [one_div,← div_eq_inv_mul,le_div_iff₀ hc]
      dsimp [L]; nlinarith only [hg,hlk]
    have h₂ : (k:ℝ) ≤ A*L*log k := by
      rw [mul_assoc]
      exact h₁.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (mul_nonneg (by linarith) hlk))
    exact (invert_length hA hL (by exact_mod_cast hk1) h₂).trans
      (mul_le_mul_of_nonneg_right (le_max_right ..) (zero_le_one.trans (lengthScale_ge_one d)))

#print axioms length_bound_of_multiple

/-- The shifted seed z is p+1 for the first kind and p−1 for the second.
The two kinds at one center are allowed to occur together. -/
def IsPrefixCenter (z k : ℕ) : Prop :=
  (∃ p, z = p+1 ∧ ∀ i < k, (firstKindTerm p i).Prime) ∨
  (∃ p, z = p-1 ∧ ∀ i < k, (secondKindTerm p i).Prime)

private theorem below_seed_of_prefix {p k : ℕ} (hk : 6 ≤ k)
    (hp : (∀ i < k, (firstKindTerm p i).Prime) ∨ (∀ i < k, (secondKindTerm p i).Prime)) :
    k < p := by
  have hpr : p.Prime := hp.elim (fun h => h 0 (by omega)) (fun h => h 0 (by omega))
  by_cases hp2 : p=2
  · subst p
    rcases hp with h | h
    · exact False.elim (two_starts_firstKind_length_five.2.2 (h 5 (by omega)))
    · have hh := h 3 (by omega)
      norm_num [secondKindTerm] at hh
  · by_contra! h
    obtain ⟨hf,hs⟩ := both_nonprime_at_pred_of_odd_prime hpr hp2
    have hi : p-1 < k := by have := hpr.two_le; omega
    exact hp.elim (fun a => hf (a _ hi)) (fun a => hs (a _ hi))

/-- Every center of a prefix of length at least six belongs to the same residue
class modulo the product, regardless of the sign. -/
theorem forced_product_dvd_center {z k : ℕ} (hk : 6 ≤ k) (hz : IsPrefixCenter z k) :
    (∏ q ∈ artinPrimes k, q) ∣ z := by
  rcases hz with ⟨p,rfl,hp⟩ | ⟨p,rfl,hp⟩
  · exact firstKind_artin_product_dvd (below_seed_of_prefix hk (.inl hp)) hp
  · exact secondKind_artin_product_dvd (below_seed_of_prefix hk (.inr hp)) hp

private theorem center_pos {z k : ℕ} (hk : 6 ≤ k) (hz : IsPrefixCenter z k) : 0 < z := by
  rcases hz with ⟨p,rfl,hp⟩ | ⟨p,rfl,hp⟩
  · omega
  · have := below_seed_of_prefix hk (.inr hp)
    omega

private theorem scale_mono : Monotone lengthScale := by
  intro a b hab
  have h1 : 1 ≤ (a:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) a]
  have h2 : 1 ≤ (b:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) b]
  have h := log_le_log (by linarith : 0 < (a:ℝ)+1)
    (show (a:ℝ)+1 ≤ (b:ℝ)+1 by exact_mod_cast Nat.succ_le_succ hab)
  have hp := log_nonneg h1
  have hq := log_nonneg h2
  dsimp [lengthScale]
  have hh := log_le_log (show 0 < 1+log ((a:ℝ)+1) by linarith)
    (show 1+log ((a:ℝ)+1) ≤ 1+log ((b:ℝ)+1) by linarith)
  apply mul_le_mul (by linarith) (by linarith)
  · linarith [log_nonneg (show 1 ≤ 1+log ((a:ℝ)+1) by linarith)]
  · linarith

/-- Uniform bounds in the size of a center and in the distance between two
distinct centers, including when their prime prefixes come from opposite signs. -/
theorem prefix_length_and_spacing (h : DyadicPrimitiveRootBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ k z : ℕ, IsPrefixCenter z k →
      (k : ℝ) ≤ C*lengthScale z ∧ ∀ w, IsPrefixCenter w k → z ≠ w →
        (k : ℝ) ≤ C*lengthScale (Nat.dist z w) := by
  obtain ⟨c,hc,H⟩ := length_bound_of_multiple h
  let C := max c 6
  refine ⟨C,hc.trans_le (le_max_left ..),?_⟩
  intro k z hz
  have apply_bound (d : ℕ) (hdiv : 6 ≤ k → 0 < d ∧ (∏ q ∈ artinPrimes k, q) ∣ d) :
      (k:ℝ) ≤ C * lengthScale d := by
    by_cases hk : 6 ≤ k
    · obtain ⟨hd,hm⟩ := hdiv hk
      exact (H k d hd hm).trans (mul_le_mul_of_nonneg_right (le_max_left ..)
        (zero_le_one.trans (lengthScale_ge_one d)))
    · have hsmall : (k:ℝ) ≤ C := (show (k:ℝ) ≤ 6 by exact_mod_cast (by omega : k ≤ 6)).trans (le_max_right ..)
      exact hsmall.trans (le_mul_of_one_le_right (hc.trans_le (le_max_left ..)).le (lengthScale_ge_one d))
  refine ⟨apply_bound z (fun hk => ⟨center_pos hk hz,forced_product_dvd_center hk hz⟩),?_⟩
  intro w hw hne
  apply apply_bound
  intro hk
  refine ⟨Nat.dist_pos_of_ne hne,?_⟩
  have ha := forced_product_dvd_center hk hz
  have hb := forced_product_dvd_center hk hw
  rcases le_total z w with hl | hl
  · rw [Nat.dist_eq_sub_of_le hl]
    exact Nat.dvd_sub hb ha
  · rw [Nat.dist_eq_sub_of_le_right hl]
    exact Nat.dvd_sub ha hb

/-- An individual pointwise bound for the canonical exact-length declarations:
k is O(log p · log log p) uniformly for either sign. -/
theorem exact_length_bound (h : DyadicPrimitiveRootBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ p k : ℕ, IsFirstKindChainOfLength p k ∨ IsSecondKindChainOfLength p k →
      (k : ℝ) ≤ C * lengthScale (p+1) := by
  obtain ⟨C,hC,H⟩ := prefix_length_and_spacing h
  refine ⟨C,hC,?_⟩
  intro p k hp
  rcases hp with hp | hp
  · exact (H k _ (Or.inl ⟨p,rfl,hp.2.1⟩)).1
  · exact (H k _ (Or.inr ⟨p,rfl,hp.2.1⟩)).1.trans
      (mul_le_mul_of_nonneg_left (scale_mono (by omega)) hC.le)

#print axioms forced_product_dvd_center
#print axioms prefix_length_and_spacing
#print axioms exact_length_bound

end CunninghamChain.DyadicSpacing
