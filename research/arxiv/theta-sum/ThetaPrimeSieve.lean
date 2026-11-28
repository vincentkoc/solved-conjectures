import ThetaPeriodMeans
import Mathlib.Data.Nat.Squarefree
/-! Finite sieve weights for the low theta rows. -/
namespace Arxiv.«2501.03234».ThetaPrimeSieve
open Finset ThetaPeriodMeans

/-- Squarefree denominators used in the upper sieve. -/
def moduli (R : ℕ) := (Icc 1 R).filter Squarefree

/-- Normalizing constant of the finite Ramanujan-sum majorant. -/
noncomputable def normalizer (R : ℕ) : ℝ := ∑ a ∈ moduli R, (a.totient:ℝ)⁻¹



/-- The sieve normalization grows at least as fast as the harmonic sum,
up to the sum of reciprocal squares. -/
theorem harmonic_le_normalizer (R : ℕ) : (harmonic R:ℝ) ≤ (∑' n : ℕ, ((n:ℝ)^2)⁻¹)*normalizer R := by
  let Z : ℝ := ∑' n : ℕ, ((n:ℝ)^2)⁻¹
  change _ ≤ Z*normalizer R
  classical
  let s := (moduli R) ×ˢ (Icc 1 R)
  let f (u : ℕ × ℕ) := u.2^2*u.1
  have hsub : Icc 1 R ⊆ s.image f := by
    intro n hn; obtain ⟨hn₀,hnR⟩ := mem_Icc.mp hn
    obtain ⟨a,b,ha,hb,he,hs⟩ := Nat.sq_mul_squarefree_of_pos hn₀
    have hba : b≤n := by rw [← he]; nlinarith [Nat.le_mul_of_pos_right (b^2) ha, Nat.le_self_pow (by decide : 2≠0) b]
    have haa : a≤n := Nat.le_of_dvd hn₀ ⟨b^2,by simpa [mul_comm] using he.symm⟩
    exact mem_image.mpr ⟨(a,b),mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨ha,haa.trans hnR⟩,hs⟩,
      mem_Icc.mpr ⟨hb,hba.trans hnR⟩⟩,he⟩
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  apply (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans
  apply (sum_image_le_of_nonneg (s:=s) (g:=f) (f:=fun n : ℕ => (n:ℝ)⁻¹) (by intros; positivity)).trans
  dsimp only [s]; rw [sum_product]
  calc
    _ = ∑ a ∈ moduli R, (a:ℝ)⁻¹*∑ b ∈ Icc 1 R, ((b:ℝ)^2)⁻¹ := by
      apply sum_congr rfl; intro a _; rw [mul_sum]; apply sum_congr rfl; intro b _; simp [f,mul_comm]
    _ ≤ ∑ a ∈ moduli R, (a.totient:ℝ)⁻¹*Z := by
      apply sum_le_sum; intro a ha
      have hpos := (mem_Icc.mp (mem_filter.mp ha).1).1
      have hphi := Nat.totient_pos.mpr hpos
      apply mul_le_mul (inv_anti₀ (by exact_mod_cast hphi) (by exact_mod_cast Nat.totient_le a)) _
        (by positivity) (by positivity)
      exact (Real.summable_nat_pow_inv.mpr (by decide : 1<2)).sum_le_tsum _ (by intros; positivity)
    _ = _ := by rw [← sum_mul,mul_comm]; rfl

/-- The prime-local Ramanujan factor is one away from the zero class. -/
noncomputable def localFactor (p n : ℕ) : ℝ := if p∣n then 1-(p:ℝ) else 1

private theorem local_onMod (p : ℕ) : OnMod p (localFactor p) := by
  intro n
  simp [localFactor,Nat.dvd_mod_iff]

private theorem local_mean {p : ℕ} (hp : Nat.Prime p) : mean p (localFactor p)=0 := by
  have eq (n) (hn : n∈range p) : localFactor p n=1-(if n=0 then (p:ℝ) else 0) := by
    have h : p∣n ↔ n=0 := ⟨fun h => Nat.eq_zero_of_dvd_of_lt h (mem_range.mp hn),by rintro rfl; simp⟩
    simp [localFactor,h]; split_ifs <;> simp
  unfold mean; rw [sum_congr rfl eq,sum_sub_distrib]
  simp [hp.pos]

private theorem local_square {p : ℕ} (hp : Nat.Prime p) :
    mean p (fun n => localFactor p n^2)=p-1 := by
  have eq (n) (hn : n∈range p) : localFactor p n^2=1+(if n=0 then (p:ℝ)^2-2*p else 0) := by
    have h : p∣n ↔ n=0 := ⟨fun h => Nat.eq_zero_of_dvd_of_lt h (mem_range.mp hn),by rintro rfl; simp⟩
    simp only [localFactor,h]; split_ifs <;> ring
  unfold mean; rw [sum_congr rfl eq,sum_add_distrib]
  have hn : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp [hp.pos]; field_simp [hn]; ring

/-- Product of the local factors for a squarefree denominator. -/
noncomputable def ramanujan (r n : ℕ) : ℝ := ∏ p ∈ r.primeFactors, localFactor p n

private noncomputable def choiceAt (s : Finset ℕ) (p n : ℕ) : ℝ :=
  if p∈s then localFactor p n else 1

private theorem prod_choiceAt {s t : Finset ℕ} (hst : s⊆t) (n : ℕ) :
    ∏ p ∈ t, choiceAt s p n = ∏ p ∈ s, localFactor p n := by
  classical
  simp only [choiceAt,← prod_filter]
  congr 1
  ext p; simp only [mem_filter]; exact and_iff_right_of_imp (fun h => hst h)

/-- Orthogonality on any full period of two squarefree Ramanujan factors. -/
theorem mean_ramanujan_mul {r s P : ℕ} (hr : Squarefree r) (hs : Squarefree s)
    (hP : 0<P) (hrP : r∣P) (hsP : s∣P) :
    mean P (fun n => ramanujan r n*ramanujan s n) = if r=s then (r.totient:ℝ) else 0 := by
  classical
  let U := r.primeFactors∪s.primeFactors
  let F p n := choiceAt r.primeFactors p n * choiceAt s.primeFactors p n
  have hpU {p} (hp : p∈U) : Nat.Prime p :=
    (mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  have hdU : (∏ p ∈ U,p)∣P := by
    apply Finset.prod_primes_dvd _ (fun p hp => Nat.prime_iff.mp (hpU hp))
    intro p hp
    exact (mem_union.mp hp).elim (fun h => (Nat.dvd_of_mem_primeFactors h).trans hrP)
      (fun h => (Nat.dvd_of_mem_primeFactors h).trans hsP)
  have hf (p) (_ : p∈U) : OnMod p (F p) := by
    intro n; simp [F,choiceAt,local_onMod p n]
  have H (n) : ramanujan r n*ramanujan s n=∏ p ∈ U,F p n := by
    rw [show ∏ p ∈ U,F p n = (∏ p ∈ U,choiceAt r.primeFactors p n)*(∏ p ∈ U,choiceAt s.primeFactors p n)
      from prod_mul_distrib,prod_choiceAt subset_union_left,prod_choiceAt subset_union_right]; rfl
  simp_rw [H]
  rw [mean_lift (prod_pos (fun p hp => (hpU hp).pos)) hP hdU (onMod_prod F hf),
    mean_prime_product U F (fun _ hp => hpU hp) hf]
  split_ifs with he
  · subst s
    have hu : U=r.primeFactors := union_self _
    rw [hu]
    calc
      _ = ∏ p ∈ r.primeFactors, ((p:ℝ)-1) := by
        apply prod_congr rfl; intro p hp
        simpa only [F,choiceAt,if_pos hp,pow_two] using local_square (Nat.prime_of_mem_primeFactors hp)
      _ = (r.totient:ℝ) := by
        rw [Nat.totient_eq_div_primeFactors_mul,Nat.prod_primeFactors_of_squarefree hr,
          Nat.div_self (Nat.pos_of_ne_zero hr.ne_zero),one_mul,Nat.cast_prod]
        apply prod_congr rfl; intro p hp
        rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le,Nat.cast_one]
  · have hne : r.primeFactors≠s.primeFactors := by
      intro h
      exact he (by rw [← Nat.prod_primeFactors_of_squarefree hr,h,Nat.prod_primeFactors_of_squarefree hs])
    obtain ⟨p,hp⟩ : ∃ p, ¬(p∈r.primeFactors ↔ p∈s.primeFactors) := by
      by_contra! hh; exact hne (Finset.ext hh)
    have hp' : p∈U := mem_union.mpr (by tauto)
    apply prod_eq_zero hp'
    by_cases h₁ : p∈r.primeFactors
    · have h₂ : p∉s.primeFactors := by tauto
      simpa only [F,choiceAt,if_pos h₁,if_neg h₂,mul_one] using local_mean (hpU hp')
    · have h₂ : p∈s.primeFactors := by tauto
      simpa only [F,choiceAt,if_neg h₁,if_pos h₂,one_mul] using local_mean (hpU hp')


/-- The square of the normalized sum is nonnegative on every integer and is one
on primes exceeding the sieve level. -/
noncomputable def weight (R n : ℕ) : ℝ :=
  ((∑ r ∈ moduli R, ramanujan r n/(r.totient:ℝ))/normalizer R)^2

theorem one_le_normalizer {R : ℕ} (hR : 1≤R) : 1≤normalizer R := by
  have h : 1∈moduli R := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,hR⟩,squarefree_one⟩
  simpa [normalizer] using (single_le_sum (f:=fun r : ℕ => (r.totient:ℝ)⁻¹) (fun i _ => by positivity) h)

theorem weight_prime {R p : ℕ} (hR : 1≤R) (hp : Nat.Prime p) (hpR : R<p) :
    weight R p=1 := by
  have H (r) (hr : r∈moduli R) : ramanujan r p=1 := by
    apply prod_eq_one; intro q hq
    have hqr := Nat.le_of_mem_primeFactors hq
    have hq' := Nat.prime_of_mem_primeFactors hq
    have hrR := (mem_Icc.mp (mem_filter.mp hr).1).2
    have hnd : ¬q∣p := by
      intro h
      rcases (Nat.dvd_prime hp).mp h with h|h
      · exact hq'.ne_one h
      · omega
    exact if_neg hnd
  unfold weight
  have he : ∑ r∈moduli R, ramanujan r p/(r.totient:ℝ) = normalizer R := by
    unfold normalizer; apply sum_congr rfl; intro r hr; rw [H r hr,one_div]
  rw [he,div_self (by linarith [one_le_normalizer hR] : normalizer R≠0)]
  norm_num

/-- Exact mass of the finite square sieve on each common complete period. -/
theorem mean_weight {R P : ℕ} (hR : 1≤R) (hP : 0<P) (h : ∀ r∈moduli R, r∣P) :
    mean P (weight R) = (normalizer R)⁻¹ := by
  classical
  have he (n) : weight R n =
      (∑ r ∈ moduli R, ∑ s ∈ moduli R, (ramanujan r n*ramanujan s n) /
        ((r.totient:ℝ)*s.totient)) / (normalizer R)^2 := by
    unfold weight; rw [div_pow,pow_two, sum_mul_sum]
    congr 1
    apply sum_congr rfl; intro r _; apply sum_congr rfl; intro s _; ring
  unfold mean; simp_rw [he,← sum_div]
  rw [sum_comm]
  have ht (r : ℕ) (hr : r∈moduli R) :
      ∑ n ∈ range P, ∑ s ∈ moduli R, ramanujan r n * ramanujan s n /
          ((r.totient:ℝ)*s.totient) = P*(r.totient:ℝ)⁻¹ := by
    rw [sum_comm]
    have H (s) (hs : s∈moduli R) :
        (∑ n∈range P,ramanujan r n*ramanujan s n/((r.totient:ℝ)*s.totient)) =
          (if r=s then P*(r.totient:ℝ)⁻¹ else 0) := by
      have ho := mean_ramanujan_mul (mem_filter.mp hr).2 (mem_filter.mp hs).2 hP (h r hr) (h s hs)
      unfold mean at ho
      have hh := (div_eq_iff (by exact_mod_cast hP.ne' : (P:ℝ)≠0)).mp ho
      rw [← sum_div,hh]; split_ifs with heq
      · subst s; have hp := Nat.totient_pos.mpr ((mem_Icc.mp (mem_filter.mp hr).1).1)
        field_simp [show (r.totient:ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hp.ne']
      · simp
    rw [sum_congr rfl H]; simp [hr]
  rw [sum_congr rfl ht, ← mul_sum]
  change ((P:ℝ)*normalizer R/(normalizer R)^2)/P=(normalizer R)⁻¹
  field_simp [show normalizer R≠0 by linarith [one_le_normalizer hR],Nat.cast_ne_zero.mpr hP.ne']

/-- Each unnormalized sieve term has a polynomial bound independent of the argument. -/
theorem ramanujan_bound {r : ℕ} (hr : Squarefree r) (n : ℕ) : |ramanujan r n| ≤ r := by
  rw [ramanujan,Finset.abs_prod]
  calc
    _ ≤ ∏ p ∈ r.primeFactors, (p:ℝ) := by
      apply prod_le_prod (fun _ _ => abs_nonneg _)
      intro p hp
      have hp' : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      unfold localFactor; split_ifs
      · rw [abs_of_nonpos (by linarith : (1:ℝ)-(p:ℝ)≤0)]; linarith
      · rw [abs_one]; linarith
    _ = _ := by rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hr]

theorem ramanujan_onMod {r : ℕ} (hr : Squarefree r) : OnMod r (ramanujan r) := by
  change OnMod r (fun n => ∏ p ∈ r.primeFactors, localFactor p n)
  simpa only [Nat.prod_primeFactors_of_squarefree hr] using
    (onMod_prod localFactor (s:=r.primeFactors) (fun p _ => local_onMod p))

/-- The prime sieve weight depends only on divisibility by its local primes.
Multiplication by a unit in a common period preserves it. -/
theorem weight_invariant {P R : ℕ} (h : ∀ r∈moduli R,r∣P) (u : (ZMod P)ˣ) (x : ZMod P) :
    weight R ((u:ZMod P)*x).val=weight R x.val := by
  unfold weight
  congr 2
  apply sum_congr rfl; intro r hr
  congr 1
  apply prod_congr rfl; intro p hp
  have hP := (Nat.dvd_of_mem_primeFactors hp).trans (h r hr)
  have hu : p.Coprime (u:ZMod P).val :=
    ((ZMod.val_coe_unit_coprime u).coprime_dvd_right hP).symm
  simp only [localFactor,ZMod.val_mul,Nat.dvd_mod_iff hP,hu.dvd_mul_left]

/-- A complete period with the square sieve costs the inverse normalizer times
the inverse density of unit residues in the smaller modulus. -/
theorem weighted_period {q R P : ℕ} (hq : 0<q) (hR : 1≤R) (hP : 0<P)
    (hd : q∣P) (hr : ∀ r∈moduli R,r∣P) {h : ℕ → ℝ} (hf : OnMod q h)
    (hs : ∀ n, ¬n.Coprime q → h n=0) :
    |mean P (fun n => weight R n*h n)| ≤ (normalizer R)⁻¹*((q:ℝ)/q.totient)*|mean q h| := by
  simpa only [mean_weight hR hP hr] using
    (weighted_unit_mean hq hP hd (weight R) h (fun _ => sq_nonneg _) (weight_invariant hr) hf hs)

end Arxiv.«2501.03234».ThetaPrimeSieve
#print axioms Arxiv.«2501.03234».ThetaPrimeSieve.ramanujan_bound
#print axioms Arxiv.«2501.03234».ThetaPrimeSieve.ramanujan_onMod
#print axioms Arxiv.«2501.03234».ThetaPrimeSieve.weight_invariant
#print axioms Arxiv.«2501.03234».ThetaPrimeSieve.weighted_period
#print axioms Arxiv.«2501.03234».ThetaPrimeSieve.harmonic_le_normalizer
#print axioms Arxiv.«2501.03234».ThetaPrimeSieve.mean_ramanujan_mul
#print axioms Arxiv.«2501.03234».ThetaPrimeSieve.weight_prime
#print axioms Arxiv.«2501.03234».ThetaPrimeSieve.mean_weight
