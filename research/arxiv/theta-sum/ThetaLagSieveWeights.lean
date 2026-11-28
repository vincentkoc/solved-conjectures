import ThetaPositiveLag
import ThetaTotientTail

/-! A finite square-mean bound for the local factors in the prime-pair sieve. -/
namespace Arxiv.«2501.03234».ThetaLagSieveWeights
open Real Finset ThetaPositiveLag
noncomputable section

def weight (u : ℝ) (n : ℕ) := ∏ p∈n.primeFactors,(1+u/(p:ℝ))

theorem nonneg {u : ℝ} (hu : 0≤u) (n : ℕ) : 0≤weight u n :=
  prod_nonneg (fun _ _ => add_nonneg zero_le_one (div_nonneg hu (Nat.cast_nonneg _)))

theorem mean {u : ℝ} (hu : 0≤u) (L : ℕ) :
    ∑ k∈offsets L,weight u k≤exp u*L := by
  classical
  let S := offsets L
  let P := S.biUnion Nat.primeFactors
  let a (t : Finset ℕ) := ∏ p∈t,(u/(p:ℝ))
  let d (t : Finset ℕ) := ∏ p∈t,p
  have hP (p : ℕ) (hp : p∈P) : 2≤p := by
    obtain ⟨_,_,hn⟩ := mem_biUnion.mp hp;exact (Nat.prime_of_mem_primeFactors hn).two_le
  have ha (t : Finset ℕ) : 0≤a t := prod_nonneg (fun p _ => div_nonneg hu (Nat.cast_nonneg _))
  have row (k : ℕ) (hk : k∈S) : weight u k=∑ t∈P.powerset,if t⊆k.primeFactors then a t else 0 := by
    have he : P.powerset.filter (·⊆k.primeFactors)=k.primeFactors.powerset := by
      ext t;simp only [mem_filter,mem_powerset,and_iff_right_iff_imp]
      exact fun h => h.trans (fun p hp => mem_biUnion.mpr ⟨k,hk,hp⟩)
    dsimp only [a];rw [←sum_filter,he,weight,←prod_one_add]
  have hm (t : Finset ℕ) (ht : t∈P.powerset) :
      (((S.filter (fun k => t⊆k.primeFactors)).card):ℝ)≤L/(d t:ℝ) := by
    have hd : 0<d t := prod_pos (fun p hp => by have := hP p (mem_powerset.mp ht hp);omega)
    have hsub : S.filter (fun k => t⊆k.primeFactors)⊆(range L.succ).filter (fun k => k≠0 ∧ d t∣k) := by
      intro k hk
      obtain ⟨hsk,hh⟩ := mem_filter.mp hk
      obtain ⟨h₀,hl⟩ := mem_erase.mp hsk
      exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hl).trans (Nat.lt_succ_self _)),
        h₀,(prod_dvd_prod_of_subset t k.primeFactors id hh).trans (Nat.prod_primeFactors_dvd k)⟩
    have hc := card_le_card hsub
    rw [Nat.card_multiples'] at hc
    apply (le_div_iff₀ (by exact_mod_cast hd : 0<(d t:ℝ))).mpr
    exact_mod_cast (Nat.mul_le_mul_right (d t) hc).trans (Nat.div_mul_le_self ..)
  have hmass : ∑ t∈P.powerset,a t/(d t:ℝ)≤exp u := by
    have eq (t : Finset ℕ) : a t/(d t:ℝ)=∏ p∈t,((u/(p:ℝ))/p) := by dsimp only [a,d];rw [Nat.cast_prod,←prod_div_distrib]
    simp_rw [eq];rw [←prod_one_add]
    have hs := ThetaTotientTail.reciprocal_pair_tail P 2 (by decide) hP
    norm_num at hs
    have hdom (p : ℕ) (hp : p∈P) : u/(p:ℝ)/p≤u*(((p:ℝ)-1)⁻¹/p) := by
      have hh : (2:ℝ)≤p := by exact_mod_cast hP p hp
      rw [div_eq_mul_inv u,mul_div_assoc];gcongr <;> linarith
    calc _ ≤ ∏ p∈P,exp ((u/(p:ℝ))/p) := by
              apply prod_le_prod
              · intro p _;positivity
              · intro p _;linarith [add_one_le_exp (u/(p:ℝ)/p)]
         _ = _ := (exp_sum ..).symm
         _ ≤ exp u := by
              apply exp_le_exp.mpr
              have hh := sum_le_sum hdom
              rw [←mul_sum] at hh
              nlinarith only [hh,mul_le_mul_of_nonneg_left hs hu]
  calc _ = ∑ k∈S,∑ t∈P.powerset,if t⊆k.primeFactors then a t else 0 := sum_congr rfl row
       _ = ∑ t∈P.powerset,((S.filter (fun k => t⊆k.primeFactors)).card:ℝ)*a t := by
            rw [sum_comm];apply sum_congr rfl;intro t _;rw [←sum_filter,sum_const,nsmul_eq_mul]
       _ ≤ ∑ t∈P.powerset,L/(d t:ℝ)*a t := sum_le_sum (fun t ht => mul_le_mul_of_nonneg_right (hm t ht) (ha t))
       _ = (∑ t∈P.powerset,a t/(d t:ℝ))*L := by rw [sum_mul];apply sum_congr rfl;intros;ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hmass (Nat.cast_nonneg _)

theorem mean_square {D : ℕ} (hD : 0<D) (L : ℕ) :
    ∑ k∈offsets L,(weight 3 (D*k))^2≤exp 12*D*L := by
  have hs (n : ℕ) : (weight 3 n)^2≤weight 12 n := by
    unfold weight
    rw [←prod_pow]
    apply prod_le_prod (fun _ _ => sq_nonneg _)
    intro p hp
    have hh : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    field_simp [show 0<(p:ℝ) by linarith]
    nlinarith
  have hinj : Set.InjOn (fun k : ℕ => D*k) (offsets L) := fun _ _ _ _ hh => Nat.eq_of_mul_eq_mul_left hD hh
  have hsub : (offsets L).image (fun k => D*k)⊆offsets (D*L) := by
    intro h hh;obtain ⟨k,hk,rfl⟩ := mem_image.mp hh
    obtain ⟨h₀,hl⟩ := mem_erase.mp hk
    exact mem_erase.mpr ⟨Nat.mul_ne_zero hD.ne' h₀,mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hl) hD)⟩
  calc _ ≤ ∑ k∈offsets L,weight 12 (D*k) := sum_le_sum (fun k _ => hs _)
       _ = ∑ h∈(offsets L).image (fun k => D*k),weight 12 h := (sum_image hinj).symm
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => nonneg (by norm_num : (0:ℝ)≤12) k)
       _ ≤ _ := by simpa only [Nat.cast_mul,mul_assoc] using mean (by norm_num : (0:ℝ)≤12) (D*L)

#print axioms mean_square

#print axioms mean
end
end Arxiv.«2501.03234».ThetaLagSieveWeights
