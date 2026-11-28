import HosoyaABCRadicals
import LucasFibonacciIsolatedDivisors
import Mathlib.NumberTheory.Primorial

/-! Prime divisors of multiplicity one exclusive to individual Hosoya sites. -/

namespace Arxiv.«2211.10788».HosoyaRadical

open Finset Filter Real HosoyaNeighbor
open scoped Topology

/-- Primes occurring exactly once at the specified site and nowhere else on
either diagonal within the inclusive radius H. -/
noncomputable def isolatedSimplePrimes (s : HosoyaNeighbor) (n H Y : ℕ) : Finset ℕ := by
  classical
  exact (s.value n).primeFactors.filter fun p =>
    (s.value n).factorization p=1 ∧ Y<p ∧
      ∀ t m, s≠t ∨ n≠m → Nat.dist n m ≤ H → ¬p ∣ t.value m

private theorem simple_part_le (s : HosoyaNeighbor) (n H Y : ℕ) :
    simplePart (s.value n) ≤ primorial Y*shiftDetProduct H*(isolatedSimplePrimes s n H Y).prod id := by
  classical
  let y := s.value n
  let A := y.primeFactors.filter (fun p => y.factorization p=1)
  let G := isolatedSimplePrimes s n H Y
  let M := primorial Y*shiftDetProduct H
  have hM : 0 < M := Nat.mul_pos (primorial_pos _) (shiftDetProduct_pos _)
  have hGA : G ⊆ A := by
    intro p hp
    obtain ⟨hp,hp',_⟩ := mem_filter.mp (show p∈isolatedSimplePrimes s n H Y from hp)
    exact mem_filter.mpr ⟨hp,hp'⟩
  have hsub : A \ G ⊆ M.primeFactors := by
    intro p hp
    obtain ⟨ha,hg⟩ := mem_sdiff.mp hp
    obtain ⟨hp,hval⟩ := mem_filter.mp ha
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    refine Nat.mem_primeFactors.mpr ⟨hpr,?_,hM.ne'⟩
    by_cases hh : Y<p
    · have hex : ∃ t m, (s≠t ∨ n≠m) ∧ Nat.dist n m ≤ H ∧ p ∣ t.value m := by
        by_contra! hc
        exact hg (mem_filter.mpr ⟨hp,hval,hh,hc⟩)
      obtain ⟨t,m,hsite,hgap,hdiv⟩ := hex
      exact dvd_mul_of_dvd_right (dvd_shiftDetProduct_of_shared hsite hgap hd hdiv) _
    · exact dvd_mul_of_dvd_left (hpr.dvd_primorial.trans (primorial_dvd_primorial (by omega))) _
  have hbad : (A \ G).prod id ≤ M := Nat.le_of_dvd hM
    ((Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd M))
  change A.prod id ≤ M*G.prod id
  rw [← Finset.prod_sdiff hGA]
  exact Nat.mul_le_mul_right _ hbad


private theorem value_tendsto (s : HosoyaNeighbor) : Tendsto s.value atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ))).eventually_gt_atTop (B^2)]
    with n hn
  have hh := (s.supportBounds).lower n
  by_contra! h
  have := Nat.pow_le_pow_left h.le 2
  omega

/-- The exponent-one primes unique in the window carry nearly all the value
on the logarithmic scale when the cutoff and radius satisfy the displayed budget. -/
theorem eventual_isolated_simple_product (hA : type_of% @ABC.abc) {δ : ℝ} (hδ : 0<δ)
    (s : HosoyaNeighbor) :
    ∀ᶠ n : ℕ in atTop, ∀ H Y : ℕ,
      4*(2*Y+4*(H+1)*(H+10):ℕ) ≤ δ*(n:ℝ) →
      (s.value n:ℝ)^(1-δ) < (((isolatedSimplePrimes s n H Y).prod id : ℕ):ℝ) := by
  have E := (value_tendsto s).eventually (eventual_diagonal_simple_part hA (show 0<δ/2 by positivity))
  filter_upwards [E,(value_tendsto s).eventually_gt_atTop 1] with n hs hv
  have hs' := hs (show (∃ j, s.value n=lucasFibonacciSum j) ∨ IsLowerNeighborValue (s.value n) by
    cases s
    · exact Or.inl ⟨n+2,rfl⟩
    · exact Or.inr (Or.inr ⟨n,rfl⟩))
  intro H Y hcut
  let y := s.value n
  let G := (isolatedSimplePrimes s n H Y).prod id
  let L := 2*Y+4*(H+1)*(H+10)
  have hL : (L:ℝ) ≤ n*(δ/4) := by dsimp [L]; push_cast at hcut ⊢; linarith
  have hM : primorial Y * shiftDetProduct H ≤ 2^L := by
    calc primorial Y * shiftDetProduct H ≤ 4^Y*2^((H+1)*(4*(H+10))) :=
            Nat.mul_le_mul (primorial_le_four_pow _) (shiftDetProduct_le _)
      _ = _ := by
        dsimp [L]
        rw [pow_add,pow_mul (2:ℕ) 2 Y,show (2:ℕ)^2=4 by decide,
          show (H+1)*(4*(H+10)) = 4*(H+1)*(H+10) by ring]
  have hy : 0<(y:ℝ) := by exact_mod_cast (show 0<y by omega)
  have hbudget : (2:ℝ)^(L:ℝ) ≤ (y:ℝ)^(δ/2) := by
    calc (2:ℝ)^(L:ℝ) ≤ 2^((n:ℝ)*(δ/4)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hL
      _ = ((2:ℝ)^n)^(δ/4) := by rw [Real.rpow_natCast_mul (by norm_num)]
      _ ≤ ((y:ℝ)^2)^(δ/4) := Real.rpow_le_rpow (by positivity)
            (by exact_mod_cast (s.supportBounds).lower n) (by positivity)
      _ = _ := by rw [←Real.rpow_natCast_mul hy.le]; congr 1; push_cast; ring
  have hn : simplePart y ≤ 2^L*G := (simple_part_le s n H Y).trans (Nat.mul_le_mul_right _ hM)
  have hn' : (simplePart y:ℝ) ≤ (2:ℝ)^(L:ℝ)*(G:ℝ) := by rw [Real.rpow_natCast]; exact_mod_cast hn
  have he : (y:ℝ)^(δ/2)*(y:ℝ)^(1-δ) = (y:ℝ)^(1-δ/2) := by rw [←Real.rpow_add hy]; congr 1; ring
  apply (mul_lt_mul_iff_right₀ (Real.rpow_pos_of_pos hy (δ/2))).mp
  rw [he]
  exact hs'.trans_le (hn'.trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg G)))

#print axioms eventual_isolated_simple_product


/-- Under abc, every sufficiently late site on each diagonal has a prime
greater than n/64 occurring exactly once, absent from every other site on both
diagonals within floor(sqrt(n)/16) steps. -/
theorem prime_once_on_both_diagonals (hA : type_of% @ABC.abc) :
    ∀ᶠ n : ℕ in atTop, ∀ s : HosoyaNeighbor, ∃ p : ℕ, p.Prime ∧ n/64 < p ∧
      (s.value n).factorization p=1 ∧ ∀ t m, s≠t ∨ n≠m → Nat.dist n m ≤ n.sqrt/16 →
        ¬p ∣ t.value m := by
  have h (s : HosoyaNeighbor) := eventual_isolated_simple_product hA (by norm_num : 0<(1/2:ℝ)) s
  filter_upwards [h .upper,h .lower,eventually_ge_atTop (160^2)] with n hu hl hn
  have hs : 160 ≤ n.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using hn)
  have hprod : 64*((n.sqrt/16+1)*(n.sqrt/16+10)) ≤ n := by
    calc
      64*((n.sqrt/16+1)*(n.sqrt/16+10)) ≤ (8*(n.sqrt/16+10))^2 := by
        rw [show (8*(n.sqrt/16+10))^2 = 64*((n.sqrt/16+10)*(n.sqrt/16+10)) by ring]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ ≤ n.sqrt^2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ n := Nat.sqrt_le' n
  have hY : 64*(n/64) ≤ n := by omega
  have hcut : 8*(2*(n/64)+4*(n.sqrt/16+1)*(n.sqrt/16+10)) ≤ n := by nlinarith only [hprod,hY]
  intro s
  have hx : (s.value n:ℝ)^(1-(1/2:ℝ)) <
      (((isolatedSimplePrimes s n (n.sqrt/16) (n/64)).prod id : ℕ):ℝ) := by
    have hb : 4*(2*(n/64)+4*(n.sqrt/16+1)*(n.sqrt/16+10):ℕ) ≤ (1/2:ℝ)*(n:ℝ) := by
      have he : (8:ℝ)*((2*(n/64)+4*(n.sqrt/16+1)*(n.sqrt/16+10):ℕ):ℝ) ≤ n := by exact_mod_cast hcut
      linarith
    cases s
    · exact hu _ _ hb
    · exact hl _ _ hb
  have hy : 1 ≤ s.value n := by
    by_contra! he
    have hh := (s.supportBounds).lower n
    rw [show s.value n=0 by omega] at hh
    have := Nat.one_le_two_pow (n:=n)
    omega
  have hx' := (Real.one_le_rpow (by exact_mod_cast hy : 1 ≤ (s.value n:ℝ))
    (by norm_num : 0 ≤ 1-(1/2:ℝ))).trans_lt hx
  classical
  have hne : (isolatedSimplePrimes s n (n.sqrt/16) (n/64)).Nonempty := by
    by_contra! hh
    rw [hh] at hx'
    norm_num at hx'
  obtain ⟨p,hp⟩ := hne
  obtain ⟨hm,hf,hp',hother⟩ := mem_filter.mp hp
  exact ⟨p,Nat.prime_of_mem_primeFactors hm,hp',hf,hother⟩

#print axioms prime_once_on_both_diagonals


/-- Every nonempty selection of sites in a late window has nonsquare product,
including selections using both diagonals at the same physical index. -/
theorem nonsquare_products_in_windows (hA : type_of% @ABC.abc) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Finset (HosoyaNeighbor × ℕ), T.Nonempty →
      (∀ u ∈ T, n ≤ u.2 ∧ u.2 ≤ n+n.sqrt/16) →
      ¬ IsSquare (∏ u ∈ T, u.1.value u.2) := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp (prime_once_on_both_diagonals hA)
  filter_upwards [eventually_ge_atTop N] with n hn
  intro T hT hr
  obtain ⟨⟨s,i⟩,ha⟩ := hT
  obtain ⟨hi,hi'⟩ := hr _ ha
  change n ≤ i at hi
  change i ≤ n+n.sqrt/16 at hi'
  obtain ⟨p,hp,_,hf,hisol⟩ := hN i (by omega) s
  let f (u : HosoyaNeighbor × ℕ) := u.1.value u.2
  let W := (T.erase (s,i)).prod f
  have hw : ¬p ∣ W := hp.prime.not_dvd_finsetProd fun u hu => by
    obtain ⟨hne,hu⟩ := Finset.mem_erase.mp hu
    obtain ⟨hm,hm'⟩ := hr _ hu
    apply hisol u.1 u.2
    · by_contra! heq
      exact hne (Prod.ext heq.1.symm heq.2.symm)
    · have hroot := Nat.sqrt_le_sqrt hi
      simp only [Nat.dist]
      omega
  have hwpos : W ≠ 0 := fun h => hw (h ▸ dvd_zero _)
  have hz : s.value i ≠ 0 := by intro h; simp [h] at hf
  have he := T.mul_prod_erase f ha
  change s.value i*W=T.prod f at he
  intro hsquare
  obtain ⟨b,hb⟩ := hsquare
  change T.prod f=b*b at hb
  have hh := congrArg (fun z : ℕ => z.factorization p) (he.trans hb)
  rw [← pow_two,Nat.factorization_pow,Nat.factorization_mul hz hwpos] at hh
  simp [Finsupp.add_apply,hf,Nat.factorization_eq_zero_of_not_dvd hw] at hh
  omega

#print axioms nonsquare_products_in_windows

end Arxiv.«2211.10788».HosoyaRadical
