import research.arxiv.«1104.1579».CunninghamSelbergSieve

/-! Uniform estimates for square divisors of Cunningham terms at prime seeds. -/

namespace CunninghamChain
open Finset

/-- Uniform prime upper bound in any progression whose step is a prime square. -/
theorem prime_square_progression_sieve {q z N : ℕ} (hq : q.Prime) (a : ℕ)
    (hz : 1<z) (hy : z^16 ≤ N) :
    (((range N).filter fun n => z < q^2*n+a ∧ (q^2*n+a).Prime).card : ℝ)*
      Real.log ((z:ℝ)+1) ≤ 24*N := by
  classical
  let E := z.primesLE ∩ {2,q}
  let R (ℓ : ℕ) : Finset (ZMod ℓ) := {- (a:ZMod ℓ)*((q:ZMod ℓ)^2)⁻¹}
  let A := (range N).filter fun n => z < q^2*n+a ∧ (q^2*n+a).Prime
  have exc {ℓ : ℕ} (hℓ : ℓ ∈ z.primesLE \ E) : ℓ.Prime ∧ ℓ≠2 ∧ ℓ≠q := by
    obtain ⟨hp,he⟩ := mem_sdiff.mp hℓ
    refine ⟨Nat.prime_of_mem_primesLE hp,?_,?_⟩
    · rintro rfl
      exact he (mem_inter.mpr ⟨hp,by simp⟩)
    · rintro rfl
      exact he (mem_inter.mpr ⟨hp,by simp⟩)
  have h := finite_residue_sieve_bound E R A (k:=1) (by decide) hz inter_subset_left
    (fun ℓ hℓ => ⟨by have hh := (exc hℓ).1.two_le; have := (exc hℓ).2.1; omega,card_singleton _⟩)
    (filter_subset ..) (by
      intro n hn ℓ hℓ he
      obtain ⟨_,hz₁,hp⟩ := mem_filter.mp hn
      have hlp := (exc hℓ).1
      let : Fact ℓ.Prime := ⟨hlp⟩
      have hq₀ : (q:ZMod ℓ) ≠ 0 :=
        (ZMod.natCast_eq_zero_iff ..).not.mpr ((Nat.prime_dvd_prime_iff_eq hlp hq).not.mpr (exc hℓ).2.2)
      have hv : ((q^2*n+a:ℕ):ZMod ℓ)=0 := by
        push_cast
        rw [show (n:ZMod ℓ)= - (a:ZMod ℓ)*((q:ZMod ℓ)^2)⁻¹ from mem_singleton.mp he]
        field_simp
        ring
      have heq := (Nat.prime_dvd_prime_iff_eq hlp hp).mp ((ZMod.natCast_eq_zero_iff ..).mp hv)
      have := Nat.le_of_mem_primesLE (mem_sdiff.mp hℓ).1
      omega) (by simpa [←pow_mul] using hy)
  have hE : E.card ≤ 2 :=
    (card_le_card (show E ⊆ {2,q} from inter_subset_right)).trans (card_insert_le .. |>.trans (by simp))
  have hprod : (∏ ℓ ∈ E, (1-1/(ℓ:ℝ))⁻¹) ≤ 4 := by
    calc
      _ ≤ ∏ _ ∈ E, (2:ℝ) := by
        apply prod_le_prod
        · intro ℓ hℓ
          have : (2:ℝ) ≤ ℓ := by exact_mod_cast (Nat.prime_of_mem_primesLE (mem_inter.mp hℓ).1).two_le
          exact inv_nonneg.mpr (sub_nonneg.mpr (by apply (div_le_iff₀ (by positivity)).mpr; linarith))
        · intro ℓ hℓ
          have hl : (2:ℝ) ≤ ℓ := by exact_mod_cast (Nat.prime_of_mem_primesLE (mem_inter.mp hℓ).1).two_le
          have hh : 1/(ℓ:ℝ) ≤ 1/2 := by apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr; linarith
          rw [inv_eq_one_div,div_le_iff₀ (by linarith)]
          linarith
      _ = 2^E.card := prod_const ..
      _ ≤ (2:ℝ)^2 := pow_le_pow_right₀ (by norm_num) hE
      _ = 4 := by norm_num
  simp only [pow_one] at h
  exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg (α:=ℝ) N)])

#print axioms prime_square_progression_sieve

/-- Count primes in a specified residue class modulo q² inside an initial interval. -/
theorem prime_square_residue_sieve {q z X : ℕ} (hq : q.Prime) (a : ℕ)
    (hz : 1<z) (hy : z^16 ≤ X/q^2+1) :
    (((range X).filter fun p => z<p ∧ p.Prime ∧ p%q^2=a).card : ℝ)*
      Real.log ((z:ℝ)+1) ≤ 24*(X/q^2+1:ℕ) := by
  classical
  let A := (range X).filter fun p => z<p ∧ p.Prime ∧ p%q^2=a
  let B := (range (X/q^2+1)).filter fun n => z<q^2*n+a ∧ (q^2*n+a).Prime
  have split {p : ℕ} (hp : p ∈ A) : q^2*(p/q^2)+a=p := by
    rw [←(mem_filter.mp hp).2.2.2,add_comm,Nat.mod_add_div]
  have hc : A.card ≤ B.card := by
    apply card_le_card_of_injOn (fun p => p/q^2)
    · intro p hp
      have hr := mem_range.mp (mem_filter.mp hp).1
      have hle : p/q^2 ≤ X/q^2 := Nat.div_le_div_right hr.le
      change p/q^2 ∈ B
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hle),by
        rw [split hp]; exact ⟨(mem_filter.mp hp).2.1,(mem_filter.mp hp).2.2.1⟩⟩
    · intro p hp s hs h
      change p/q^2=s/q^2 at h
      rw [←split hp,←split hs,h]
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc : (A.card:ℝ)≤B.card)
    (Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) z; linarith))).trans (prime_square_progression_sieve hq a hz hy)

#print axioms prime_square_residue_sieve

end CunninghamChain
