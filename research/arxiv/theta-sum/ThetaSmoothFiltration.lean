import ThetaPrimeCoordinate

/-! Reveal complete prime-power factors in increasing prime order. -/
namespace Arxiv.«2501.03234».ThetaSmoothFiltration
open Finset
noncomputable section

def factors (P t : ℕ) := P.primeFactors.filter (·≤t)
def modulus (P t : ℕ) := ∏ q∈factors P t, q^(P.factorization q)

theorem divides {P : ℕ} (hP : 0<P) (t : ℕ) : modulus P t∣P := by
  have H := prod_dvd_prod_of_subset (factors P t) P.primeFactors (fun q => q^(P.factorization q)) (filter_subset ..)
  have he : (∏ q∈P.primeFactors,q^P.factorization q)=P := Nat.prod_factorization_pow_eq_self hP.ne'
  rwa [he] at H

theorem terminal {P t : ℕ} (hP : 0<P) (ht : P≤t) : modulus P t=P := by
  have hg : factors P t=P.primeFactors := filter_eq_self.mpr (fun q hq => (Nat.le_of_mem_primeFactors hq).trans ht)
  rw [modulus,hg]
  exact Nat.prod_factorization_pow_eq_self hP.ne'

theorem pos {P : ℕ} (hP : 0<P) (t : ℕ) : 0 < modulus P t :=
  Nat.pos_of_dvd_of_pos (divides hP t) hP

theorem next (P t : ℕ) : modulus P (t+1)=modulus P t*(t+1)^P.factorization (t+1) := by
  classical
  by_cases h : t+1∈P.primeFactors
  · have he : factors P (t+1)=insert (t+1) (factors P t) := by
      ext q
      simp only [factors,mem_filter,mem_insert]
      constructor
      · rintro ⟨hq,hl⟩
        by_cases hh : q=t+1
        · exact Or.inl hh
        · exact Or.inr ⟨hq,by omega⟩
      · rintro (rfl|⟨hq,hl⟩)
        · exact ⟨h,le_rfl⟩
        · exact ⟨hq,by omega⟩
    rw [modulus,he,prod_insert (by simp [factors]),mul_comm]
    rfl
  · have he : factors P (t+1)=factors P t := by
      ext q
      simp only [factors,mem_filter]
      constructor
      · rintro ⟨hq,hl⟩
        have hn : q≠t+1 := fun he => h (he ▸ hq)
        exact ⟨hq,by omega⟩
      · rintro ⟨hq,hl⟩;exact ⟨hq,by omega⟩
    have hz : P.factorization (t+1)=0 := by
      by_contra! hh
      exact h (Finsupp.mem_support_iff.mpr hh)
    simp [modulus,he,hz]

theorem prime_bound (P t : ℕ) : ∀ q∈(modulus P t).primeFactors, q≤t := by
  intro q hq
  have hp := Nat.prime_of_mem_primeFactors hq
  have hd := Nat.dvd_of_mem_primeFactors hq
  unfold modulus at hd
  obtain ⟨k,hk,hdiv⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  have hh := hp.dvd_of_dvd_pow hdiv
  have hp' := Nat.prime_of_mem_primeFactors (mem_filter.mp hk).1
  exact (Nat.prime_dvd_prime_iff_eq hp hp').mp hh ▸ (mem_filter.mp hk).2

theorem two_le {Y t : ℕ} (hY : 2≤Y) (ht : 2≤t) : 2 ≤ modulus Y.factorial t := by
  have h := (Nat.Prime.dvd_factorial Nat.prime_two).mpr hY
  have he : 2∈Y.factorial.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h,Nat.factorial_ne_zero _⟩
  have ha : Y.factorial.factorization 2≠0 := Finsupp.mem_support_iff.mp he
  have hd := dvd_pow_self 2 ha
  exact Nat.le_of_dvd (pos (Nat.factorial_pos _) _) (hd.trans
    (dvd_prod_of_mem (fun q => q^Y.factorial.factorization q) (mem_filter.mpr ⟨he,ht⟩)))

#print axioms next
#print axioms prime_bound
end
end Arxiv.«2501.03234».ThetaSmoothFiltration
