import ThetaDirichletEuler

/-! Reindex the conductor rows by multiples of the primitive period. -/
namespace Arxiv.«2501.03234».ThetaDirichletEuler
open Finset Filter Topology Complex ThetaDirichletRows ThetaDirichletMeans
open ThetaJacobiRows (sieve)
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

private theorem pf_partition {n : ℕ} (hn : n≠0) :
    (q*n).primeFactors=q.primeFactors ∪ sieve q n := by
  rw [Nat.primeFactors_mul (NeZero.ne q) hn]
  ext p
  simp only [mem_union,sieve,mem_filter]
  by_cases hp : p∈n.primeFactors
  · have h := Nat.prime_of_mem_primeFactors hp
    simp only [Nat.mem_primeFactors_of_ne_zero (NeZero.ne q),h,true_and,hp,true_and,or_true,true_iff,h.coprime_iff_not_dvd]
    exact or_not
  · simp [hp]

private lemma sieve_scaled {n : ℕ} (hn : n≠0) : sieve q (q*n)=sieve q n := by
  unfold sieve
  rw [Nat.primeFactors_mul (NeZero.ne q) hn,filter_union]
  have he : q.primeFactors.filter (·.Coprime q)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p h
    obtain ⟨hp,hc⟩ := mem_filter.mp h
    exact ((Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp hc) (Nat.dvd_of_mem_primeFactors hp)
  rw [he,empty_union]

private theorem totient_scaled {n : ℕ} (hn : n≠0) :
    ((q*n).totient:ℂ)=(q.totient:ℂ)*n*∏ p∈sieve q n,(1-(p:ℂ)⁻¹) := by
  have ht (k : ℕ) : (k.totient:ℂ)=k*∏ p∈k.primeFactors,(1-(p:ℂ)⁻¹) := by
    have H := congrArg (fun z : ℚ => (z:ℂ)) (Nat.totient_eq_mul_prod_factors k)
    push_cast at H
    exact H
  have dis : Disjoint q.primeFactors (sieve q n) := by
    apply disjoint_left.mpr
    intro p hp h
    exact ((Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp (mem_filter.mp h).2) (Nat.dvd_of_mem_primeFactors hp)
  rw [ht (q*n),ht q,pf_partition hn,prod_union dis,Nat.cast_mul]; ring

omit [NeZero q] in
private lemma weight_factors {n : ℕ} (ho : Odd n) :
    (∏ p∈n.primeFactors,factor χ p)*(∏ p∈sieve q n,(1-(p:ℂ)⁻¹))=
    (∏ p∈sieve q n,(1-symbol χ⁻¹ p))*(∏ p∈sieve q n,(1-symbol χ p/p)) := by
  have he : ∏ p∈n.primeFactors,factor χ p=∏ p∈sieve q n,factor χ p := by
    rw [sieve,prod_filter]
    apply prod_congr rfl
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have h2 : p≠2 := fun h => (by have H := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)); omega)
    split_ifs with hc
    · rfl
    · simp [factor,h2,not_not.mp (mt hpr.coprime_iff_not_dvd.mpr hc)]
  rw [he,←prod_mul_distrib,←prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have h2 : p≠2 := fun h => (by have H := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)); omega)
  have hn : ¬p∣q := hpr.coprime_iff_not_dvd.mp (mem_filter.mp hp).2
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hpr.ne_zero
  have hp1 : (p:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast hpr.ne_one)
  simp only [factor,if_neg h2,if_neg hn,ofReal_div,ofReal_sub,ofReal_natCast,ofReal_one]
  field_simp

/-- The conductor-independent part of the scaled row coefficient. -/
noncomputable def initial (A : ℂ) : ℂ := A*(1-symbol χ 2/2)/((q:ℂ)*q.totient)

theorem coeff_multiple (ho : Odd q) (A : ℂ) (n : ℕ) :
    rowCoeff χ A (q*n)=initial χ A*weight χ n := by
  by_cases hn : n=0
  · simp [hn,weight,rowCoeff]
  have hdiv := Nat.dvd_mul_right q n
  by_cases hodd : Odd n
  · have h2 : 2∉sieve q n := fun h =>
      (by have H := Nat.odd_iff.mp (hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors (mem_filter.mp h).1)); omega)
    have hφ : (((q*n).totient):ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (NeZero.pos q) (Nat.pos_of_ne_zero hn))).ne'
    have hφq : (q.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
    have hq0 : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
    have hn0 : (n:ℂ)≠0 := by exact_mod_cast hn
    rw [rowCoeff,if_pos ⟨ho.mul hodd,hdiv⟩,sieve_scaled hn,prod_insert h2,initial,weight,div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero (by exact_mod_cast Nat.mul_ne_zero (NeZero.ne q) hn) hφ)
        (mul_ne_zero (mul_ne_zero hq0 hφq) (pow_ne_zero _ hn0)),totient_scaled hn,Nat.cast_mul]
    linear_combination -(A*(1-symbol χ 2/2)*(q:ℂ)*q.totient*(n:ℂ)^2)*(weight_factors χ hodd)
  · have h2 : 2∈n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide,by have := Nat.odd_iff.not.mp hodd; omega,hn⟩
    have hno : ¬Odd (q*n) := fun h => hodd (h.of_dvd_nat (Nat.dvd_mul_left n q))
    simp [rowCoeff,hno,weight,prod_eq_zero h2 (by simp [factor] : factor χ 2=0)]

theorem coeff_hasSum (ho : Odd q) (A : ℂ) :
    HasSum (rowCoeff χ A) (initial χ A*∑' n,weight χ n) := by
  have hs := (summable_weight χ).of_norm.hasSum.mul_left (initial χ A)
  have hi : Function.Injective (fun n : ℕ => q*n) := fun _ _ h => Nat.eq_of_mul_eq_mul_left (NeZero.pos q) h
  apply (hi.hasSum_iff _).mp
  · simpa only [Function.comp_def,coeff_multiple χ ho] using hs
  · rintro d hd
    have hdiv : ¬q∣d := fun ⟨j,hj⟩ => hd ⟨j,hj.symm⟩
    simp [rowCoeff,hdiv]

#print axioms coeff_multiple
#print axioms coeff_hasSum
end Arxiv.«2501.03234».ThetaDirichletEuler
