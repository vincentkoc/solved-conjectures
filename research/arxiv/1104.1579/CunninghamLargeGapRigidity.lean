import CunninghamEndpointWeights

/-! The factor-reversal argument for a large gap with one irreducible endpoint. -/

namespace CunninghamChain.LargeGap
open Polynomial CoefficientEnergy Finset

private lemma cut_mul (A B : ℤ[X]) (m : ℕ) :
    cut (cut A m*cut B m) m=cut (A*B) m := by
  simp only [cut,Polynomial.coe_mul,PowerSeries.trunc_trunc_mul_trunc]

private lemma unit_ends (P Q c : ℤ[X]) (eq : P*Q=c) (hu : IsUnit P) :
    ∃ s : ℤ, s^2=1 ∧ P=C s ∧ Q=C s*c := by
  let s := P.coeff 0
  have he : P=C s := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hu)
  have hs : IsUnit s := isUnit_C.mp (he ▸ hu)
  have sq : s^2=1 := by rcases Int.isUnit_iff.mp hs with h|h <;> rw [h] <;> decide
  refine ⟨s,sq,he,?_⟩
  rw [←eq,he,←mul_assoc,←map_mul,←pow_two,sq,map_one,one_mul]

private lemma match_ends (G c : ℤ[X]) {N m : ℕ} (dc : c.natDegree < m)
    (bound : c.natDegree+m ≤ N) (dg : G.natDegree ≤ N)
    (weight : energy G (N+1)=energy (separated c N) (N+1)) {s : ℤ}
    (hs : s^2=1) (low : cut G m=C s) (high : cut (reflect N G) m=C s*c) :
    G=C s*separated c N := by
  have df := separated_degree c (by omega : c.natDegree ≤ N)
  have cs : s≠0 := by intro no; simp [no] at hs
  apply fixed_energy_agreement _ _ (by rw [natDegree_C_mul cs]; exact df) dg
  · rw [energy_scale,hs,one_mul,weight]
  intro i hi nz
  by_cases zero : i=0
  · subst i
    have at0 := congrArg (fun P : ℤ[X] => P.coeff 0) low
    have dm : c.natDegree < N := by omega
    simpa [cut_coeff,show 0 < m by omega,separated,coeff_add,coeff_reflect,
      coeff_eq_zero_of_natDegree_lt dm] using at0
  have fi : (separated c N).coeff i=c.coeff (N-i) := by simp [separated,coeff_one,zero,revAt_le hi]
  have nz' : c.coeff (N-i)≠0 := by
    intro no
    simp [fi,no] at nz
  have sm := (le_natDegree_of_ne_zero nz').trans_lt dc
  have top := congrArg (fun P : ℤ[X] => P.coeff (N-i)) high
  simp only [cut_coeff,if_pos sm,coeff_reflect,revAt_le (by omega : N-i ≤ N),
    Nat.sub_sub_self hi,coeff_C_mul] at top
  simpa only [coeff_C_mul,fi] using top

/-- A degree threshold depending only on the short endpoint, with a dyadic
interval for each possible unit increment in the two truncation weights. -/
def gapThreshold (c : ℤ[X]) : ℕ :=
  2*((c.natDegree+1)*2^(2*(1+energy c (c.natDegree+1)).toNat+1))

/-- For an irreducible integral endpoint c, any polynomial with the same
reflected product as 1+reflect N c equals that polynomial or its reflection
up to sign once N reaches the stated threshold. -/
theorem large_gap_rigidity (G c : ℤ[X]) {N : ℕ} (irr : Irreducible c)
    (large : gapThreshold c ≤ N) (dg : G.natDegree ≤ N)
    (prod : G*reflect N G=separated c N*reflect N (separated c N)) :
    ∃ s : ℤ, s^2=1 ∧ (G=C s*separated c N ∨ reflect N G=C s*separated c N) := by
  let d := c.natDegree+1
  let W := 1+energy c d
  let w := 2*W.toNat
  let B := d*2^(w+1)
  let F := separated c N
  change 2*B ≤ N at large
  have db : d ≤ B := Nat.le_mul_of_pos_right _ (by positivity)
  have dc : c.natDegree < N := by dsimp only [d] at db; omega
  have gweight : energy G (N+1)=energy F (N+1) := by
    rw [←coeff_mul_self_reflect,←coeff_mul_self_reflect,prod]
  have fw : energy F (N+1)=W := separated_energy c dc
  have Wpos : 0 ≤ W := by dsimp [W]; linarith [energy_nonneg c d]
  have budget : energy G B+energy (reflect N G) B ≤ (w:ℤ) := by
    have l := energy_mono G (by omega : B ≤ N+1)
    have r := energy_mono (reflect N G) (by omega : B ≤ N+1)
    rw [reflect_energy] at r
    dsimp [w]
    rw [Int.toNat_of_nonneg Wpos]
    linarith
  obtain ⟨m,hm,mb,lo⟩ := common_dyadic_gap G (reflect N G) d w budget
  change 2*m ≤ B at mb
  have dm : c.natDegree < m := by dsimp [d] at hm; omega
  have lm : c.natDegree+2*m ≤ N := by dsimp [d] at db; omega
  obtain ⟨f₀,f₁⟩ := separated_low c (m:=2*m) (by omega) lm
  have entry : cut (G*reflect N G) (2*m)=c := by
    rw [prod,←cut_mul,f₀,f₁,one_mul]
    exact PowerSeries.trunc_coe_eq_self (by omega)
  have exactprod : cut G m*cut (reflect N G) m=c := by
    apply exact_low_product _ _ _ (by omega) (by omega) (fun i h l => (lo i h l).1)
      (fun i h l => (lo i h l).2)
    intro i hi
    simpa [cut_coeff,hi] using congrArg (fun P : ℤ[X] => P.coeff i) entry
  rcases irr.isUnit_or_isUnit exactprod.symm with hu|hu
  · obtain ⟨s,hs,hl,hh⟩ := unit_ends _ _ _ exactprod hu
    exact ⟨s,hs,Or.inl (match_ends G c dm (by omega) dg gweight hs hl hh)⟩
  · obtain ⟨s,hs,hl,hh⟩ := unit_ends _ _ _ ((mul_comm ..).trans exactprod) hu
    refine ⟨s,hs,Or.inr (match_ends (reflect N G) c dm (by omega)
      (natDegree_reflect_le.trans (max_le le_rfl dg)) ?_ hs hl ?_)⟩
    · rwa [reflect_energy]
    · simpa using hh

#print axioms large_gap_rigidity

end CunninghamChain.LargeGap
