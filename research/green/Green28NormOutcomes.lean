import Green28PencilNorm
import Green28ThreeLevelPartner

/-! Divisibility of the number of output sites for a single deficient atom. -/

namespace Green28NormOutcomes

open Polynomial Finset Green28 Green28UniformSums Green28AlgebraicWidth Green28UnpairedSites
  Green28DeficientFibre Green28ThreeLevelPartner
open scoped ENNReal Polynomial

/-- Specializing the generator of an integral polynomial order at an integer
gives a divisibility test for rational integers divisible by the linear factor. -/
theorem specialize_linear {x v : ℝ} {q N : ℤ} (int : IsIntegral ℤ x)
    (mem : v ∈ Algebra.adjoin ℤ {x}) (eq : ((q:ℝ)-x)*v = (N:ℝ)) :
    (minpoly ℤ x).eval q ∣ N := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at mem
  obtain ⟨p,hp⟩ := mem
  change aeval x p = v at hp
  let f : ℤ[X] := (C q-X)*p-C N
  have zero : aeval x f = 0 := by simp only [f,map_sub,map_mul,aeval_C,aeval_X,hp]; exact sub_eq_zero.mpr eq
  have d := eval_dvd (x := q) (minpoly.isIntegrallyClosed_dvd int zero)
  simpa [f] using d

private theorem total {P : PMF ℤ} (finite : P.support.Finite) (a : ℤ) :
    (∑ i ∈ finite.toFinset,weight P a i) = 1/(P a).toReal := by
  have eq := congrArg ENNReal.toReal P.tsum_coe
  have off (i : ℤ) (hi : i ∉ finite.toFinset) : P i = 0 :=
    (P.apply_eq_zero_iff _).mpr (fun h => hi (finite.mem_toFinset.mpr h))
  rw [tsum_eq_sum off,ENNReal.toReal_sum (fun i _ => P.apply_ne_top i),ENNReal.toReal_one] at eq
  simp only [weight,←sum_div,eq]

private theorem peak {P Q : PMF ℤ} {S : Finset ℤ} (sn : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S sn) (pf : P.support.Finite)
    {a b : ℤ} (pa : IsGreatest P.support a) (qb : IsGreatest Q.support b) :
    (P a).toReal*(Q b).toReal*(S.card:ℝ) = 1 := by
  have occ : a+b ∈ (indepSum P Q).support := (PMF.mem_support_bind_iff _ _ _).mpr ⟨a,pa.1,
    (PMF.mem_support_bind_iff _ _ _).mpr ⟨b,qb.1,(PMF.mem_support_pure_iff _ _).mpr rfl⟩⟩
  rw [sum,PMF.support_uniformOfFinset] at occ
  have eq := sum_coeff P Q (a+b) pf
  rw [sum,PMF.uniformOfFinset_apply_of_mem sn occ,sum_eq_single a] at eq
  · simp only [add_sub_cancel_left,ENNReal.toReal_inv,ENNReal.toReal_natCast] at eq
    rw [←eq,inv_mul_cancel₀ (by exact_mod_cast sn.card_pos.ne')]
  · intro i hi ne
    have le := pa.2 (pf.mem_toFinset.mp hi)
    have off : a+b-i ∉ Q.support := fun h => by have := qb.2 h; omega
    simp [(Q.apply_eq_zero_iff _).mpr off]
  · exact fun h => (h (pf.mem_toFinset.mpr pa.1)).elim

/-- In any nonuniform example with one deficient atom of normalized weight
`u` and exceptional-side cardinality `q`, the minimal polynomial of `1-u`
evaluated at `q` divides the actual number of sum outcomes. -/
theorem outcome_count {P Q : PMF ℤ} {S : Finset ℤ} (sn : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S sn) (one : OneDeficit Q)
    (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q)) (w : Boundary P Q) :
    (minpoly ℤ (1-weight Q w.b w.d)).eval (Q.support.ncard:ℤ) ∣ (S.card:ℤ) := by
  classical
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,sn,sum⟩
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  let u := weight Q w.b w.d
  let x := 1-u
  have comp : u = 1-x := by dsimp [x]; ring
  have ap := ENNReal.toReal_pos ((P.mem_support_iff _).mp w.topP.1) (P.apply_ne_top _)
  have bp := ENNReal.toReal_pos ((Q.mem_support_iff _).mp w.topQ.1) (Q.apply_ne_top _)
  obtain ⟨pa,hpa,ptop,prows⟩ := (endpoint_weights flat).1
  obtain rfl := w.topP.unique (show IsGreatest P.support pa from ⟨hpa,ptop⟩)
  obtain ⟨qb,hqb,qtop,qrows⟩ := (endpoint_weights flat).2
  have eb := w.topQ.unique (show IsGreatest Q.support qb from ⟨hqb,qtop⟩)
  have uint : IsIntegral ℤ u := by change IsIntegral ℤ ((Q w.d).toReal/(Q w.b).toReal); rw [eb]; exact (qrows w.d).2.2.1
  let R := Algebra.adjoin ℤ ({x}:Set ℝ)
  have inc : Algebra.adjoin ℤ ({u}:Set ℝ) ≤ R := Algebra.adjoin_le (by
    intro z hz; obtain rfl : z = u := hz
    rw [comp]; exact R.sub_mem R.one_mem (Algebra.subset_adjoin (Set.mem_singleton x)))
  let v := ∑ i ∈ pf.toFinset,weight P w.a i
  have vr : v ∈ R := by
    apply R.sum_mem
    intro i hi
    by_cases eq : (P i).toReal = (P w.a).toReal
    · rw [weight,eq,div_self ap.ne']; exact R.one_mem
    · have lt : (P i).toReal<(P w.a).toReal := lt_of_le_of_ne (by
        have le := (prows i).2.1
        simpa only [one_mul] using (div_le_iff₀ ap).mp le) eq
      have mem : weight P w.a i ∈ Submodule.span ℤ (deficientWeights P w.a) :=
        Submodule.subset_span ⟨i,pf.mem_toFinset.mp hi,lt,rfl⟩
      rw [deficient_integer_span flat one bad w] at mem
      exact inc mem
  let B := qf.toFinset
  have eqcard : B.card = Q.support.ncard := (Set.ncard_eq_toFinset_card _ _).symm
  have dm : w.d ∈ B := qf.mem_toFinset.mpr w.lowQ
  have qsum : (∑ j ∈ B,weight Q w.b j) = (Q.support.ncard:ℝ)-x := by
    rw [←sum_erase_add _ _ dm]
    have eq : (∑ j ∈ B.erase w.d,weight Q w.b j) = (B.erase w.d).card • (1:ℝ) := by
      apply sum_eq_card_nsmul
      intro j hj
      obtain ⟨ne,mem⟩ := mem_erase.mp hj
      rw [weight,w.other _ (qf.mem_toFinset.mp mem) ne,div_self bp.ne']
    have z : ((B.erase w.d).card:ℝ)+1 = Q.support.ncard := by
      exact_mod_cast (card_erase_add_one dm).trans eqcard
    rw [eq,nsmul_eq_mul,mul_one]
    change _+u = _
    linarith only [z,comp]
  have vp : v = 1/(P w.a).toReal := total pf _
  have vq := total qf w.b
  rw [qsum] at vq
  have mass := peak sn sum pf w.topP w.topQ
  apply specialize_linear (x := x) (v := v) (isIntegral_one.sub uint) vr
  push_cast
  rw [vp,vq]
  field_simp
  linarith only [mass]

private theorem quad_min {x : ℝ} (xp : 0 < x) (xl : x < 1) {k : ℕ}
    (quad : x^2-(k+1)*x+1 = 0) :
    minpoly ℤ x = (X^2-C ((k:ℤ)+1)*X+1:ℤ[X]) := by
  let f : ℤ[X] := X^2-C ((k:ℤ)+1)*X+1
  have deg : f.natDegree = 2 := by dsimp [f]; compute_degree!
  have mon : f.Monic := by
    change f.coeff f.natDegree = 1
    rw [deg]; simp [f,coeff_X_pow,coeff_one]
  have ann : aeval x f = 0 := by
    simp only [f,map_add,map_sub,map_pow,map_one,map_mul,aeval_X,aeval_C]
    simpa only [map_natCast] using quad
  have int : IsIntegral ℤ x := ⟨f,mon,ann⟩
  have irr : x ∉ (algebraMap ℤ ℝ).range := by
    rintro ⟨z,eq⟩
    change (z:ℝ) = x at eq
    have p : (0:ℤ) < z := by exact_mod_cast xp.trans_eq eq.symm
    have l : z<(1:ℤ) := by exact_mod_cast eq.trans_lt xl
    omega
  have two := (minpoly.two_le_natDegree_iff int).mpr irr
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic int) mon
    (minpoly.isIntegrallyClosed_dvd int ann) (deg ▸ two)).symm

private theorem count_flanks {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {w : Boundary P Q} (d : ThreeLevelData P Q w) : 2*d.k+1 ≤ Q.support.ncard := by
  classical
  have qf := (finite_of_uniform_sum flat).2
  let L := qf.toFinset.filter fun j => j < w.d
  let R := qf.toFinset.filter fun j => w.d < j
  have dis : Disjoint L R := disjoint_left.mpr (fun {_} l r => (mem_filter.mp l).2.not_gt (mem_filter.mp r).2)
  have off : w.d ∉ L∪R := by simp [L,R]
  have inc : insert w.d (L∪R) ⊆ qf.toFinset := insert_subset (qf.mem_toFinset.mpr w.lowQ)
    (union_subset (filter_subset _ _) (filter_subset _ _))
  have size := card_le_card inc
  rw [card_insert_of_notMem off,card_union_of_disjoint dis,←Set.ncard_eq_toFinset_card Q.support qf] at size
  have lc : (Q.support ∩ Set.Iio w.d).ncard = L.card := by
    rw [←Set.ncard_coe_finset]; congr 1; ext; simp [L]
  have rc : (Q.support ∩ Set.Ioi w.d).ncard = R.card := by
    rw [←Set.ncard_coe_finset]; congr 1; ext; simp [R]
  obtain ⟨l,r⟩ := flank_sizes flat d
  rw [lc] at l; rw [rc] at r; omega

/-- With at most three opposite masses, a nonuniform example needs an
explicit divisor of its number of output sites. Here `q` is the number of
atoms in the law with the single deficient site. -/
theorem three_level_count {P Q : PMF ℤ} {S : Finset ℤ} (sn : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S sn) (one : OneDeficit Q) (three : massLevels P ≤ 3)
    (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q)) :
    let q := Q.support.ncard
    ∃ k : ℕ, 2 ≤ k ∧ 2*k+1 ≤ q ∧ q*(q-(k+1))+1 ∣ S.card := by
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,sn,sum⟩
  obtain ⟨w⟩ := boundary_of_one_deficit flat one bad
  obtain ⟨h⟩ := three_level_data flat one bad three w
  have half := count_flanks flat h
  refine ⟨h.k,h.two,half,?_⟩
  have count := outcome_count sn sum one bad w
  have x := h.complement
  have wpos := ENNReal.toReal_pos ((Q.mem_support_iff _).mp w.lowQ) (Q.apply_ne_top _)
  have bpos := ENNReal.toReal_pos ((Q.mem_support_iff _).mp w.topQ.1) (Q.apply_ne_top _)
  have pos : 0 < weight Q w.b w.d := div_pos wpos bpos
  have lt : weight Q w.b w.d < 1 := (div_lt_one bpos).mpr w.deficient
  rw [show 1-weight Q w.b w.d = h.x by linarith only [x],
    quad_min (by linarith only [x,lt]) (by linarith only [x,pos]) h.quadratic] at count
  simp only [eval_add,eval_sub,eval_pow,eval_X,eval_C,eval_mul,eval_one] at count
  have hk : h.k+1 ≤ Q.support.ncard := by omega
  apply Int.natCast_dvd_natCast.mp
  push_cast [Nat.cast_sub hk]
  convert count using 1; ring

/-- Uniformity follows whenever the number of outcomes divides a power
of the exceptional marginal's support size. -/
theorem uniform_of_card_dvd_power {P Q : PMF ℤ} {S : Finset ℤ} (sn : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S sn) (one : OneDeficit Q) (three : massLevels P ≤ 3)
    (n : ℕ) (power : S.card ∣ Q.support.ncard^n) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  by_contra bad
  obtain ⟨k,hk,flank,counts⟩ := three_level_count sn sum one three bad
  let q := Q.support.ncard
  let b := q-(k+1)
  have cop : Nat.Coprime (q*b+1) q := by
    rw [Nat.coprime_comm,show q*b+1 = 1+b*q by ring,Nat.coprime_add_mul_right_right]
    exact Nat.coprime_one_right _
  have unit := (cop.pow_right n).eq_one_of_dvd (counts.trans power)
  have qp : 0 < q := by change 0 < Q.support.ncard; omega
  have bp : 0 < b := by dsimp [b,q]; omega
  have pos := Nat.mul_pos qp bp
  omega

/-- A size occurs when it is the actual output cardinality of a failure with
the stated support size, a single deficient atom and a three-level partner. -/
def Occurs (q M : ℕ) : Prop :=
  ∃ (P Q : PMF ℤ) (S : Finset ℤ) (sn : S.Nonempty),
    Q.support.ncard = q ∧ S.card = M ∧ indepSum P Q = PMF.uniformOfFinset S sn ∧
    OneDeficit Q ∧ massLevels P ≤ 3 ∧ ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q)

/-- Among the first `N` positive integers, at most `N/q` can occur
as output sizes for this entire class at exceptional-side cardinality `q`. -/
theorem sparse_outcome_sizes (q N : ℕ) (T : Finset ℕ)
    (bounded : ∀ M ∈ T, M ≤ N) (occurs : ∀ M ∈ T, Occurs q M) : q*T.card ≤ N := by
  classical
  let L := (q-1)/2
  let D := q*L+1
  let U := (Icc 1 L) ×ˢ (Icc 1 (N/D))
  let recover (p : ℕ×ℕ) := (q*(q-(p.1+1))+1)*p.2
  have sub : T ⊆ U.image recover := by
    intro M hm
    obtain ⟨P,Q,S,sn,eq,sz,sum,one,three,bad⟩ := occurs M hm
    obtain ⟨k,small,flank,div⟩ := three_level_count sn sum one three bad
    rw [eq] at flank div
    rw [sz] at div
    obtain ⟨t,ht⟩ := div
    have mpos : 0 < M := sz ▸ sn.card_pos
    have tp : 0 < t := by
      by_contra! z
      have tz : t = 0 := by omega
      rw [tz,mul_zero] at ht
      omega
    have low : D ≤ q*(q-(k+1))+1 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      dsimp [L]; omega
    have limit : t ≤ N/D := by
      apply (Nat.le_div_iff_mul_le (by dsimp [D]; omega)).mpr
      rw [mul_comm]
      exact (Nat.mul_le_mul_right _ low).trans (ht ▸ bounded _ hm)
    refine mem_image.mpr ⟨(k,t),mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,by dsimp [L]; omega⟩,
      mem_Icc.mpr ⟨tp,limit⟩⟩,ht.symm⟩
  have card : T.card ≤ L*(N/D) := by
    simpa only [U,card_product,Nat.card_Icc,Nat.add_sub_cancel] using (card_le_card sub).trans card_image_le
  calc
    q*T.card ≤ q*(L*(N/D)) := Nat.mul_le_mul_left _ card
    _ = (q*L)*(N/D) := (Nat.mul_assoc ..).symm
    _ ≤ D*(N/D) := Nat.mul_le_mul_right _ (Nat.le_succ _)
    _ ≤ N := Nat.mul_div_le _ _

#print axioms specialize_linear
#print axioms outcome_count
#print axioms three_level_count
#print axioms uniform_of_card_dvd_power
#print axioms sparse_outcome_sizes
end Green28NormOutcomes
