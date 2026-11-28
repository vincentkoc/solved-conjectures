import Green28CoprimeOrbitFactors
import Green28TernaryExample

/-! A sixteen-site uniform law with a unique nonconstant decomposition up to translation and exchange. -/

namespace Green28CoprimeOrbitExample
open Finset Polynomial Green28 Green28UniformSums Green28PrimitiveSupport
open Green28TernaryExample Green28PrimeOrbitIndex Green28CoprimeOrbitFactors

namespace Left

/-- The integer mask of a four-site summand. -/
noncomputable def mask : ℤ[X] := X^14+X^2+X+1

private def relation : Word := [0,0,0,0,0,0,0,0,0,0,0,2,1,2]

theorem mon : mask.Monic := by
  have deg : mask.natDegree = 14 := by unfold mask;compute_degree!
  rw [Monic,leadingCoeff,deg]
  norm_num [mask,coeff_X_pow,coeff_X,coeff_one]

private theorem value_one {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) :
    value x (unpack relation.length 1) = 1 := by
  change value x ([0,0,0,0,0,0,0,0,0,0,0,0,0,1]:Word) = 1
  simp [value]

private theorem value_x {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) :
    value x (unpack relation.length 3) = x := by
  change value x ([0,0,0,0,0,0,0,0,0,0,0,0,1,0]:Word) = x
  simp [value]

set_option maxHeartbeats 3000000 in
private theorem signed_order {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K)
    (root : x^relation.length = value x relation) : IsPrimitiveRoot x 2391484 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · have h := checked_power relation x (value_x x) root 2391484 1
      [2,2987446,2616302,4511633,224617,3200187,4023766,
        1357364,2194313,4478506,2834615,80355,3799070,4412992,
        1417248,734832,1863,19683,81,9,3] (by decide +kernel)
    rw [←h,value_one]
  · intro q prime dvd
    have mem := Nat.mem_primeFactors.mpr ⟨prime,dvd,(by decide : (2391484:ℕ) ≠ 0)⟩
    have factors : (2391484:ℕ).primeFactors = {2,547,1093} := by decide +kernel
    simp only [factors,Finset.mem_insert,Finset.mem_singleton] at mem
    rcases mem with rfl|rfl|rfl
    · have h := checked_power relation x (value_x x) root 1195742 2
        [2987446,2616302,4511633,224617,3200187,4023766,1357364,
        2194313,4478506,2834615,80355,3799070,4412992,1417248,
        734832,1863,19683,81,9,3] (by decide +kernel)
      exact h ▸ checked_ne_one relation x (value_one x) root (w:=2) (v:=1) (by decide +kernel)
    · have h := checked_power relation x (value_x x) root 4372 1662874
        [4247192,2220326,3792110,1084728,123911,3737591,81648,
        621,6561,81,9,3] (by decide +kernel)
      exact h ▸ checked_ne_one relation x (value_one x) root (w:=1662874) (v:=2900621) (by decide +kernel)
    · have h := checked_power relation x (value_x x) root 2188 4743962
        [1877996,1810399,1084728,123911,3737591,81648,621,
        6561,81,9,3] (by decide +kernel)
      exact h ▸ checked_ne_one relation x (value_one x) root (w:=4743962) (v:=2809227) (by decide +kernel)

/-- The signed root has the full norm-one order at the prime three. -/
theorem orbit : PrimeOrbit mask 3 14 2391484 := by
  classical
  let K := AlgebraicClosure (ZMod 3)
  let M := mask.map (Int.castRingHom K)
  have deg : mask.natDegree = 14 := by unfold mask;compute_degree!
  have degM : M.natDegree = 14 := (mon.natDegree_map _).trans deg
  obtain ⟨a,z⟩ := IsAlgClosed.exists_root M (ne_of_gt (natDegree_pos_iff_degree_pos.mp (by omega)))
  let x := -a
  have r : mask.eval₂ (Int.castRingHom K) (-x) = 0 := by
    rw [show -x = a from neg_neg a,←eval_map];exact z
  have relation_x : x^relation.length = value x relation := by
    have e := r
    simp only [mask,eval₂_add,eval₂_pow,eval₂_X,eval₂_one] at e
    have three : (3:K) = 0 := CharP.cast_eq_zero K 3
    have two : algebraMap (ZMod 3) K (2:ZMod 3) = (2:K) := map_ofNat _ 2
    simp [relation,value,two]
    linear_combination e-(1+x^2)*three
  apply primeOrbit_of_root mon deg (by decide) r (signed_order x relation_x)
  decide +kernel

end Left

namespace Right

/-- The integer mask of a four-site summand. -/
noncomputable def mask : ℤ[X] := X^11+X^7+X^3+1

private def relation : Word := [0,0,0,2,0,0,0,2,0,0,1]

theorem mon : mask.Monic := by
  have deg : mask.natDegree = 11 := by unfold mask;compute_degree!
  rw [Monic,leadingCoeff,deg]
  norm_num [mask,coeff_X_pow,coeff_X,coeff_one]

private theorem value_one {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) :
    value x (unpack relation.length 1) = 1 := by
  change value x ([0,0,0,0,0,0,0,0,0,0,1]:Word) = 1
  simp [value]

private theorem value_x {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) :
    value x (unpack relation.length 3) = x := by
  change value x ([0,0,0,0,0,0,0,0,0,1,0]:Word) = x
  simp [value]

set_option maxHeartbeats 3000000 in
private theorem signed_order {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K)
    (root : x^relation.length = value x relation) : IsPrimitiveRoot x 88573 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · have h := checked_power relation x (value_x x) root 88573 1
      [249,163477,51165,34852,52338,4618,141279,
        24197,10224,37008,101094,80190,59049,243,
        9,3] (by decide +kernel)
    rw [←h,value_one]
  · intro q prime dvd
    have mem := Nat.mem_primeFactors.mpr ⟨prime,dvd,(by decide : (88573:ℕ) ≠ 0)⟩
    have factors : (88573:ℕ).primeFactors = {23,3851} := by decide +kernel
    simp only [factors,Finset.mem_insert,Finset.mem_singleton] at mem
    rcases mem with rfl|rfl
    · have h := checked_power relation x (value_x x) root 3851 5275
        [37547,65988,70683,138074,90263,19779,11773,
        110,2187,27,3] (by decide +kernel)
      exact h ▸ checked_ne_one relation x (value_one x) root (w:=5275) (v:=25516) (by decide +kernel)
    · have h := checked_power relation x (value_x x) root 23 11155
        [4429,243,9,3] (by decide +kernel)
      exact h ▸ checked_ne_one relation x (value_one x) root (w:=11155) (v:=157806) (by decide +kernel)

/-- The signed root has the full norm-one order at the prime three. -/
theorem orbit : PrimeOrbit mask 3 11 88573 := by
  classical
  let K := AlgebraicClosure (ZMod 3)
  let M := mask.map (Int.castRingHom K)
  have deg : mask.natDegree = 11 := by unfold mask;compute_degree!
  have degM : M.natDegree = 11 := (mon.natDegree_map _).trans deg
  obtain ⟨a,z⟩ := IsAlgClosed.exists_root M (ne_of_gt (natDegree_pos_iff_degree_pos.mp (by omega)))
  let x := -a
  have r : mask.eval₂ (Int.castRingHom K) (-x) = 0 := by
    rw [show -x = a from neg_neg a,←eval_map];exact z
  have relation_x : x^relation.length = value x relation := by
    have e := r
    simp only [mask,eval₂_add,eval₂_pow,eval₂_X,eval₂_one] at e
    have three : (3:K) = 0 := CharP.cast_eq_zero K 3
    have two : algebraMap (ZMod 3) K (2:ZMod 3) = (2:K) := map_ofNat _ 2
    simp [relation,value,two]
    linear_combination -e-(x^3+x^7)*three
  apply primeOrbit_of_root mon deg (by decide) r (signed_order x relation_x)
  decide +kernel

end Right

/-- The sixteen distinct sums of the two four-site supports. -/
def sites : Finset ℤ := {0,1,2,3,4,5,7,8,9,11,12,13,14,17,21,25}

private theorem present : (0:ℤ) ∈ sites := by decide

/-- The two possible nonconstant marginal masks, indexed by a Boolean. -/
noncomputable def component (b : Bool) : ℤ[X] := if b then Right.mask else Left.mask
private def width (b : Bool) := if b then 11 else 14
private def rootOrder (b : Bool) := if b then 88573 else 2391484

private theorem mask_eq : outputMask sites ⟨0,present⟩ = ∏ b, component b := by
  have least : sites.min' ⟨0,present⟩ = 0 := by
    apply le_antisymm (Finset.min'_le _ _ present)
    apply Finset.le_min'
    intro j hj
    simp only [sites,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  unfold outputMask
  rw [least]
  have img : sites.image (fun z => (z-0).toNat) = ({0,1,2,3,4,5,7,8,9,11,12,13,14,17,21,25}:Finset ℕ) := by decide +kernel
  rw [img,Fintype.prod_bool]
  simp (disch := decide) only [Finset.sum_insert,Finset.sum_singleton,←C_mul_X_pow_eq_monomial,map_one,one_mul,pow_zero,pow_one]
  simp only [component,Bool.false_eq_true,if_false,if_true,Left.mask,Right.mask]
  ring

/-- The supports give a direct sum. Every displayed outcome occurs exactly once. -/
theorem one_representation : ∀ z ∈ sites,
    (({0,1,2,14}:Finset ℤ).filter fun a => z-a ∈ ({0,3,7,11}:Finset ℤ)).card = 1 := by
  decide +kernel

/-- Every independent decomposition partitions the two certified masks,
and both marginal laws are uniform on their own supports. -/
theorem classify_sixteen_sites {P Q : PMF ℤ} (sum : indepSum P Q = PMF.uniformOfFinset sites ⟨0,present⟩) :
    ∃ (I : Finset Bool) (a b : ℤ) (s t : ℝ),
      Models P ((∏ i ∈ I, component i).map (Int.castRingHom ℝ)) a s ∧
      Models Q ((∏ i ∈ univ \ I, component i).map (Int.castRingHom ℝ)) b t ∧
      IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  apply marginal_subproducts ⟨0,present⟩ sum component width rootOrder (fun _ => 1) mask_eq (p:=3)
  · intro b; cases b
    · exact Left.mon
    · exact Right.mon
  · intro b; cases b
    · exact Left.orbit
    · exact Right.orbit
  · decide +kernel
  · decide
  · intro i j neq; cases i <;> cases j <;> first | contradiction | decide +kernel

def leftSites : Finset ℤ := {0,1,2,14}
def rightSites : Finset ℤ := {0,3,7,11}

private theorem left_ne : leftSites.Nonempty := by decide
private theorem right_ne : rightSites.Nonempty := by decide
private theorem sites_ne : sites.Nonempty := ⟨0,present⟩

open scoped ENNReal

/-- Independent fair laws on the two four-site supports realize the observed
uniform law on all sixteen sites. -/
theorem realized :
    indepSum (PMF.uniformOfFinset leftSites left_ne) (PMF.uniformOfFinset rightSites right_ne) =
      PMF.uniformOfFinset sites sites_ne := by
  classical
  have l : leftSites.Nonempty := by decide
  have r : rightSites.Nonempty := by decide
  have cardL : leftSites.card = 4 := by decide
  have cardR : rightSites.card = 4 := by decide
  have cardS : sites.card = 16 := by decide
  have sums : ∀ a ∈ leftSites, ∀ b ∈ rightSites, a+b ∈ sites := by decide +kernel
  apply PMF.ext
  intro z
  rw [Green28UniformSums.convolution]
  by_cases hz : z ∈ sites
  · obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (one_representation z hz)
    change leftSites.filter (fun v => z-v ∈ rightSites) = {a} at ha
    have hmem : a ∈ leftSites.filter (fun v => z-v ∈ rightSites) := ha ▸ mem_singleton_self a
    rw [tsum_eq_single a]
    · rw [PMF.uniformOfFinset_apply_of_mem l (mem_filter.mp hmem).1,
        PMF.uniformOfFinset_apply_of_mem r (mem_filter.mp hmem).2,PMF.uniformOfFinset_apply_of_mem sites_ne hz,
        cardL,cardR,cardS]
      norm_num [←ENNReal.mul_inv]
    · intro v ne
      by_cases hv : v ∈ leftSites
      · have out : z-v ∉ rightSites := fun yes => ne (mem_singleton.mp (ha ▸ mem_filter.mpr ⟨hv,yes⟩))
        simp [PMF.uniformOfFinset_apply_of_notMem r out]
      · simp [PMF.uniformOfFinset_apply_of_notMem l hv]
  · rw [PMF.uniformOfFinset_apply_of_notMem sites_ne hz,ENNReal.tsum_eq_zero]
    intro v
    by_cases hv : v ∈ leftSites
    · have out : z-v ∉ rightSites := fun yes => hz (by simpa using sums v hv (z-v) yes)
      simp [PMF.uniformOfFinset_apply_of_notMem r out]
    · simp [PMF.uniformOfFinset_apply_of_notMem l hv]

#print axioms realized
#print axioms one_representation
#print axioms classify_sixteen_sites
#print axioms Left.orbit
#print axioms Right.orbit
end Green28CoprimeOrbitExample
