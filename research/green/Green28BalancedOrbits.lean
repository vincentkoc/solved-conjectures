import Green28PrimitiveSupport
import Mathlib.Combinatorics.Colex

/-! Binary Frobenius orbits and the widths of independent summands in Green 28. -/

namespace Green28BalancedOrbits

open Finset Polynomial Green28PrimitiveSupport

/-- The integer encoded by a set of binary places. -/
def bits (U : Finset ℕ) : ℕ := ∑ i ∈ U, 2^i

private theorem bits_range (d : ℕ) : bits (range d)+1 = 2^d := by
  induction d with
  | zero => simp [bits]
  | succ d ih => simp only [bits, sum_range_succ] at *; rw [pow_succ]; omega

private theorem bits_lt {U : Finset ℕ} {d : ℕ} (sub : U ⊂ range d) :
    bits U < 2^d-1 := by
  obtain ⟨j,hj,out⟩ := Finset.not_subset.mp sub.2
  have lt := Finset.sum_lt_sum_of_subset (f:=fun i:ℕ=>2^i) sub.1 hj out (by positivity)
    (fun _ _ _ => Nat.zero_le _)
  change bits U < bits (range d) at lt
  have h := bits_range d
  omega

/-- Suppose a word selects a nonempty proper subset of the `d` binary places
and its value is a multiple of `n`. If the index of `n` in `2^d-1` divides
`2^k+1`, exactly half the places are selected. -/
theorem balanced_places {d n c k : ℕ} (hd : 0 < d) (index : n*c = 2^d-1)
    (negative : c ∣ 2^k+1) {U : Finset ℕ} (sub : U ⊂ range d) (live : U.Nonempty)
    (unit : n ∣ bits U) : 2*U.card = d := by
  classical
  let M := 2^d-1
  let rot := fun i : ℕ => (k+i)%d
  let R := U.image rot
  let V := range d \ U
  have inj : Set.InjOn rot (U:Set ℕ) := by
    intro i hi j hj eq
    have h : k+i ≡ k+j [MOD d] := eq
    exact (Nat.ModEq.add_left_cancel' k h).eq_of_lt_of_lt (mem_range.mp (sub.1 hi)) (mem_range.mp (sub.1 hj))
  have rc : R.card = U.card := card_image_of_injOn inj
  have vc : V.card = d-U.card := by rw [Finset.card_sdiff_of_subset sub.1,card_range]
  have cap : U.card < d := by simpa using Finset.card_lt_card sub
  have pos := Finset.card_pos.mpr live
  have rr : R ⊆ range d := by
    intro j hj
    obtain ⟨i,_,rfl⟩ := mem_image.mp hj
    exact mem_range.mpr (Nat.mod_lt _ hd)
  have vr : V ⊆ range d := Finset.sdiff_subset
  have bound (T : Finset ℕ) (inR : T ⊆ range d) (size : T.card < d) : bits T < M := by
    apply bits_lt (lt_of_le_of_ne inR ?_)
    intro eq; rw [eq,card_range] at size; omega
  have rv := bound R rr (by omega)
  have vv := bound V vr (by omega)
  have tot : bits V+bits U = M := by
    have e := Finset.sum_sdiff (f:=fun i:ℕ=>2^i) sub.1
    change bits V+bits U = bits (range d) at e
    have b := bits_range d
    dsimp [M]; omega
  have period : (2:ZMod M)^d = 1 := by
    have a : M+1 = 2^d := by dsimp [M]; have := Nat.two_pow_pos d; omega
    have b := congrArg (fun z:ℕ=>(z:ZMod M)) a
    simpa using b.symm
  have shift (i : ℕ) : (2:ZMod M)^(rot i) = 2^k*2^i := by
    rw [←pow_add]
    conv_rhs => rw [←Nat.mod_add_div (k+i) d, pow_add,pow_mul,period,one_pow,mul_one]
  have br : (bits R:ZMod M) = 2^k*(bits U:ZMod M) := by
    simp only [bits,R,sum_image inj,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat,mul_sum,shift]
  have dv : M ∣ (2^k+1)*bits U := by
    dsimp only [M]
    rw [←index]; simpa [mul_comm] using Nat.mul_dvd_mul negative unit
  have cz := (ZMod.natCast_eq_zero_iff _ M).mpr dv
  have ct := congrArg (fun z:ℕ=>(z:ZMod M)) tot
  push_cast at cz ct
  have eq : (bits R:ZMod M) = (bits V:ZMod M) := by
    rw [br]
    have zero : (M:ZMod M) = 0 := ZMod.natCast_self M
    rw [zero] at ct
    linear_combination cz-ct
  have val := (ZMod.natCast_eq_natCast_iff _ _ _).mp eq
  have same := Finset.geomSum_injective (by decide : 2 ≤ 2) (show bits R = bits V from val.eq_of_lt_of_lt rv vv)
  have h := congrArg Finset.card same
  omega

/-- A unit constant coefficient selects a binary multiple of the Frobenius
root order. Its number of digits equal to one is the factor degree. -/
theorem divisor_width {K : Type*} [Field K] [CharP K 2] {α : K} {n d : ℕ}
    (order : IsPrimitiveRoot α n) {f g : K[X]} (fm : f.Monic) (gm : g.Monic)
    (f0 : f.coeff 0 = 1) (eq : f*g = ∏ i ∈ range d, (X-C (α^(2^i)))) :
    ∃ U ⊆ range d, U.card = f.natDegree ∧ n ∣ bits U := by
  classical
  obtain ⟨U,sub,h⟩ := divisor_subproduct (fun i => α^(2^i)) (range d) fm gm eq
  have prod : (∏ i ∈ U, α^(2^i)) = 1 := by
    rw [coeff_zero_eq_eval_zero,h,eval_prod] at f0
    simpa [CharTwo.neg_eq] using f0
  refine ⟨U,sub,by rw [h,natDegree_finsetProd_X_sub_C_eq_card],?_⟩
  exact order.dvd_of_pow_eq_one _ (by simpa only [bits,Finset.prod_pow_eq_pow_sum] using prod)

private theorem degree_alternative {a b d n c k : ℕ} (deg : a+b = d) (index : n*c = 2^d-1)
    (negative : c ∣ 2^k+1) (places : ∃ U ⊆ range d, U.card = a ∧ n ∣ bits U) : a = 0 ∨ b = 0 ∨ a = b := by
  by_cases ha : a = 0
  · exact Or.inl ha
  by_cases hb : b = 0
  · exact Or.inr (Or.inl hb)
  obtain ⟨U,sub,size,mul⟩ := places
  have strict : U ⊂ range d := lt_of_le_of_ne sub (by intro h; rw [h,card_range] at size; omega)
  have half := balanced_places (by omega : 0 < d) index negative strict (Finset.card_pos.mp (by omega)) mul
  exact Or.inr (Or.inr (by omega))

/-- The binary mask has the listed Frobenius factors, with multiplicity, and
the chosen root has multiplicative order `n`. -/
def BinaryOrbit (H : ℤ[X]) (d n : ℕ) : Prop :=
  ∃ α : GaloisField 2 d, IsPrimitiveRoot α n ∧
    H.map (Int.castRingHom (GaloisField 2 d)) = ∏ i ∈ range d, (X-C (α^(2^i)))

/-- The width of a monic real factor with constant term one must equal the
number of occupied binary places in a multiple of the root order. -/
theorem real_divisor_width {H : ℤ[X]} (hm : H.Monic) {d n : ℕ} (orbit : BinaryOrbit H d n)
    {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic) (f0 : f.coeff 0 = 1)
    (eq : f*g = H.map (Int.castRingHom ℝ)) :
    ∃ U ⊆ range d, U.card = f.natDegree ∧ n ∣ bits U := by
  classical
  apply degrees_of_binary_reduction H hm fm gm f0 eq (fun i _ => ∃ U ⊆ range d, U.card = i ∧ n ∣ bits U)
  intro K fld cp closed F G mF mG zero product
  let _ := ZMod.algebra K 2
  let emb : GaloisField 2 d →ₐ[ZMod 2] K := IsAlgClosed.lift
  obtain ⟨α,ord,factor⟩ := orbit
  have mapped := congrArg (Polynomial.map emb.toRingHom) factor
  simp only [Polynomial.map_map,Polynomial.map_prod,Polynomial.map_sub,map_X,map_C,
    RingHom.ext_int (emb.toRingHom.comp _) (Int.castRingHom K)] at mapped
  simp only [emb.toRingHom.map_pow] at mapped
  exact divisor_width (ord.map_of_injective emb.injective) mF mG zero (product.trans mapped)

/-- Under the semiprimitive index condition a proper real split has equal widths. -/
theorem degrees_of_real_split {H : ℤ[X]} (hm : H.Monic) {d n c k : ℕ}
    (orbit : BinaryOrbit H d n) (index : n*c = 2^d-1) (negative : c ∣ 2^k+1)
    {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic) (f0 : f.coeff 0 = 1)
    (eq : f*g = H.map (Int.castRingHom ℝ)) :
    f.natDegree = 0 ∨ g.natDegree = 0 ∨ f.natDegree = g.natDegree := by
  apply degree_alternative _ index negative (real_divisor_width hm orbit fm gm f0 eq)
  obtain ⟨α,_,prod⟩ := orbit
  rw [←natDegree_mul fm.ne_zero gm.ne_zero,eq,hm.natDegree_map,
    ←hm.natDegree_map (Int.castRingHom (GaloisField 2 d)),prod,natDegree_finsetProd_X_sub_C_eq_card,card_range]

open Green28 Green28UniformSums

/-- A balanced binary orbit for the uniform output forces a point mass on at
least one side, regardless of the signs of algebraic conjugates of the input weights. -/
theorem pure_factor_of_balanced_orbit {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) {d n c k : ℕ}
    (orbit : BinaryOrbit (outputMask S ne) d n) (index : n*c = 2^d-1) (negative : c ∣ 2^k+1) :
    (∃ x, P = PMF.pure x) ∨ (∃ y, Q = PMF.pure y) := by
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  obtain ⟨f,g,_,_,_,_,fp,gp,fm,gm,fw,gw,fc,gc,product⟩ := mask_factorization ne sum
  have mon := monic_of_injective Int.cast_injective (product ▸ fm.mul gm)
  have bin := ((fp.mul gp).uniform_iff (fm.mul gm)).mp flat
  rcases degrees_of_real_split mon orbit index negative fm gm fc product with h|h|h
  · exact Or.inl (pure_of_width_zero pf (fw ▸ h))
  · exact Or.inr (pure_of_width_zero qf (gw ▸ h))
  · by_cases zero : f.natDegree = 0
    · exact Or.inl (pure_of_width_zero pf (fw ▸ zero))
    · exact False.elim (Green28AlgebraicWidth.unequal_widths fm gm fp.nonneg gp.nonneg fc gc bin
        (Nat.pos_of_ne_zero zero) h)

/-- Green 28 holds for uniform outputs with a balanced binary orbit. -/
theorem uniform_of_balanced_orbit {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) {d n c k : ℕ}
    (orbit : BinaryOrbit (outputMask S ne) d n) (index : n*c = 2^d-1) (negative : c ∣ 2^k+1) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q :=
  uniform_of_pure_factor ⟨S,ne,sum⟩ (pure_factor_of_balanced_orbit ne sum orbit index negative)

/-- Every divisor of the multiplicative group order gives a binary orbit mask
of the specified width. -/
theorem exists_index_mask {d n c : ℕ} (hd : 0 < d) (index : n*c = 2^d-1) :
    ∃ (S : Finset ℤ) (ne : S.Nonempty), S.min' ne = 0 ∧ (outputMask S ne).natDegree = d ∧
      BinaryOrbit (outputMask S ne) d n := by
  classical
  let K := GaloisField 2 d
  let _ : NeZero d := ⟨hd.ne'⟩
  obtain ⟨u,hu⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := Kˣ)).mp inferInstance
  have ord : IsPrimitiveRoot (u:K) (2^d-1) := IsPrimitiveRoot.iff_orderOf.mpr (by
    rw [show orderOf (u:K) = orderOf u from orderOf_units,hu,Nat.card_units,GaloisField.card 2 d hd.ne'])
  have pos : 0 < 2^d-1 := by have := Nat.one_lt_two_pow hd.ne'; omega
  have alpha := IsPrimitiveRoot.pow pos ord (show 2^d-1 = c*n by rw [mul_comm,index])
  have pw := alpha.pow_eq_one
  have pow : ((u:K)^c)^(2^d-1) = 1 := by rw [←index,pow_mul,pw,one_pow]
  obtain ⟨S,ne,least,deg,rep⟩ := exists_orbit_support d hd _ pow
  exact ⟨S,ne,least,deg,_,alpha,rep⟩

/-- A smaller root order for the full orbit rules out a primitive reduction,
even if the factors in the orbit repeat. -/
theorem not_primitive_of_order {H : ℤ[X]} {d n : ℕ} (width : H.natDegree = d)
    (orbit : BinaryOrbit H d n) (pos : 0 < n) (small : n < 2^d-1) : ¬PrimitiveBinary H := by
  classical
  intro prim
  unfold PrimitiveBinary at prim
  rw [width] at prim
  obtain ⟨_,β,root,big⟩ := prim
  obtain ⟨α,ord,prod⟩ := orbit
  rw [←eval_map,prod,eval_prod] at root
  obtain ⟨i,_,zero⟩ := Finset.prod_eq_zero_iff.mp root
  have eq : β = α^(2^i) := sub_eq_zero.mp (by simpa using zero)
  have exp : β^n = 1 := by rw [eq,←pow_mul,mul_comm,pow_mul,ord.pow_eq_one,one_pow]
  exact (Nat.not_le_of_lt small) (Nat.le_of_dvd pos (big.dvd_of_pow_eq_one n exp))

/-- Every positive even width has an index-three orbit mask to which the
point-mass theorem applies, beyond the primitive case. -/
theorem exists_index_three (t : ℕ) (ht : 0 < t) :
    ∃ (S : Finset ℤ) (ne : S.Nonempty) (n : ℕ), S.min' ne = 0 ∧
      (outputMask S ne).natDegree = 2*t ∧ n*3 = 2^(2*t)-1 ∧
      BinaryOrbit (outputMask S ne) (2*t) n ∧ ¬PrimitiveBinary (outputMask S ne) := by
  have pos : 1 < 2^(2*t) := Nat.one_lt_two_pow (by omega)
  have mod : 4^t ≡ 1 [MOD 3] := by simpa using (show 4 ≡ 1 [MOD 3] by decide).pow t
  have dvd : 3 ∣ 2^(2*t)-1 := by
    rw [pow_mul,show (2:ℕ)^2 = 4 by decide]
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow t 4 (by decide))).mp mod.symm
  obtain ⟨n,h⟩ := dvd
  have idx : n*3 = 2^(2*t)-1 := by omega
  obtain ⟨S,ne,least,deg,orb⟩ := exists_index_mask (by omega) idx
  exact ⟨S,ne,n,least,deg,idx,orb,not_primitive_of_order deg orb (by omega) (by omega)⟩

/-- A uniform law with no decomposition into two nonconstant integer laws
exists at every positive even width outside the primitive-mask class. -/
theorem exists_indecomposable_nonprimitive (t : ℕ) (ht : 0 < t) :
    ∃ (S : Finset ℤ) (ne : S.Nonempty), S.min' ne = 0 ∧ (outputMask S ne).natDegree = 2*t ∧
      ¬PrimitiveBinary (outputMask S ne) ∧ ∀ P Q : PMF ℤ, indepSum P Q = PMF.uniformOfFinset S ne →
        (∃ x, P = PMF.pure x) ∨ (∃ y, Q = PMF.pure y) := by
  obtain ⟨S,ne,n,least,degree,index,orbit,nonprim⟩ := exists_index_three t ht
  exact ⟨S,ne,least,degree,nonprim,fun _ _ sum =>
    pure_factor_of_balanced_orbit ne sum orbit index (show 3 ∣ 2^1+1 by decide)⟩

#print axioms balanced_places
#print axioms divisor_width
#print axioms real_divisor_width
#print axioms degrees_of_real_split
#print axioms pure_factor_of_balanced_orbit
#print axioms uniform_of_balanced_orbit
#print axioms exists_index_mask
#print axioms not_primitive_of_order
#print axioms exists_index_three
#print axioms exists_indecomposable_nonprimitive
end Green28BalancedOrbits
