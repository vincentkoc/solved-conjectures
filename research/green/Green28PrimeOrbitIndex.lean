import Green28PrimitiveSupport
import Mathlib.Combinatorics.Colex

/-! Odd-characteristic root-order obstructions for uniform independent integer sums. -/

namespace Green28PrimeOrbitIndex

open Polynomial Finset

/-- The base-`p` integer having ones at the places in `U`. -/
def digitSum (p : ℕ) (U : Finset ℕ) : ℕ := ∑ i ∈ U, p^i

/-- The residue modulo the base reads off the units digit. -/
theorem digitSum_residue (p : ℕ) (U : Finset ℕ) :
    (digitSum p U:ZMod p) = if 0 ∈ U then 1 else 0 := by
  classical
  simp only [digitSum,Nat.cast_sum,Nat.cast_pow,ZMod.natCast_self]
  by_cases zero : 0 ∈ U
  · rw [if_pos zero,sum_eq_single_of_mem 0 zero]
    · simp
    · intro i _ ne
      exact zero_pow ne
  · rw [if_neg zero]
    apply sum_eq_zero
    exact fun i hi => zero_pow (fun eq => zero (eq ▸ hi))

/-- If a positive proper selection gives the `j`th multiple of the root
order, either `j` or its complement in the index is a multiple of the base. -/
theorem index_residue {p d n c j : ℕ} (hd : 0 < d) (index : n*c = digitSum p (range d))
    (U : Finset ℕ) (sel : digitSum p U = n*j) :
    (j:ZMod p) = if 0 ∈ U then c else 0 := by
  have full : (digitSum p (range d):ZMod p) = 1 := by
    rw [digitSum_residue,if_pos (mem_range.mpr hd)]
  have ident : digitSum p U*c = digitSum p (range d)*j := by rw [sel,←index];ring
  have cast := congrArg (fun z:ℕ=>(z:ZMod p)) ident
  push_cast at cast
  rw [full,one_mul,digitSum_residue] at cast
  split at cast <;> simp_all

/-- If the root index is at most the characteristic, no nonempty proper
selection of places has a sum divisible by the root order. -/
theorem no_small_index_selection {p d n c : ℕ} (hp : 1 < p) (hd : 0 < d)
    (index : n*c = digitSum p (range d)) (small : c ≤ p)
    {U : Finset ℕ} (sub : U ⊂ range d) (live : U.Nonempty) : ¬n ∣ digitSum p U := by
  rintro ⟨j,hj⟩
  have pos : 0 < digitSum p U := sum_pos (fun i _ => pow_pos (by omega) i) live
  obtain ⟨i,hi,out⟩ := Finset.not_subset.mp sub.2
  have lt : digitSum p U < digitSum p (range d) := Finset.sum_lt_sum_of_subset sub.1 hi out
    (pow_pos (by omega) i) (fun _ _ _ => Nat.zero_le _)
  rw [hj,←index] at lt
  have hlt : j < c := lt_of_mul_lt_mul_left' lt
  have jp : j < p := by omega
  have nz : 0 < j := by by_contra! h; simp [show j = 0 by omega,hj] at pos
  have val := index_residue hd index U hj
  by_cases included : 0 ∈ U
  · rw [if_pos included] at val
    have h := (ZMod.natCast_eq_natCast_iff j c p).mp val
    by_cases eq : c = p
    · rw [eq,ZMod.natCast_self] at val
      have dvd := (ZMod.natCast_eq_zero_iff j p).mp (by simpa only [Nat.cast_zero] using val)
      exact (Nat.not_le_of_lt jp) (Nat.le_of_dvd nz dvd)
    · exact (Nat.ne_of_lt hlt) (h.eq_of_lt_of_lt jp (by omega))
  · rw [if_neg included] at val
    have dvd := (ZMod.natCast_eq_zero_iff j p).mp (by simpa only [Nat.cast_zero] using val)
    exact (Nat.not_le_of_lt jp) (Nat.le_of_dvd nz dvd)

private theorem only_positive_multiple {p a : ℕ} (ha : 0 < a) (small : a < 2*p) (multiple : p ∣ a) :
    a = p := by
  obtain ⟨b,rfl⟩ := multiple
  have pos : 0 < p := Nat.pos_of_mul_pos_right ha
  have low : b ≠ 0 := by rintro rfl; simp at ha
  have high : b < 2 := by
    by_contra! h
    have := Nat.mul_le_mul_left p h
    omega
  rw [show b = 1 by omega,mul_one]

/-- Below twice the base there are at most two possible multiples for a
proper selection. A cyclic shift either keeps its value or complements it. -/
theorem two_index_values {p d n c j : ℕ} (hd : 0 < d) (index : n*c = digitSum p (range d))
    (U : Finset ℕ) (sel : digitSum p U = n*j) (pos : 0 < j) (lt : j < c) (small : c ≤ 2*p) :
    j = p ∨ c = j+p := by
  have e := index_residue hd index U sel
  by_cases hz : 0 ∈ U
  · rw [if_pos hz] at e
    have h := (ZMod.natCast_eq_natCast_iff j c p).mp e
    have dvd := (Nat.modEq_iff_dvd' lt.le).mp h
    have eq := only_positive_multiple (Nat.sub_pos_of_lt lt) (show c-j < 2*p by omega) dvd
    exact Or.inr (by omega)
  · rw [if_neg hz] at e
    exact Or.inl (only_positive_multiple pos (lt.trans_le small)
      ((ZMod.natCast_eq_zero_iff j p).mp (by simpa only [Nat.cast_zero] using e)))

/-- Below twice the base, a nonempty proper selection giving a multiple of
the root order has exactly half the places. -/
theorem half_of_small_index {p d n c : ℕ} (hp : 1 < p) (hd : 0 < d)
    (index : n*c = digitSum p (range d)) (small : c ≤ 2*p)
    {U : Finset ℕ} (sub : U ⊂ range d) (live : U.Nonempty) (unit : n ∣ digitSum p U) :
    2*U.card = d := by
  classical
  let L := digitSum p (range d)
  let M := p^d-1
  have geom : L*(p-1) = M := geom_sum_mul_of_one_le hp.le d
  let rot := fun i : ℕ => (1+i)%d
  let R := U.image rot
  let V := range d \ U
  have inj : Set.InjOn rot (U:Set ℕ) := by
    intro i hi j hj eq
    exact (Nat.ModEq.add_left_cancel' 1 (show 1+i ≡ 1+j [MOD d] from eq)).eq_of_lt_of_lt
      (mem_range.mp (sub.1 hi)) (mem_range.mp (sub.1 hj))
  have rc : R.card = U.card := card_image_of_injOn inj
  have vc : V.card = d-U.card := by rw [Finset.card_sdiff_of_subset sub.1,card_range]
  have cap : U.card < d := by simpa using Finset.card_lt_card sub
  have pos := card_pos.mpr live
  have rr : R ⊂ range d := by
    apply lt_of_le_of_ne _ (by intro eq;rw [eq,card_range] at rc;omega)
    intro j hj;obtain ⟨i,_,rfl⟩ := mem_image.mp hj
    exact mem_range.mpr (Nat.mod_lt _ hd)
  have weight {T : Finset ℕ} (s : T ⊂ range d) (q : T.Nonempty) :
      0 < digitSum p T ∧ digitSum p T < L := by
    obtain ⟨i,hi,out⟩ := Finset.not_subset.mp s.2
    exact ⟨sum_pos (fun j _ => pow_pos (by omega) j) q,
      Finset.sum_lt_sum_of_subset s.1 hi out (pow_pos (by omega) _) (fun _ _ _ => Nat.zero_le _)⟩
  obtain ⟨eu,lu⟩ := weight sub live
  obtain ⟨er,lr⟩ := weight rr (card_pos.mp (by omega))
  have per : (p:ZMod M)^d = 1 := by
    have a : M+1 = p^d := by dsimp [M];have := pow_pos (by omega : 0 < p) d;omega
    simpa using (congrArg (fun z:ℕ=>(z:ZMod M)) a).symm
  have shift (i : ℕ) : (p:ZMod M)^(rot i) = p*p^i := by
    rw [←pow_succ',Nat.add_comm i 1]
    conv_rhs => rw [←Nat.mod_add_div (1+i) d,pow_add,pow_mul,per,one_pow,mul_one]
  have moved : (digitSum p R:ZMod M) = p*(digitSum p U:ZMod M) := by
    simp only [digitSum,R,sum_image inj,Nat.cast_sum,Nat.cast_pow,mul_sum,shift]
  have hmod : digitSum p R ≡ p*digitSum p U [MOD M] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by push_cast;exact moved)
  have nM : n ∣ M := by rw [←geom,←show n*c = L from index];exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have mult : n ∣ digitSum p R := (Nat.modEq_zero_iff_dvd.mp
    ((hmod.of_dvd nM).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right unit p))))
  have changed : digitSum p R ≠ digitSum p U := by
    intro eq
    rw [eq] at hmod
    have h := (Nat.modEq_iff_dvd' (by nlinarith : digitSum p U ≤ p*digitSum p U)).mp hmod
    have pd : p*digitSum p U-digitSum p U = (p-1)*digitSum p U := by rw [Nat.sub_mul,one_mul]
    rw [pd] at h
    have low := Nat.le_of_dvd (Nat.mul_pos (by omega : 0 < p-1) eu) h
    have high := Nat.mul_lt_mul_of_pos_left lu (by omega : 0 < p-1)
    rw [←geom,mul_comm L] at low;omega
  obtain ⟨j,ju⟩ := unit
  obtain ⟨q,qr⟩ := mult
  have ix : n*c = L := index
  have jb : 0 < j ∧ j < c := by rw [ju] at eu lu;rw [←ix] at lu;exact ⟨Nat.pos_of_mul_pos_left eu,lt_of_mul_lt_mul_left' lu⟩
  have qb : 0 < q ∧ q < c := by rw [qr] at er lr;rw [←ix] at lr;exact ⟨Nat.pos_of_mul_pos_left er,lt_of_mul_lt_mul_left' lr⟩
  have distinct : q ≠ j := fun e => changed (by rw [qr,ju,e])
  have u := two_index_values hd index U ju jb.1 jb.2 small
  have r := two_index_values hd index R qr qb.1 qb.2 small
  have total : q+j = c := by omega
  have equal : digitSum p R = digitSum p V := by
    have sum := Finset.sum_sdiff (f:=fun i:ℕ=>p^i) sub.1
    change digitSum p V+digitSum p U = L at sum
    have all : digitSum p R+digitSum p U = L := by rw [qr,ju,←Nat.mul_add,total,ix]
    omega
  have same := Finset.geomSum_injective hp equal
  have := congrArg Finset.card same
  omega

open Green28PrimitiveSupport

/-- Frobenius factorization of the output mask in characteristic `p`. The
order is measured on the negative of a root, the constant of its monic
linear factor. Repeated roots are allowed. -/
def PrimeOrbit (H : ℤ[X]) (p d n : ℕ) [Fact p.Prime] : Prop :=
  ∃ β : AlgebraicClosure (ZMod p), IsPrimitiveRoot β n ∧
    H.map (Int.castRingHom (AlgebraicClosure (ZMod p))) =
      ∏ i ∈ range d, (X-C (-(β^(p^i))))

/-- One root verifies the whole orbit when its Frobenius powers have
distinct exponents modulo the signed root order. -/
theorem primeOrbit_of_root {p d n : ℕ} [Fact p.Prime] {H : ℤ[X]} (hm : H.Monic)
    (degree : H.natDegree = d) (hn : 0 < n) {β : AlgebraicClosure (ZMod p)}
    (root : H.eval₂ (Int.castRingHom _) (-β) = 0) (ord : IsPrimitiveRoot β n)
    (distinct : Function.Injective (fun i : Fin d => p^(i:ℕ)%n)) : PrimeOrbit H p d n := by
  classical
  let K := AlgebraicClosure (ZMod p)
  let r := fun i : ℕ => -(β^(p^i))
  have van (i : ℕ) : H.eval₂ (Int.castRingHom K) (r i) = 0 := by
    induction i with
    | zero => simpa [r] using root
    | succ i ih =>
      have e := H.hom_eval₂ (Int.castRingHom K) (frobenius K p) (r i)
      rw [ih,map_zero,RingHom.ext_int ((frobenius K p).comp (Int.castRingHom K)) (Int.castRingHom K)] at e
      have step : (frobenius K p) (r i) = r (i+1) := by
        dsimp only [r];rw [map_neg];change -((β^(p^i))^p) = -(β^(p^(i+1)))
        rw [pow_succ p i,pow_mul]
      rw [←step];exact e.symm
  have modpow (i : ℕ) : β^(p^i%n) = β^(p^i) := by
    rw [←IsPrimitiveRoot.iff_orderOf.mp ord];exact pow_mod_orderOf _ _
  have inj : Set.InjOn r (range d:Set ℕ) := by
    intro i hi j hj e
    have eq : β^(p^i) = β^(p^j) := neg_inj.mp e
    rw [←modpow i,←modpow j] at eq
    exact congrArg Fin.val (distinct (a₁:=⟨i,mem_range.mp hi⟩) (a₂:=⟨j,mem_range.mp hj⟩)
      (ord.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) eq))
  let T := (range d).image r
  let F := H.map (Int.castRingHom K)
  have fm : F.Monic := hm.map _
  have dvd : (∏ z ∈ T, (X-C z)) ∣ F := by
    apply (Multiset.prod_X_sub_C_dvd_iff_le_roots fm.ne_zero T.val).mpr
    apply (Multiset.le_iff_subset T.nodup).mpr
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (show z ∈ T from hz)
    exact (Polynomial.mem_roots fm.ne_zero).mpr (by simpa only [IsRoot,F,eval_map] using van i)
  have eq := Polynomial.eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic T _ (fun z _ => monic_X_sub_C z)) fm dvd
    (by rw [natDegree_finsetProd_X_sub_C_eq_card];dsimp only [T];rw [card_image_of_injOn inj,card_range];
        exact (hm.natDegree_map _).trans_le degree.le)
  exact ⟨β,ord,by simpa only [T,Finset.prod_image inj] using eq⟩

/-- A real monic factor with constant term one selects base-`p` places whose
value is divisible by the order of the signed Frobenius root. -/
theorem real_width {p d n : ℕ} [Fact p.Prime] {H : ℤ[X]} (hm : H.Monic)
    (orbit : PrimeOrbit H p d n) {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (f0 : f.coeff 0 = 1) (eq : f*g = H.map (Int.castRingHom ℝ)) :
    ∃ U ⊆ range d, U.card = f.natDegree ∧ n ∣ digitSum p U := by
  classical
  apply degrees_of_prime_reduction p H hm fm gm f0 eq (fun i _ => ∃ U ⊆ range d, U.card = i ∧ n ∣ digitSum p U)
  intro K fld cp closed F G mF mG zero product
  let _ := ZMod.algebra K p
  let emb : AlgebraicClosure (ZMod p) →ₐ[ZMod p] K := IsAlgClosed.lift
  obtain ⟨β,ord,fac⟩ := orbit
  have mapped := congrArg (Polynomial.map emb.toRingHom) fac
  simp only [Polynomial.map_map,Polynomial.map_prod,Polynomial.map_sub,map_X,map_C,
    RingHom.ext_int (emb.toRingHom.comp _) (Int.castRingHom K)] at mapped
  simp only [emb.toRingHom.map_neg,emb.toRingHom.map_pow] at mapped
  obtain ⟨U,sub,h⟩ := divisor_subproduct (fun i => -((emb β)^(p^i))) (range d) mF mG (product.trans mapped)
  have prod : (∏ i ∈ U, (emb β)^(p^i)) = 1 := by
    rw [coeff_zero_eq_eval_zero,h,eval_prod] at zero
    simpa using zero
  refine ⟨U,sub,by rw [h,natDegree_finsetProd_X_sub_C_eq_card],?_⟩
  have rootOrder : IsPrimitiveRoot (emb β) n := ord.map_of_injective emb.injective
  exact rootOrder.dvd_of_pow_eq_one _
    (by simpa only [digitSum,Finset.prod_pow_eq_pow_sum] using prod)

private theorem split_degrees {p d n : ℕ} [Fact p.Prime] {H : ℤ[X]} (hm : H.Monic)
    (orbit : PrimeOrbit H p d n) {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (eq : f*g = H.map (Int.castRingHom ℝ)) : f.natDegree+g.natDegree = d := by
  obtain ⟨β,_,prod⟩ := orbit
  rw [←natDegree_mul fm.ne_zero gm.ne_zero,eq,hm.natDegree_map,
    ←hm.natDegree_map (Int.castRingHom (AlgebraicClosure (ZMod p))),prod,natDegree_finsetProd_X_sub_C_eq_card,card_range]

/-- At index at most the characteristic the integer mask has no proper
real monic factor with constant coefficient one. -/
theorem no_real_split {p d n c : ℕ} [prime : Fact p.Prime] {H : ℤ[X]} (hm : H.Monic)
    (orbit : PrimeOrbit H p d n) (index : n*c = digitSum p (range d)) (small : c ≤ p)
    {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic) (f0 : f.coeff 0 = 1)
    (eq : f*g = H.map (Int.castRingHom ℝ)) : f.natDegree = 0 ∨ g.natDegree = 0 := by
  by_contra! h
  have deg := split_degrees hm orbit fm gm eq
  obtain ⟨U,sub,size,mul⟩ := real_width hm orbit fm gm f0 eq
  have strict : U ⊂ range d := lt_of_le_of_ne sub (by intro e;rw [e,card_range] at size;omega)
  exact no_small_index_selection prime.out.one_lt (by omega) index small strict (card_pos.mp (by omega)) mul

/-- At index at most twice the characteristic, positive-degree monic real
factors with constant coefficient one have equal widths. -/
theorem real_split_equal {p d n c : ℕ} [prime : Fact p.Prime] {H : ℤ[X]} (hm : H.Monic)
    (orbit : PrimeOrbit H p d n) (index : n*c = digitSum p (range d)) (small : c ≤ 2*p)
    {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic) (f0 : f.coeff 0 = 1)
    (eq : f*g = H.map (Int.castRingHom ℝ)) (hf : f.natDegree ≠ 0) (hg : g.natDegree ≠ 0) :
    f.natDegree = g.natDegree := by
  have deg := split_degrees hm orbit fm gm eq
  obtain ⟨U,sub,size,mul⟩ := real_width hm orbit fm gm f0 eq
  have strict : U ⊂ range d := lt_of_le_of_ne sub (by intro e;rw [e,card_range] at size;omega)
  have half := half_of_small_index prime.out.one_lt (by omega) index small strict (card_pos.mp (by omega)) mul
  omega

open Green28 Green28UniformSums

/-- The prime-index test forces a point-mass summand for the original
integer convolution. -/
theorem pure_of_prime_index {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) {p d n c : ℕ} [Fact p.Prime]
    (orbit : PrimeOrbit (outputMask S ne) p d n) (index : n*c = digitSum p (range d)) (small : c ≤ 2*p) :
    (∃ x, P = PMF.pure x) ∨ (∃ y, Q = PMF.pure y) := by
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  obtain ⟨f,g,_,_,_,_,fp,gp,fm,gm,fw,gw,fc,gc,product⟩ := mask_factorization ne sum
  by_cases hf : f.natDegree = 0
  · exact Or.inl (pure_of_width_zero pf (fw ▸ hf))
  by_cases hg : g.natDegree = 0
  · exact Or.inr (pure_of_width_zero qf (gw ▸ hg))
  have mon := monic_of_injective Int.cast_injective (product ▸ fm.mul gm)
  have bin := ((fp.mul gp).uniform_iff (fm.mul gm)).mp flat
  exact False.elim ((Green28AlgebraicWidth.unequal_widths fm gm fp.nonneg gp.nonneg fc gc bin
    (Nat.pos_of_ne_zero hf)) (real_split_equal mon orbit index small fm gm fc product hf hg))

/-- Green 28 holds under the output-mask index condition, independently of
support sizes, multiplicities, and the real marginal probabilities. -/
theorem uniform_of_prime_index {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) {p d n c : ℕ} [Fact p.Prime]
    (orbit : PrimeOrbit (outputMask S ne) p d n) (index : n*c = digitSum p (range d)) (small : c ≤ 2*p) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q :=
  uniform_of_pure_factor ⟨S,ne,sum⟩ (pure_of_prime_index ne sum orbit index small)

#print axioms digitSum_residue
#print axioms index_residue
#print axioms no_small_index_selection
#print axioms two_index_values
#print axioms half_of_small_index
#print axioms real_width
#print axioms no_real_split
#print axioms real_split_equal
#print axioms pure_of_prime_index
#print axioms uniform_of_prime_index
#print axioms primeOrbit_of_root
end Green28PrimeOrbitIndex
