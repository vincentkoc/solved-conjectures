import Green28PrimeFactors
import Green28ReversalField

/-!
# Two-homogeneous Galois groups in Green 28

A rational constant coefficient fixes the logarithmic sum of a divisor under
all conjugations. On an orbit transitive on unordered pairs, the associated
Gram matrix forces uniform multiplicities when the moduli vary. This yields
a Green 28 criterion on the output mask, with arbitrary cyclotomic padding.
See Zheng, *Computing the Exponent Lattice of Generic Polynomial Roots*,
Theorem 3.2, for the general exponent-lattice theorem.
-/

namespace Green28GaloisOrbits
open Finset Polynomial
open scoped Polynomial

/-- A nonconstant real vector separates all nonconstant weights under a
transitive group that is transitive on unordered pairs of distinct points.
The off-diagonal entries of its orbit Gram matrix are all equal. -/
theorem constant_weights {G X : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]
    (trans : ∀ x y : X, ∃ g : G, g • x = y)
    (pairs : ∀ a b x y : X, a ≠ b → x ≠ y → ∃ g : G,
      (g • a = x ∧ g • b = y) ∨ (g • a = y ∧ g • b = x))
    (u w : X → ℝ) (varies : ∃ a b, u a ≠ u b) {c : ℝ}
    (fixed : ∀ g : G, ∑ x, w x*u (g • x) = c) : ∀ x y, w x = w y := by
  classical
  obtain ⟨a,b,diff⟩ := varies
  have ab : a ≠ b := fun e => diff (e ▸ rfl)
  let gram (x y : X) := ∑ g : G, u (g • x)*u (g • y)
  let A := gram a a
  let B := gram a b
  have inv (g : G) (x y : X) : gram (g • x) (g • y) = gram x y := by
    apply Fintype.sum_equiv (Equiv.mulRight g)
    intro h; simp [mul_smul]
  have diag (x : X) : gram x x = A := by
    obtain ⟨g,rfl⟩ := trans a x
    exact inv g a a
  have off (x y : X) (ne : x ≠ y) : gram x y = B := by
    obtain ⟨g,h⟩ := pairs a b x y ab ne
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact inv g a b
    · exact (inv g b a).trans (by simp only [gram,B,mul_comm])
  have gap : A ≠ B := by
    intro eq
    have pos : 0<∑ g : G, (u (g • a)-u (g • b))^2 :=
      sum_pos' (fun _ _ => sq_nonneg _) ⟨1,mem_univ _,by simpa using sq_pos_of_ne_zero (sub_ne_zero.mpr diff)⟩
    have sq : (∑ g : G, (u (g • a)-u (g • b))^2) = gram a a+gram b b-2*gram a b := by
      simp only [gram,mul_sum,←sum_add_distrib,←sum_sub_distrib]
      apply sum_congr rfl
      intro g _; ring
    rw [sq,diag a,diag b,off a b ab,eq] at pos
    linarith
  have lin (y : X) : (∑ x, w x)*B+w y*(A-B) = c*∑ g : G, u (g • y) := by
    calc
      _ = ∑ x, w x * gram x y := by
        rw [←sum_erase_add univ w (mem_univ y),←sum_erase_add univ (fun x => w x*gram x y) (mem_univ y),diag]
        have eq : (∑ x ∈ univ.erase y, w x*gram x y) = (∑ x ∈ univ.erase y, w x)*B := by
          rw [sum_mul]; apply sum_congr rfl; intro x hx; rw [off x y (mem_erase.mp hx).1]
        rw [eq]; ring
      _ = ∑ g : G, (∑ x, w x*u (g • x))*u (g • y) := by
        simp only [gram,mul_sum,sum_mul,mul_assoc]
        rw [sum_comm]
      _ = _ := by simp only [fixed,mul_sum]
  intro x y
  obtain ⟨g,rfl⟩ := trans x y
  have same : (∑ h : G, u (h • (g • x))) = ∑ h : G, u (h • x) := by
    apply Fintype.sum_equiv (Equiv.mulRight g)
    intro h; simp [mul_smul]
  have z := lin (g • x)
  rw [same,←lin x] at z
  exact mul_right_cancel₀ (sub_ne_zero.mpr gap) (add_left_cancel z).symm

private theorem divisor_weights {K α : Type*} [Field K] [DecidableEq α] (a : α → K)
    (T : Finset α) (k : ℕ) (D : K[X]) (dm : D.Monic)
    (dvd : D ∣ ∏ i ∈ T, (X-C (a i))^k) :
    ∃ w : α → ℕ, (∀ i, w i ≤ k) ∧ D = ∏ i ∈ T, (X-C (a i))^(w i) := by
  classical
  induction T using Finset.induction_on generalizing D with
  | empty =>
    have : IsUnit D := isUnit_of_dvd_one (by simpa using dvd)
    exact ⟨fun _ => 0,fun _ => Nat.zero_le _,by simp [dm.eq_one_of_isUnit this]⟩
  | @insert j T fresh ih =>
    rw [prod_insert fresh] at dvd
    obtain ⟨U,V,um,vm,ud,vd,prod⟩ := Green28PrimeFactors.split_monic_divisor dm dvd
    obtain ⟨e,le,assoc⟩ := (dvd_prime_pow (prime_X_sub_C (a j)) k).mp ud
    have ueq : U = (X-C (a j))^e := eq_of_monic_of_associated um ((monic_X_sub_C _).pow _) assoc
    obtain ⟨w,bound,veq⟩ := ih V vm vd
    refine ⟨Function.update w j e,fun i => ?_,?_⟩
    · by_cases h : i = j
      · subst i; simpa using le
      · simpa [Function.update_of_ne h] using bound i
    · rw [prod_insert fresh,Function.update_self,prod,ueq,veq]
      congr 1
      apply prod_congr rfl
      intro x hx
      have neq : x ≠ j := fun h => fresh (h ▸ hx)
      rw [Function.update_of_ne neq]

private theorem all_roots_product (H : ℚ[X]) (hm : H.Monic) (irr : Irreducible H) :
    H.map (algebraMap ℚ H.SplittingField) = ∏ x : H.rootSet H.SplittingField, (X-C x.val) := by
  classical
  let F := H.map (algebraMap ℚ H.SplittingField)
  have splits : F.Splits := SplittingField.splits H
  have nd : F.roots.Nodup := nodup_roots irr.separable.map
  refine (splits.eq_prod_roots_of_monic (hm.map _)).trans ?_
  change (F.roots.map fun x => X-C x).prod =
    ∏ x : F.roots.toFinset, (X-C x.val)
  rw [Finset.prod_coe_sort F.roots.toFinset (fun x : H.SplittingField => X-C x)]
  change _ = (F.roots.toFinset.val.map fun x => X-C x).prod
  rw [Multiset.toFinset_val,nd.dedup]

/-- Transitivity of the Galois group on unordered pairs of distinct roots. -/
def PairTransitive (H : ℚ[X]) : Prop :=
  ∀ a b x y : H.rootSet H.SplittingField, a ≠ b → x ≠ y → ∃ g : H.Gal,
    (g a.val = x.val ∧ g b.val = y.val) ∨ (g a.val = y.val ∧ g b.val = x.val)

private theorem root_trans (H : ℚ[X]) (irr : Irreducible H) :
    ∀ a b : H.rootSet H.SplittingField, ∃ g : H.Gal, g • a = b := by
  let : Normal ℚ H.SplittingField := SplittingField.instNormal H
  intro a b
  have ha := minpoly.eq_of_irreducible irr (mem_rootSet.mp a.2).2
  have hb := minpoly.eq_of_irreducible irr (mem_rootSet.mp b.2).2
  obtain ⟨g,hg⟩ := (Normal.minpoly_eq_iff_mem_orbit H.SplittingField).mp (hb.symm.trans ha)
  exact ⟨g,Subtype.ext hg⟩

private theorem root_log_product {K α : Type*} [Field K] [Algebra ℚ K] [Fintype α]
    (emb : K →ₐ[ℚ] ℂ) (a : α → K) (nz : ∀ x, a x ≠ 0) (w : α → ℕ) :
    Real.log ‖emb (∏ x, (-a x)^(w x))‖ = ∑ x, (w x:ℝ)*Real.log ‖emb (a x)‖ := by
  classical
  simp only [map_prod,map_pow,map_neg,norm_prod,norm_pow,norm_neg]
  rw [Real.log_prod (fun x _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (by simpa only [_root_.map_ne_zero] using nz x)))]
  simp only [Real.log_pow]

private theorem transfer_product {H : ℚ[X]} (emb : H.SplittingField →ₐ[ℚ] ℂ)
    (w : H.rootSet H.SplittingField → ℕ) (D : ℂ[X])
    (prod : D = ∏ x, (X-C (emb x.val))^(w x)) {q : ℚ} (cq : D.coeff 0 = (q:ℂ)) :
    ∏ x, (-x.val)^(w x) = algebraMap ℚ H.SplittingField q := by
  apply emb.injective
  change emb _ = emb (algebraMap ℚ H.SplittingField q)
  rw [emb.commutes]
  rw [coeff_zero_eq_eval_zero,prod] at cq
  simpa [eval_prod] using cq

private theorem map_roots_product (H : ℚ[X]) (hm : H.Monic) (irr : Irreducible H)
    (emb : H.SplittingField →ₐ[ℚ] ℂ) :
    H.map (algebraMap ℚ ℂ) = ∏ x : H.rootSet H.SplittingField, (X-C (emb x.val)) := by
  have h := congrArg (fun T => Polynomial.map emb.toRingHom T) (all_roots_product H hm irr)
  rw [Polynomial.map_map,RingHom.ext_rat (emb.toRingHom.comp _) (algebraMap ℚ ℂ)] at h
  rw [h,Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro x _
  rw [Polynomial.map_sub,map_X,map_C]
  rfl

/-- For an irreducible two-homogeneous core, a monic complex divisor of any
power with constant coefficient ±1 is either supported on the unit circle or
it is a whole power. -/
theorem unit_roots_or_power (H : ℚ[X]) (hm : H.Monic) (irr : Irreducible H)
    (hn : H.coeff 0 ≠ 0) (pairs : PairTransitive H) (k : ℕ) (D : ℂ[X]) (dm : D.Monic)
    (dvd : D ∣ (H.map (algebraMap ℚ ℂ))^k) (sign : D.coeff 0 = 1 ∨ D.coeff 0= -1) :
    (∀ z ∈ D.roots, ‖z‖=1) ∨ ∃ t ≤ k, D = (H.map (algebraMap ℚ ℂ))^t := by
  classical
  let R := H.rootSet H.SplittingField
  let emb : H.SplittingField →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have roots := map_roots_product H hm irr emb
  rw [roots,←Finset.prod_pow] at dvd
  obtain ⟨w,le,prod⟩ := divisor_weights (fun x : R => emb x.val) univ k D dm dvd
  obtain ⟨q,cq,nq⟩ : ∃ q : ℚ, D.coeff 0 = (q:ℂ) ∧ ‖(q:ℂ)‖=1 := by
    rcases sign with h|h
    · exact ⟨1,by simpa using h,by simp⟩
    · exact ⟨-1,by simpa using h,by simp⟩
  have rational := transfer_product emb w D prod cq
  have nz (x : R) : x.val ≠ 0 := by
    intro hx
    have h := (mem_rootSet.mp x.2).2
    rw [hx] at h
    rw [←coeff_zero_eq_aeval_zero'] at h
    exact hn ((_root_.map_eq_zero (algebraMap ℚ H.SplittingField)).mp h)
  let u (x : R) := Real.log ‖emb x.val‖
  have fixed (g : H.Gal) : ∑ x, (w x:ℝ)*u (g • x) = 0 := by
    have h := root_log_product emb (fun x : R => g x.val) (fun x => by
      simpa only [_root_.map_ne_zero] using nz x) w
    have rat := congrArg (fun b : H.SplittingField => g b) rational
    simp only [map_prod,map_pow,map_neg] at rat
    have fixes : g ((algebraMap ℚ H.SplittingField) q) = algebraMap ℚ H.SplittingField q :=
      (g : H.SplittingField ≃ₐ[ℚ] H.SplittingField).commutes q
    rw [rat,fixes,emb.commutes] at h
    change Real.log ‖(q:ℂ)‖=_ at h
    rw [nq,Real.log_one] at h
    exact h.symm
  by_cases var : ∃ a b, u a ≠ u b
  · right
    obtain ⟨a,b,hab⟩ := var
    have same := constant_weights (root_trans H irr) (fun x y j l xy jl => by
      obtain ⟨g,h|h⟩ := pairs x y j l xy jl
      · exact ⟨g,Or.inl ⟨Subtype.ext h.1,Subtype.ext h.2⟩⟩
      · exact ⟨g,Or.inr ⟨Subtype.ext h.1,Subtype.ext h.2⟩⟩)
      u (fun x => (w x:ℝ)) ⟨a,b,hab⟩ fixed
    refine ⟨w a,le a,?_⟩
    rw [prod,roots,←Finset.prod_pow]
    exact prod_congr rfl fun x _ => by rw [show w x = w a by exact_mod_cast same x a]
  · left
    push Not at var
    intro z hz
    have zero := (mem_roots dm.ne_zero).mp hz
    rw [IsRoot,prod,eval_prod] at zero
    obtain ⟨i,_,hi⟩ := Finset.prod_eq_zero_iff.mp zero
    simp only [eval_pow,eval_sub,eval_X,eval_C] at hi
    obtain ⟨eq,pos⟩ := pow_eq_zero_iff'.mp hi
    have total : 0 < ∑ x, (w x:ℝ) := single_le_sum (f:=fun x => (w x:ℝ))
      (fun _ _ => Nat.cast_nonneg _) (mem_univ i) |>.trans_lt' (by exact_mod_cast Nat.pos_of_ne_zero pos)
    have h := fixed 1
    simp only [one_smul] at h
    have h' : (∑ x, (w x:ℝ))*u i = 0 := by
      rw [Finset.sum_mul,←h]
      exact sum_congr rfl fun x _ => by rw [var x i]
    have ui := (mul_eq_zero.mp h').resolve_left total.ne'
    rw [sub_eq_zero.mp eq]
    exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr (by simpa only [_root_.map_ne_zero] using nz i)) ui

open Green28 Green28UniformSums Green28PrimitiveSupport Green28PolynomialReduction
open Green28RootLocation Green28ReversalField Green28PrimeFactors

/-- Arbitrarily repeated irreducible core with two-homogeneous Galois group,
padded by any nonzero real polynomial with unit-modulus roots. -/
theorem binary_of_padded_core {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) (H : ℚ[X]) (hm : H.Monic) (irr : Irreducible H)
    (hn : H.coeff 0 ≠ 0) (pairs : PairTransitive H) (k : ℕ)
    (U : ℝ[X]) (un : U ≠ 0) (unit : ∀ z ∈ (U.map Complex.ofRealHom).roots, ‖z‖=1)
    (dvd : f ∣ (H.map (algebraMap ℚ ℝ))^k * U) : Binary f ∧ Binary g := by
  obtain ⟨D,W,dm,wm,dd,dw,fact⟩ := split_monic_divisor fm dvd
  have wn := (wm.map Complex.ofRealHom).ne_zero
  have un' : U.map Complex.ofRealHom ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr un
  have wu (z : ℂ) (hz : z ∈ (W.map Complex.ofRealHom).roots) : ‖z‖=1 := by
    apply unit z ((mem_roots un').mpr ?_)
    exact dvd_iff_isRoot.mp <| (dvd_iff_isRoot.mpr ((mem_roots wn).mp hz)).trans
      (Polynomial.map_dvd Complex.ofRealHom dw)
  have rev := reverse_eq_scaled_of_unit_roots W wm wu
  have sq := congrArg (fun T : ℝ[X] => T.coeff 0) rev
  simp only [coeff_zero_reverse,wm.leadingCoeff,coeff_C_mul] at sq
  have signs : W.coeff 0 = 1 ∨ W.coeff 0= -1 := by
    have eq : (W.coeff 0-1)*(W.coeff 0+1) = 0 := by nlinarith
    rcases mul_eq_zero.mp eq with h|h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have prod := congrArg (fun T : ℝ[X] => T.coeff 0) fact
  rw [fc,mul_coeff_zero] at prod
  have dsign : (D.map Complex.ofRealHom).coeff 0 = 1 ∨ (D.map Complex.ofRealHom).coeff 0= -1 := by
    rcases signs with h|h
    · have e : D.coeff 0 = 1 := by simpa [h] using prod.symm
      exact Or.inl (by simp [coeff_map,e])
    · have e : D.coeff 0= -1 := by rw [h,mul_neg_one] at prod; linarith
      exact Or.inr (by simp [coeff_map,e])
  have cover := Polynomial.map_dvd Complex.ofRealHom dd
  rw [Polynomial.map_pow,Polynomial.map_map,RingHom.ext_rat (Complex.ofRealHom.comp _) (algebraMap ℚ ℂ)] at cover
  rcases unit_roots_or_power H hm irr hn pairs k _ (dm.map _) cover dsign with du|⟨t,_,pow⟩
  · apply binary_of_reciprocal fm gm fc gc fp gp bin (reciprocal_of_unit_roots f fm fc ?_)
    intro z hz
    rw [fact,Polynomial.map_mul,roots_mul (mul_ne_zero (dm.map _).ne_zero wn),
      Multiset.mem_add] at hz
    exact hz.elim (du z) (wu z)
  · have rat (n : ℕ) : D.coeff n ∈ (algebraMap ℚ ℝ).fieldRange := by
      refine ⟨(H^t).coeff n,?_⟩
      have eq := congrArg (fun T : ℂ[X] => T.coeff n) pow
      rw [←Polynomial.map_pow,coeff_map,coeff_map] at eq
      apply Complex.ofReal_injective
      exact (Complex.ofReal_ratCast _).trans eq.symm
    rcases signs with h|h
    · exact binary_of_rational_times_reciprocal fm gm fc gc fp gp bin fact rat
        (c:=1) (by simpa [h] using rev)
    · exact binary_of_rational_times_reciprocal fm gm fc gc fp gp bin fact rat
        (c:= -1) (by simpa [h] using rev)

/-- A condition solely on the uniform sum support guarantees both original
integer laws are uniform. The degree and multiplicity of the core are unrestricted. -/
theorem uniform_of_cyclotomic_core {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (H : ℚ[X]) (hm : H.Monic) (irr : Irreducible H)
    (hn : H.coeff 0 ≠ 0) (pairs : PairTransitive H) (k m e : ℕ) (mp : 0 < m)
    (cover : (outputMask S ne).map (Int.castRingHom ℚ) ∣ H^k*(X^m-1)^e) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  obtain ⟨f,g,_,_,_,_,pf,pg,fm,gm,_,_,fc,gc,eq⟩ := mask_factorization ne sum
  let U := ((X:ℝ[X])^m-1)^e
  have un : (X:ℝ[X])^m-1 ≠ 0 := by simpa using X_pow_sub_C_ne_zero mp (1:ℝ)
  have unit (z : ℂ) (hz : z ∈ (U.map Complex.ofRealHom).roots) : ‖z‖=1 := by
    apply norm_of_cyclotomic_part (e:=e) mp
    simpa only [U,Polynomial.map_pow,Polynomial.map_sub,map_X,Polynomial.map_one] using hz
  have h := Polynomial.map_dvd (algebraMap ℚ ℝ) cover
  rw [Polynomial.map_map,RingHom.ext_int ((algebraMap ℚ ℝ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℝ),
    ←eq] at h
  have div : f ∣ (H.map (algebraMap ℚ ℝ))^k*U := (dvd_mul_right f g).trans <| by
    simpa only [U,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,map_X,Polynomial.map_one] using h
  have bin := ((pf.mul pg).uniform_iff (fm.mul gm)).mp ⟨S,ne,sum⟩
  have fair := binary_of_padded_core fm gm fc gc pf.nonneg pg.nonneg bin H hm irr hn pairs k U
    (pow_ne_zero e un) unit div
  exact ⟨(pf.uniform_iff fm).mpr fair.1,(pg.uniform_iff gm).mpr fair.2⟩

#print axioms constant_weights
#print axioms unit_roots_or_power
#print axioms binary_of_padded_core
#print axioms uniform_of_cyclotomic_core
end Green28GaloisOrbits
