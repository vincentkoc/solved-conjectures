import Green51GoldSix

/-! # Trace spaces for binary BCH projections over the field of 64 elements -/

open Green51GoldSix Green51BCHCompression Green51BCHOptimality Green51GoldForms Polynomial Finset
open scoped Pointwise
namespace Green51SixPencils
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

omit [Algebra F K] [Fintype K] in
private theorem power_row (c x y : K) (n : ℕ) :
    (c*bracket x y)^(2^n)=c^(2^n)*(x^(2^(n+1))*y^(2^n)+x^(2^n)*y^(2^(n+1))) := by
  let f := iterateFrobenius K 2 n
  change f (c*bracket x y)=_
  rw [map_mul,show bracket x y=x^2*y+x*y^2 from by unfold bracket; ring,map_add,map_mul,map_mul,map_pow,map_pow]
  simp only [f,iterateFrobenius_def,←pow_mul,pow_succ 2 n]

private theorem zero_trace (m : Module.finrank F K=6) {c x y : K}
    (hc : c^4=c^2+c) (hx : x^16=x^4+x) (hy : y^16=y^4+y) :
    let z := c*bracket x y
    z+z^2+z^4+z^8+z^16+z^32=0 := by
  have c8 : c^8=c := by
    rw [show (8 : ℕ)=4*2 by decide,pow_mul,hc,add_sq,←pow_mul]
    norm_num
    rw [hc]
    ring_nf
    reduce_mod_char!
  have c16 : c^16=c^2 := by rw [show (16 : ℕ)=8*2 by decide,pow_mul,c8]
  have c32 : c^32=c^2+c := by rw [show (32 : ℕ)=8*4 by decide,pow_mul,c8,hc]
  have pow32 (a : K) (ha : a^16=a^4+a) : a^32=a^8+a^2 := by
    rw [show (32 : ℕ)=16*2 by decide,pow_mul,ha,add_sq,←pow_mul]
    ring_nf
    reduce_mod_char!
  let z := c*bracket x y
  have h (n : ℕ) := power_row c x y n
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  norm_num only [Nat.reducePow,Nat.reduceAdd,pow_one] at h0 h1 h2 h3 h4 h5
  dsimp only
  rw [h1,h2,h3,h4,h5,h0,c32,c16,c8,hc,pow32 x hx,pow32 y hy,hx,hy,
    power_sixty_four m,power_sixty_four m]
  ring_nf
  reduce_mod_char!
omit [CharP K 2] in
/-- The trace of one vanishes in every even binary field extension. -/
theorem trace_one_even (Q : K →ₗ[F] F) (sq : ∀ z,Q (z^2)=Q z) (even : 2∣Module.finrank F K) : Q 1=0 := by
  classical
  let E := GaloisField 2 2
  let _ : Fintype E := Fintype.ofFinite E
  have sz : Module.finrank F E=2 := GaloisField.finrank 2 (by decide)
  obtain ⟨j⟩ := (FiniteField.nonempty_algHom_of_finrank_dvd
    (show Module.finrank F E∣Module.finrank F K by rw [sz]; exact even) : Nonempty (E →ₐ[F] K))
  have cu : Fintype.card Eˣ=3 := by rw [Fintype.card_units,Module.card_eq_pow_finrank (K := F),ZMod.card,sz]; decide
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨w,hw⟩ := exists_prime_orderOf_dvd_card (G := Eˣ) 3 (by rw [cu])
  have nz : (w : E)≠1 := by intro e; have eq : w=1 := Units.ext e; simp [eq] at hw
  have wc : (w : E)^3=1 := by
    have h := pow_orderOf_eq_one w
    rw [hw] at h
    exact congrArg (fun u : Eˣ => (u : E)) h
  have prod : ((w : E)-1)*((w : E)^2+(w : E)+1)=0 := by linear_combination wc
  have rel := (mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr nz)
  have e : j ((w : E)^2+w)=1 := by
    rw [CharTwo.add_eq_zero.mp rel,map_one]
  rw [←e,map_add,map_pow,map_add,sq,CharTwo.add_self_eq_zero]

omit [CharP K 2] [Fintype K] in
private theorem trace_test_fixed (Q : K →ₗ[F] F) (sq : ∀ z,Q (z^2)=Q z) (z : K) : Q (z^16+z^4+z)=Q z := by
  have f4 (w : K) : Q (w^4)=Q w := by rw [show (4 : ℕ)=2*2 by decide,pow_mul,sq,sq]
  rw [map_add,map_add,show (16 : ℕ)=4*4 by decide,pow_mul,f4,f4,CharTwo.add_self_eq_zero,zero_add]

private theorem bracket_trace_zero (m : Module.finrank F K=6) (Q : K →ₗ[F] F) (sq : ∀ z,Q (z^2)=Q z)
    {c x y : K} (hc : c^4=c^2+c) (hx : x^16=x^4+x) (hy : y^16=y^4+y) :
    Q (c*bracket x y)=0 := by
  let z := c*bracket x y
  let v := z^16+z^4+z
  have sum : z+z^2+z^4+z^8+z^16+z^32=0 := zero_trace m hc hx hy
  have sqv : v^2=v := by
    dsimp [v]
    linear_combination (norm := (ring_nf; reduce_mod_char!)) sum
  have zero_one : v=0 ∨ v=1 := by
    have h : v*(v-1)=0 := by linear_combination sqv
    exact (mul_eq_zero.mp h).imp_right sub_eq_zero.mp
  change Q z=0
  rw [←trace_test_fixed Q sq z]
  change Q v=0
  rcases zero_one with h|h
  · rw [h,map_zero]
  · rw [h]; exact trace_one_even Q sq (by rw [m]; decide)

omit [Fintype K] in
private def fr (i : ℕ) : K →ₗ[F] K := (iterateFrobenius K 2 i).toAddMonoidHom.toZModLinearMap 2
def coeffMap : K →ₗ[F] K := fr 2+fr 1+LinearMap.id
def traceMap : K →ₗ[F] K := fr 4+fr 2+LinearMap.id
omit [Fintype K] in
theorem coeff_apply (z : K) : coeffMap z=z^4+z^2+z := rfl
omit [Fintype K] in
theorem trace_apply (z : K) : traceMap z=z^16+z^4+z := rfl
omit [CharP K 2] in
private theorem rank_polynomial (D : Submodule F K) (P : Polynomial K) (n : ℕ) (np : P≠0)
    (deg : P.natDegree≤2^n) (vanish : ∀ x∈D,P.eval x=0) : Module.finrank F D≤n := by
  classical
  let Z := univ.image (fun u : D => (u : K))
  have b := Polynomial.card_le_degree_of_subset_roots (p := P) (Z := Z) (by
    intro x hx
    obtain ⟨v,_,rfl⟩ := mem_image.mp hx
    exact (Polynomial.mem_roots np).mpr (vanish v v.property))
  rw [show Z=univ.image (fun u : D => (u : K)) from rfl, card_image_of_injective _ Subtype.val_injective,
    card_univ,Module.card_eq_pow_finrank (K := F),ZMod.card] at b
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (b.trans deg)
theorem coeff_upper : Module.finrank F (coeffMap (K := K)).ker≤2 := by
  let P : Polynomial K := X^4+X^2+X
  have degree : P.natDegree=4 := by dsimp [P]; compute_degree!
  apply rank_polynomial _ P 2 (by intro h; rw [h,natDegree_zero] at degree; omega) degree.le
  intro x hx
  simpa [P,coeff_apply] using (show coeffMap x=0 from hx)
theorem trace_upper : Module.finrank F (traceMap (K := K)).ker≤4 := by
  let P : Polynomial K := X^16+X^4+X
  have degree : P.natDegree=16 := by dsimp [P]; compute_degree!
  apply rank_polynomial _ P 4 (by intro h; rw [h,natDegree_zero] at degree; omega) degree.le
  intro x hx
  simpa [P,trace_apply] using (show traceMap x=0 from hx)
theorem trace_dimension (m : Module.finrank F K=6) : Module.finrank F (traceMap (K := K)).ker=4 := by
  let P : Polynomial K := X^4-X
  have degree : P.natDegree=4 := by dsimp [P]; compute_degree!
  have rr : Module.finrank F (traceMap (K := K)).range≤2 := by
    apply rank_polynomial _ P 2 (by intro h; rw [h,natDegree_zero] at degree; omega) degree.le
    rintro _ ⟨u,rfl⟩
    have frob (a b : K) : (a+b)^4=a^4+b^4 := by ring_nf; reduce_mod_char!
    simp only [P,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,sub_eq_zero,
      trace_apply,frob,←pow_mul]
    norm_num
    rw [power_sixty_four m]
    ring
  have rank := (traceMap (K := K)).finrank_range_add_finrank_ker
  have lim := trace_upper (K := K)
  omega

theorem coeff_dimension (m : Module.finrank F K=6) : Module.finrank F (coeffMap (K := K)).ker=2 := by
  let E := GaloisField 2 3
  let _ : Fintype E := Fintype.ofFinite _
  have deg : Module.finrank F E=3 := GaloisField.finrank 2 (by decide)
  obtain ⟨j⟩ := (FiniteField.nonempty_algHom_of_finrank_dvd
    (show Module.finrank F E∣Module.finrank F K by rw [deg,m]; decide) : Nonempty (E →ₐ[F] K))
  let D := (artinSchreier (K := E)).range
  have rank := (artinSchreier (K := E)).finrank_range_add_finrank_ker
  rw [artinSchreier_ker,finrank_span_singleton one_ne_zero,deg] at rank
  have rd : Module.finrank F D=2 := by dsimp [D]; omega
  have sub : D.map j.toLinearMap≤(coeffMap (K := K)).ker := by
    rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
    have card : Fintype.card E=8 := by rw [Module.card_eq_pow_finrank (K := F),ZMod.card,deg]; decide
    have p8 : t^8=t := by rw [←card,FiniteField.pow_card]
    change coeffMap (j (t^2+t))=0
    rw [coeff_apply,←map_pow,←map_pow,←map_add,←map_add,←map_zero j]
    apply congrArg j
    have add4 (a b : E) : (a+b)^4=a^4+b^4 := (iterateFrobenius E 2 2).map_add a b
    have add2 (a b : E) : (a+b)^2=a^2+b^2 := (frobenius E 2).map_add a b
    rw [add4,add2,←pow_mul,←pow_mul]
    change t^8+t^4+(t^4+t^2)+(t^2+t)=0
    rw [p8]
    calc
      _ = (t+t)+(t^4+t^4)+(t^2+t^2) := by abel
      _ = 0 := by simp [CharTwo.add_self_eq_zero]
  have le := Submodule.finrank_mono sub
  rw [←(D.equivMapOfInjective j.toLinearMap j.injective).finrank_eq,rd] at le
  exact le_antisymm coeff_upper le

open scoped Pointwise
/-- On the relative-trace kernel, the annihilator of the pair bracket is exactly the embedded trace-zero plane of the field of eight elements. -/
theorem coefficient_iff (m : Module.finrank F K=6) (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z) (c : K) :
    (∀ x∈(traceMap (K := K)).ker, ∀ y∈(traceMap (K := K)).ker,Q (c*bracket x y)=0) ↔ c∈(coeffMap (K := K)).ker := by
  let T := (traceMap (K := K)).ker
  let Z := Submodule.span F (Set.image2 bracket (T : Set K) (T : Set K))
  have generates (x : K) (hx : x∈T) (y : K) (hy : y∈T) : bracket x y∈Z := Submodule.subset_span ⟨x,hx,y,hy,rfl⟩
  have dimT : Module.finrank F T=4 := trace_dimension m
  have rankZ := Green51BracketRank.bracket_rank T Z (by omega) generates
  let B : LinearMap.BilinForm F K := (Algebra.lmul F K).toLinearMap.compr₂ Q
  let D := B.orthogonal Z
  have annih (b : K) : (∀ x∈T, ∀ y∈T,Q (b*bracket x y)=0) ↔ b∈D := by
    constructor
    · intro h
      let f := Q.comp (LinearMap.mulLeft F b)
      have sub : Z≤f.ker := Submodule.span_le.mpr (by rintro _ ⟨x,hx,y,hy,rfl⟩; exact h x hx y hy)
      intro z hz
      change Q (z*b)=0
      rw [mul_comm]; exact sub hz
    · intro h x hx y hy
      have eq := h (bracket x y) (generates x hx y hy)
      change Q (bracket x y*b)=0 at eq
      rwa [mul_comm] at eq
  have nondeg : B.ker=⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    change z=0
    by_contra nz
    apply nq
    ext x
    have eq := LinearMap.congr_fun (show B z=0 from hz) (z⁻¹*x)
    change Q (z*(z⁻¹*x))=0 at eq
    simpa [←mul_assoc,nz] using eq
  have rankD := B.finrank_add_finrank_orthogonal' Z
  rw [nondeg,inf_bot_eq,finrank_bot,add_zero] at rankD
  have inclusion : coeffMap.ker≤D := by
    intro b hb
    apply (annih b).mp
    intro x hx y hy
    have cb : b^4=b^2+b := CharTwo.add_eq_zero.mp (by simpa [coeff_apply,add_assoc] using (show coeffMap b=0 from hb))
    have tx (v : K) (hv : v∈T) : v^16=v^4+v := CharTwo.add_eq_zero.mp (by simpa [trace_apply,add_assoc] using (show traceMap v=0 from hv))
    exact bracket_trace_zero m Q sq cb (tx x hx) (tx y hy)
  have dimC := coeff_dimension m
  change Module.finrank F Z + Module.finrank F D=Module.finrank F K at rankD
  have eq := Submodule.eq_of_le_of_finrank_le inclusion (by omega)
  exact (annih c).trans (by rw [eq])

end Green51SixPencils

#print axioms Green51SixPencils.trace_one_even
#print axioms Green51SixPencils.coeff_apply
#print axioms Green51SixPencils.trace_apply
#print axioms Green51SixPencils.coeff_upper
#print axioms Green51SixPencils.trace_upper
#print axioms Green51SixPencils.trace_dimension
#print axioms Green51SixPencils.coeff_dimension
#print axioms Green51SixPencils.coefficient_iff
