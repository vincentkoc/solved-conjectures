import Green28UniformSums

/-! Degree bounds for a rational product with one affine algebraic parameter. -/

open Polynomial Finset

namespace Green28AlgebraicWidth

private noncomputable def projected (φ : ℝ →ₗ[ℚ] ℚ) (v : ℝ) (g : ℝ[X]) : ℚ[X] :=
  ∑ j ∈ g.support, monomial j (φ (v*g.coeff j))

@[simp] private theorem projected_coeff (φ : ℝ →ₗ[ℚ] ℚ) (v : ℝ) (g : ℝ[X]) (j : ℕ) :
    (projected φ v g).coeff j=φ (v*g.coeff j) := by
  classical
  simp only [projected,finsetSum_coeff,coeff_monomial,sum_ite_eq',mem_support_iff]
  split
  · rfl
  · rename_i h
    simp_all

private theorem project_add (φ : ℝ →ₗ[ℚ] ℚ) (v : ℝ) (g h : ℝ[X]) :
    projected φ v (g+h)=projected φ v g+projected φ v h := by
  ext j; simp [mul_add]

private theorem project_rat_mul (φ : ℝ →ₗ[ℚ] ℚ) (v : ℝ) (A : ℚ[X]) (g : ℝ[X]) :
    projected φ v (A.map (algebraMap ℚ ℝ)*g)=A*projected φ v g := by
  ext j
  simp only [projected_coeff,coeff_mul,mul_sum,map_sum]
  apply sum_congr rfl
  intro ij _
  simp only [coeff_map,eq_ratCast]
  change φ (v*((A.coeff ij.1:ℝ)*g.coeff ij.2))=A.coeff ij.1*φ (v*g.coeff ij.2)
  rw [mul_left_comm v]
  exact φ.map_smul (A.coeff ij.1) (v*g.coeff ij.2)

private theorem project_scalar (φ : ℝ →ₗ[ℚ] ℚ) (u v : ℝ) (g : ℝ[X]) :
    projected φ v (C u*g)=projected φ (v*u) g := by
  ext j; simp [mul_assoc]

private theorem project_rat (φ : ℝ →ₗ[ℚ] ℚ) (v : ℝ) (F : ℚ[X]) (zero : φ v=0) :
    projected φ v (F.map (algebraMap ℚ ℝ))=0 := by
  ext j
  simp only [projected_coeff,coeff_map,coeff_zero]
  change φ (v*(F.coeff j:ℝ))=0
  rw [mul_comm]
  exact (φ.map_smul (F.coeff j) v).trans (by simp [zero])

private theorem separating_power (u : ℝ) (k : ℕ) (degree : k < (minpoly ℚ u).natDegree) :
    ∃ φ : ℝ →ₗ[ℚ] ℚ, (∀ i<k, φ (u^i)=0) ∧ φ (u^k)=1 := by
  let I := Fin (minpoly ℚ u).natDegree
  let v (i : I) := u^i.val
  let S : Set I := {i | i.val < k}
  let V := Submodule.span ℚ (v '' S)
  let i : I := ⟨k,degree⟩
  have indep : LinearIndependent ℚ v := linearIndependent_pow u
  have notin : u^k ∉ V := indep.notMem_span_image (x := i) (s := S) (lt_irrefl k)
  obtain ⟨φ,eq,one⟩ := (0 : V →ₗ[ℚ] ℚ).exists_extend_of_notMem notin 1
  refine ⟨φ,?_,one⟩
  intro j hj
  have mem : u^j ∈ V := Submodule.subset_span ⟨⟨j,hj.trans degree⟩,hj,rfl⟩
  exact DFunLike.congr_fun eq ⟨u^j,mem⟩

/-- A rational product with first factor `A + u B` has a cofactor of degree at
least `k · deg A` for every `k` below the degree of `u`, if `A,B` are coprime.
The real cofactor may have coefficients anywhere in the real field. -/
theorem cofactor_degree (A B F : ℚ[X]) (u : ℝ) (g : ℝ[X]) (gm : g.Monic)
    (cop : IsCoprime A B) (product :
      (A.map (algebraMap ℚ ℝ)+C u*B.map (algebraMap ℚ ℝ))*g=F.map (algebraMap ℚ ℝ))
    (k : ℕ) (degree : k < (minpoly ℚ u).natDegree) : k*A.natDegree ≤ g.natDegree := by
  obtain ⟨φ,kills,last⟩ := separating_power u k degree
  let G (i : ℕ) := projected φ (u^i) g
  have recur (i : ℕ) (hi : i<k) : A*G i=(-B)*G (i+1) := by
    have eq := congrArg (projected φ (u^i)) product
    rw [add_mul,mul_assoc,project_add,project_rat_mul,project_scalar,project_rat_mul,
      project_rat φ _ _ (kills i hi),←pow_succ] at eq
    change A*G i+B*G (i+1)=0 at eq
    rw [neg_mul]
    exact eq_neg_of_add_eq_zero_left eq
  have iter (j : ℕ) (hj : j≤k) : A^j*G 0=(-B)^j*G j := by
    induction j with
    | zero => simp
    | succ n ih =>
      calc A^(n+1)*G 0 = A*(A^n*G 0) := by ring
           _ = A*((-B)^n*G n) := by rw [ih (by omega)]
           _ = (-B)^n*(A*G n) := by ring
           _ = (-B)^(n+1)*G (n+1) := by rw [recur n (by omega)]; ring
  have div : A^k ∣ G k := cop.neg_right.pow.dvd_of_dvd_mul_left ⟨G 0,(iter k le_rfl).symm⟩
  have nz : G k ≠ 0 := by
    intro z
    have eq := congrArg (fun q : ℚ[X] => q.coeff g.natDegree) z
    simp [G,gm.coeff_natDegree,last] at eq
  have bound : (G k).natDegree ≤ g.natDegree := natDegree_le_iff_coeff_eq_zero.mpr
    (fun j hj => by simp [G,coeff_eq_zero_of_natDegree_lt hj])
  exact (natDegree_pow A k ▸ natDegree_le_of_dvd div nz).trans bound

/-- The same equation forces every rational subspace containing the cofactor's
coefficients to contain every power of the exceptional weight. Here no
coprimality or degree assumptions on the masks are needed. -/
theorem cofactor_span (A B F : ℚ[X]) (u : ℝ) (g : ℝ[X]) (gm : g.Monic) (bn : B ≠ 0)
    (product : (A.map (algebraMap ℚ ℝ)+C u*B.map (algebraMap ℚ ℝ))*g=F.map (algebraMap ℚ ℝ))
    (V : Submodule ℚ ℝ) (includes : ∀ j, g.coeff j ∈ V) (k : ℕ) : u^k ∈ V := by
  by_contra miss
  obtain ⟨φ,ext,one⟩ := (0 : V →ₗ[ℚ] ℚ).exists_extend_of_notMem miss 1
  have vanish (x : ℝ) (hx : x∈V) : φ x=0 := DFunLike.congr_fun ext ⟨x,hx⟩
  have killed (i : ℕ) : projected φ (u^i) g=0 := by
    induction i with
    | zero => ext j; simp [vanish _ (includes j)]
    | succ i ih =>
      have top := congrArg (fun q : ℚ[X] => q.coeff g.natDegree) ih
      have zero : φ (u^i)=0 := by simpa [gm.coeff_natDegree] using top
      have eq := congrArg (projected φ (u^i)) product
      rw [add_mul,mul_assoc,project_add,project_rat_mul,project_scalar,project_rat_mul,
        project_rat φ _ _ zero,←pow_succ,ih,mul_zero,zero_add] at eq
      exact (mul_eq_zero.mp eq).resolve_left bn
  have top := congrArg (fun q : ℚ[X] => q.coeff g.natDegree) (killed k)
  simp [gm.coeff_natDegree,one] at top

open Green28 Green28UniformSums Green28PolynomialReduction
open scoped ENNReal

/-- The difference between the extreme support sites. The finite uniform-sum
hypothesis in all applications ensures the finite branch applies. -/
noncomputable def width (P : PMF ℤ) : ℕ := by
  classical
  exact if h : P.support.Finite then
    let a := h.toFinset
    let ne := h.toFinset_nonempty.mpr P.support_nonempty
    (a.max' ne-a.min' ne).toNat
  else 0

/-- A monic model at the actual support endpoints, with positive constant term. -/
theorem chart (P : PMF ℤ) (finite : P.support.Finite) :
    ∃ (f : ℝ[X]) (a : ℤ) (s : ℝ), Models P f a s ∧ f.Monic ∧ f.natDegree=width P ∧ 0<f.coeff 0 := by
  classical
  let V := finite.toFinset
  have ne : V.Nonempty := finite.toFinset_nonempty.mpr P.support_nonempty
  let a := V.min' ne
  let e := V.max' ne
  let D := (e-a).toNat
  let scale := (P e).toReal
  have em : e∈P.support := finite.mem_toFinset.mp (V.max'_mem _)
  have am : a∈P.support := finite.mem_toFinset.mp (V.min'_mem _)
  have pos : 0<scale := ENNReal.toReal_pos ((P.mem_support_iff _).mp em) (P.apply_ne_top _)
  have ae : a≤e := V.min'_le _ (V.max'_mem _)
  have shift : a+(D:ℤ)=e := by dsimp [D]; omega
  let w (i : ℕ) := (P (a+i)).toReal/scale
  let f : ℝ[X] := ∑ i ∈ range (D+1), monomial i (w i)
  have off (i : ℕ) (hi : D < i) : w i=0 := by
    have up : e<a+i := by omega
    have out : a+i∉P.support := fun h => up.not_ge (V.le_max' _ (finite.mem_toFinset.mpr h))
    simp [w,(P.apply_eq_zero_iff _).mpr out]
  have coeff (i : ℕ) : f.coeff i=w i := by
    simp only [f,finsetSum_coeff,coeff_monomial,sum_ite_eq',mem_range]
    split
    · rfl
    · rename_i h; exact (off _ (by omega)).symm
  have top : f.coeff D=1 := by rw [coeff]; dsimp [w]; rw [shift]; exact div_self pos.ne'
  have bound := natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => (coeff j).trans (off j hj))
  refine ⟨f,a,scale,⟨pos,?_,?_⟩,monic_of_natDegree_le_of_coeff_eq_one D bound top,
    ?_,?_⟩
  · intro z hz; exact (P.apply_eq_zero_iff _).mpr
      (fun h => hz.not_ge (V.min'_le _ (finite.mem_toFinset.mpr h)))
  · intro i; rw [coeff]; dsimp [w]; field_simp
  · have d := natDegree_eq_of_le_of_coeff_ne_zero bound (top ▸ one_ne_zero)
    simpa only [width,dif_pos finite] using d
  · rw [coeff]; dsimp [w]; rw [add_zero]
    exact div_pos (ENNReal.toReal_pos ((P.mem_support_iff _).mp am) (P.apply_ne_top _)) pos

private noncomputable def mask (s : Finset ℕ) : ℚ[X] := ∑ i ∈ s, monomial i 1

@[simp] private theorem mask_coeff (s : Finset ℕ) (i : ℕ) :
    (mask s).coeff i = if i∈s then 1 else 0 := by
  simp only [mask,finsetSum_coeff,coeff_monomial,sum_ite_eq']

private theorem binary_map {f : ℝ[X]} (bin : Binary f) : (mask f.support).map (algebraMap ℚ ℝ)=f := by
  ext j
  rcases bin j with h|h <;> simp [coeff_map,mem_support_iff,h]

/-- Both constant terms equal one in an endpoint-normalized binary product. -/
theorem endpoints {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (f0 : 0 < f.coeff 0) (g0 : 0 < g.coeff 0) (bin : Binary (f*g)) :
    f.coeff 0=1 ∧ g.coeff 0=1 := by
  have h := bin 0
  rw [mul_coeff_zero] at h
  have product := h.resolve_left (mul_pos f0 g0).ne'
  have a := coeff_le_one gm fp gp bin 0
  have b := coeff_le_one fm gp fp (mul_comm f g ▸ bin) 0
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left b f0.le]
  · nlinarith [mul_le_mul_of_nonneg_right a g0.le]

/-- Two positive-width normalized factors cannot have the same degree: the two
opposite endpoint cells would both contribute one at that degree. -/
theorem unequal_widths {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (f0 : f.coeff 0=1) (g0 : g.coeff 0=1) (bin : Binary (f*g)) (d : 0 < f.natDegree) :
    f.natDegree≠g.natDegree := by
  intro eq
  let n := f.natDegree
  have ne : (0,n)≠(n,0) := by intro e; exact d.ne (Prod.mk.inj e).1
  have gtop : g.coeff n=1 := by change g.coeff f.natDegree=1; rw [eq,gm.coeff_natDegree]
  have top : f.coeff n=1 := fm.coeff_natDegree
  have lt := single_lt_sum (f := fun ij : ℕ×ℕ => f.coeff ij.1*g.coeff ij.2) ne
    (show (n,0)∈antidiagonal n by simp) (show (0,n)∈antidiagonal n by simp)
    (show 0<f.coeff 0*g.coeff n by rw [gtop,f0]; norm_num)
    (fun ij _ _ => mul_nonneg (fp _) (gp _))
  change f.coeff n*g.coeff 0 < _ at lt
  rw [← coeff_mul,top,g0,one_mul] at lt
  rcases bin n with h|h <;> linarith

private theorem masks_of_exception {f : ℝ[X]} (fm : f.Monic) (f0 : f.coeff 0=1)
    {r : ℕ} (u1 : f.coeff r≠1)
    (rest : ∀ j, j≠r → f.coeff j=0 ∨ f.coeff j=1) :
    ∃ A : ℚ[X], IsCoprime A (X^r) ∧ f.natDegree ≤ A.natDegree ∧
      A.map (algebraMap ℚ ℝ)+C (f.coeff r)*(X:ℝ[X])^r=f := by
  classical
  let A := mask (f.support.erase r)
  have rn : r≠0 := fun e => u1 (e ▸ f0)
  have dn : f.natDegree≠r := fun e => u1 (e ▸ fm.coeff_natDegree)
  have at0 : A.coeff 0=1 := by simp [A,mem_erase,mem_support_iff,f0,Ne.symm rn]
  have atd : A.coeff f.natDegree=1 := by simp [A,mem_erase,mem_support_iff,fm.coeff_natDegree,dn]
  have dvd : (X : ℚ[X]) ∣ A-1 := X_dvd_iff.mpr (by simp [at0])
  obtain ⟨h,hd⟩ := dvd
  have cop : IsCoprime A X := ⟨1,-h,by linear_combination hd⟩
  refine ⟨A,cop.pow_right,le_natDegree_of_ne_zero (atd ▸ one_ne_zero),?_⟩
  ext j
  by_cases e : j=r
  · subst j; simp [A,coeff_map,coeff_X_pow]
  · rcases rest j e with h|h <;> simp [A,coeff_map,coeff_X_pow,e,h]

/-- Number of distinct positive atom masses. -/
noncomputable def massLevels (P : PMF ℤ) : ℕ := ((fun x : ℤ => (P x).toReal) '' P.support).ncard

private theorem degree_le_massLevels {Q : PMF ℤ} {g : ℝ[X]} {b : ℤ} {t u : ℝ} (model : Models Q g b t)
    (powers : ∀ V : Submodule ℚ ℝ, (∀ j, g.coeff j∈V) → ∀ k : ℕ, u^k∈V) :
    (minpoly ℚ u).natDegree ≤ massLevels Q := by
  classical
  let T := (model.finite.image (fun x : ℤ => (Q x).toReal)).toFinset
  let S := T.image (fun x : ℝ => x/t)
  let V := Submodule.span ℚ (S : Set ℝ)
  have inc (j : ℕ) : g.coeff j ∈ V := by
    by_cases zero : g.coeff j=0
    · rw [zero]; exact V.zero_mem
    · have e := model.coeff j
      have mem : b+(j:ℤ)∈Q.support := (Q.mem_support_iff _).mpr (by
        intro h; rw [h,ENNReal.toReal_zero] at e; exact (mul_ne_zero model.pos.ne' zero) e.symm)
      apply Submodule.subset_span
      apply mem_image.mpr
      refine ⟨(Q (b+j)).toReal,Set.Finite.mem_toFinset _ |>.mpr ⟨b+j,mem,rfl⟩,?_⟩
      rw [e]; field_simp [model.pos.ne']
  let v (i : Fin (minpoly ℚ u).natDegree) : V := ⟨u^i.val,powers V inc i.val⟩
  have li : LinearIndependent ℚ v := LinearIndependent.of_comp V.subtype (linearIndependent_pow u)
  have d : (minpoly ℚ u).natDegree ≤ Module.finrank ℚ V := by simpa using li.fintype_card_le_finrank
  have sz : T.card = massLevels Q := (Set.ncard_eq_toFinset_card _ _).symm
  exact d.trans ((finrank_span_finset_le_card S).trans (card_image_le.trans_eq sz))

private theorem rational_pencil {f : ℝ[X]} {u : ℝ}
    (line : ∀ j, ∃ a b : ℚ, f.coeff j=(a:ℝ)+(b:ℝ)*u) :
    ∃ A B : ℚ[X], A.map (algebraMap ℚ ℝ)+C u*B.map (algebraMap ℚ ℝ)=f := by
  classical
  choose a b rep using line
  let poly (v : ℕ → ℚ) : ℚ[X] := ∑ i ∈ f.support, monomial i (v i)
  have coeff (v : ℕ → ℚ) (j : ℕ) : (poly v).coeff j=if j∈f.support then v j else 0 := by
    simp only [poly,finsetSum_coeff,coeff_monomial,sum_ite_eq']
  refine ⟨poly a,poly b,?_⟩
  ext j; simp only [coeff_add,coeff_C_mul,coeff_map,coeff]
  by_cases hj : j∈f.support
  · simp only [if_pos hj,eq_ratCast]; rw [rep j]; ring
  · simp [hj,notMem_support_iff.mp hj]

/-- If all normalized masses on the left are rational affine functions of an
occupied nonintegral ratio, the degree of that ratio is bounded by the number
of distinct positive masses on the right. No support-width condition is needed. -/
theorem degree_of_affine_ratios {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    {e x : ℤ} (he : e∈P.support) (largest : ∀ z∈P.support, z≤e) (hx : x∈P.support)
    {u : ℝ} (ratio : (P x).toReal/(P e).toReal=u) (small : u<1)
    (line : ∀ z∈P.support, ∃ c d : ℚ, (P z).toReal/(P e).toReal=(c:ℝ)+(d:ℝ)*u) :
    2 ≤ (minpoly ℚ u).natDegree ∧ (minpoly ℚ u).natDegree ≤ massLevels Q := by
  classical
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum sum
  obtain ⟨f,a,s,fp,fm,_,_⟩ := chart P pf
  obtain ⟨g,b,t,gp,gm,_,_⟩ := chart Q qf
  have bin := ((fp.mul gp).uniform_iff (fm.mul gm)).mp sum
  have lead : (P (a+f.natDegree)).toReal=s := by simpa only [fm.coeff_natDegree,mul_one] using fp.coeff f.natDegree
  have top : a+(f.natDegree:ℤ)∈P.support := (P.mem_support_iff _).mpr (by
    intro h; rw [h,ENNReal.toReal_zero] at lead; exact fp.pos.ne lead)
  have equal : a+(f.natDegree:ℤ)=e := by
    apply le_antisymm (largest _ top)
    by_contra! above
    have off := fp.coeff (e-a).toNat
    rw [show a+↑(e-a).toNat=e by omega,coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < (e-a).toNat),mul_zero] at off
    exact (ENNReal.toReal_pos ((P.mem_support_iff _).mp he) (P.apply_ne_top _)).ne' off
  rw [equal] at lead
  have val (j : ℕ) : (P (a+j)).toReal/(P e).toReal=f.coeff j := by
    rw [fp.coeff,lead]; field_simp [fp.pos.ne']
  have below : a≤x := by by_contra! neg; exact (P.mem_support_iff _).mp hx (fp.below _ neg)
  let r := (x-a).toNat
  have ar : a+(r:ℤ)=x := by dsimp [r]; omega
  have ur : f.coeff r=u := by rw [←val,ar,ratio]
  have pos : 0<u := ratio ▸ div_pos (ENNReal.toReal_pos ((P.mem_support_iff _).mp hx) (P.apply_ne_top _))
    (ENNReal.toReal_pos ((P.mem_support_iff _).mp he) (P.apply_ne_top _))
  have irr : u ∉ (algebraMap ℚ ℝ).range := by
    rintro ⟨q,eq⟩
    have z := rational_coefficient fm gm fp.nonneg gp.nonneg bin r q (eq.trans ur.symm)
    rw [ur] at z
    exact z.elim pos.ne' small.ne
  have integral : IsIntegral ℤ u := ur ▸ integral_coefficient fm gm bin r
  obtain ⟨A,B,eq⟩ := rational_pencil (f := f) (u := u) (by
    intro j
    by_cases h : a+(j:ℤ)∈P.support
    · rw [← val]; exact line _ h
    · refine ⟨0,0,?_⟩; rw [← val,(P.apply_eq_zero_iff _).mpr h]; simp)
  have bn : B≠0 := by
    intro h; rw [h,Polynomial.map_zero,mul_zero,add_zero] at eq
    apply irr; refine ⟨A.coeff r,?_⟩
    simpa only [coeff_map,ur] using congrArg (fun p : ℝ[X] => p.coeff r) eq
  have product : (A.map (algebraMap ℚ ℝ)+C u*B.map (algebraMap ℚ ℝ))*g =
      (mask (f*g).support).map (algebraMap ℚ ℝ) := by rw [eq,binary_map bin]
  exact ⟨(minpoly.two_le_natDegree_iff integral.tower_top).mpr irr,
    degree_le_massLevels gp (cofactor_span A B _ u g gm bn product)⟩

private theorem fair_of_binary {P Q : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (fp : Models P f a s) (fm : f.Monic) (sum : IsUniformOnSupport (indepSum P Q)) (fair : Binary f) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  obtain ⟨S,hs,eq⟩ := (fp.uniform_iff fm).mpr fair
  apply uniform_of_rational_ratios sum
  left; intro x y hy
  rw [eq,PMF.support_uniformOfFinset] at hy
  rw [eq,PMF.uniformOfFinset_apply_of_mem hs hy]
  by_cases hx : x∈S
  · rw [PMF.uniformOfFinset_apply_of_mem hs hx]
    exact ⟨1,by simp [(card_pos.mpr hs).ne']⟩
  · exact ⟨0,by simp [PMF.uniformOfFinset_apply_of_notMem hs hx]⟩

/-- At most one occupied site can have less mass than another atom. -/
def OneDeficit (P : PMF ℤ) : Prop := ∃ a : ℤ, ∀ x∈P.support, (∃ y, P x < P y) → x=a

/-- All ratios are the original atom probabilities divided by the mass at a
maximal site. A nonuniform law with just one deficient atom forces degree
times diameter growth in the opposite law, with unrestricted opposite support. -/
theorem one_deficit_alternative {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit P) : (IsUniformOnSupport P ∧ IsUniformOnSupport Q) ∨
      ∃ a e : ℤ, a∈P.support ∧ e∈P.support ∧ (∀ x∈P.support, x ≤ e) ∧
        let u := (P a).toReal/(P e).toReal
        0 < u ∧ u < 1 ∧ 2 ≤ (minpoly ℚ u).natDegree ∧ width P < width Q ∧
          ((minpoly ℚ u).natDegree-1)*width P ≤ width Q ∧ (minpoly ℚ u).natDegree ≤ massLevels Q := by
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum sum
  obtain ⟨f,a,s,fp,fm,fd,fpos⟩ := chart P pf
  obtain ⟨g,b,t,gp,gm,gd,gpos⟩ := chart Q qf
  have bin := ((fp.mul gp).uniform_iff (fm.mul gm)).mp sum
  by_cases fair : Binary f
  · exact Or.inl (fair_of_binary fp fm sum fair)
  · change ¬ ∀ n, f.coeff n=0 ∨ f.coeff n=1 at fair
    push Not at fair
    obtain ⟨r,r0,r1⟩ := fair
    have lead := fp.coeff f.natDegree
    rw [fm.coeff_natDegree,mul_one] at lead
    have ur : (P (a+r)).toReal=s*f.coeff r := fp.coeff r
    have mass (j : ℕ) (j0 : f.coeff j≠0) : a+(j:ℤ)∈P.support := (P.mem_support_iff _).mpr (by
      intro z; have h := fp.coeff j; rw [z,ENNReal.toReal_zero] at h
      exact (mul_ne_zero fp.pos.ne' j0) h.symm)
    have force (j : ℕ) (j1 : f.coeff j≠1) :
        P (a+j)<P (a+f.natDegree) := by
      apply (ENNReal.toReal_lt_toReal (P.apply_ne_top _) (P.apply_ne_top _)).mp
      rw [fp.coeff,lead]
      exact (mul_lt_mul_of_pos_left (lt_of_le_of_ne (coeff_le_one gm fp.nonneg gp.nonneg bin j) j1) fp.pos).trans_eq (mul_one _)
    obtain ⟨special,uniq⟩ := one
    have loc := uniq (a+r) (mass r r0) ⟨_,force r r1⟩
    have rest (j : ℕ) (ne : j≠r) : f.coeff j=0 ∨ f.coeff j=1 := by
      by_contra! none
      have e := uniq (a+j) (mass j none.1) ⟨_,force j none.2⟩
      omega
    have ends := endpoints fm gm fp.nonneg gp.nonneg fpos gpos bin
    obtain ⟨A,cop,deg,model⟩ := masks_of_exception fm ends.1 r1 rest
    have int := integral_coefficient fm gm bin r
    have irrational : f.coeff r ∉ (algebraMap ℚ ℝ).range := by
      rintro ⟨q,eq⟩
      exact (rational_coefficient fm gm fp.nonneg gp.nonneg bin r q eq).elim r0 r1
    let d := (minpoly ℚ (f.coeff r)).natDegree
    have two : 2 ≤ d := (minpoly.two_le_natDegree_iff int.tower_top).mpr irrational
    have eq : (A.map (algebraMap ℚ ℝ)+C (f.coeff r)*((X:ℚ[X])^r).map (algebraMap ℚ ℝ))*g =
        (mask (f*g).support).map (algebraMap ℚ ℝ) := by
      simp only [Polynomial.map_pow,map_X,model,binary_map bin]
    have bound := cofactor_degree A (X^r) _ _ g gm cop eq (d-1) (by change d-1<d; omega)
    have dpos : 0<f.natDegree := by
      have p := le_natDegree_of_ne_zero r0
      have ne : r≠0 := fun e => r1 (e ▸ ends.1)
      omega
    have mismatch := unequal_widths fm gm fp.nonneg gp.nonneg ends.1 ends.2 bin dpos
    have big : (d-1)*f.natDegree ≤ g.natDegree := (Nat.mul_le_mul_left _ deg).trans bound
    have strict : f.natDegree < g.natDegree := lt_of_le_of_ne
      ((Nat.le_mul_of_pos_left _ (by omega : 0<d-1)).trans big) mismatch
    right; refine ⟨a+r,a+f.natDegree,mass _ r0,mass _ (fm.coeff_natDegree ▸ one_ne_zero),?_,?_⟩
    · intro x hx
      by_contra! above
      have off := fp.coeff (x-a).toNat
      rw [show a+↑(x-a).toNat=x by omega,coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < (x-a).toNat),mul_zero] at off
      exact (ENNReal.toReal_pos ((P.mem_support_iff _).mp hx) (P.apply_ne_top _)).ne' off
    · dsimp only
      have ratio : (P (a+r)).toReal/(P (a+f.natDegree)).toReal=f.coeff r := by rw [ur,lead]; field_simp [fp.pos.ne']
      rw [ratio,←fd,←gd]
      exact ⟨lt_of_le_of_ne (fp.nonneg r) r0.symm,lt_of_le_of_ne (coeff_le_one gm fp.nonneg gp.nonneg bin r) r1,two,strict,big,
        degree_le_massLevels gp (cofactor_span A (X^r) _ _ g gm (pow_ne_zero _ X_ne_zero) eq)⟩

/-- A marginal with at most one deficient atom cannot be the wider law in a
counterexample. The opposite law may use any number of sites and mass levels. -/
theorem uniform_of_one_deficit_of_width {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit P) (size : width Q ≤ width P) : IsUniformOnSupport P ∧ IsUniformOnSupport Q :=
  (one_deficit_alternative sum one).resolve_right (by
    rintro ⟨a,e,ha,he,top,u,lt,degree,strict,bound,levels⟩
    omega)

#print axioms unequal_widths
#print axioms cofactor_degree
#print axioms cofactor_span
#print axioms degree_of_affine_ratios
#print axioms one_deficit_alternative
#print axioms uniform_of_one_deficit_of_width

end Green28AlgebraicWidth
