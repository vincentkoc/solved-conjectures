import Green28OutputCardinality
import Green28RootLocation

/-! The boundary case in the output cardinality bound for Green 28. -/

namespace Green28OutputBoundary

open Finset Polynomial Green28PolynomialReduction Green28RootLocation
open scoped Polynomial

/-- For a normalized trinomial, three coefficients of the product suffice
when the partner has at most twice its degree. -/
theorem binary_trinomial_of_double_width {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) {r d : ℕ} (rp : 0 < r) (rd : r < d) (fd : f.natDegree = d)
    (u : ℝ) (shape : f = 1+C u*X^r+X^d) (width : g.natDegree ≤ 2*d) : Binary f ∧ Binary g := by
  let K := (algebraMap ℚ ℝ).fieldRange
  have gd : g.coeff d = 0 := by
    rcases reverse_coeff_eq_zero_or fm gc fp gp bin (show 0 < d by omega) with h|h
    · rw [coeff_reverse,fd,revAt_le le_rfl,Nat.sub_self,fc] at h
      exact (one_ne_zero h).elim
    · exact h
  have tail : g.coeff (2*d+r) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have two : g.coeff (2*d) = 0 ∨ g.coeff (2*d) = 1 := by
    rcases width.eq_or_lt with e|lt
    · exact Or.inr (e ▸ gm.coeff_natDegree)
    · exact Or.inl (coeff_eq_zero_of_natDegree_lt lt)
  have coeff (i : ℕ) : (f*g).coeff i = g.coeff i+
      u*(if r ≤ i then g.coeff (i-r) else 0)+(if d ≤ i then g.coeff (i-d) else 0) := by
    rw [shape,add_mul,add_mul,one_mul,mul_assoc,coeff_add,coeff_add,coeff_C_mul,
      coeff_X_pow_mul',coeff_X_pow_mul']
  have c0 := coeff r
  have c1 := coeff (d+r)
  have c2 := coeff (2*d+r)
  simp only [le_rfl,ite_true,Nat.sub_self,gc,mul_one,if_neg (not_le.mpr rd),add_zero] at c0
  simp only [show r ≤ d+r by omega, show d ≤ d+r by omega,ite_true,Nat.add_sub_cancel, Nat.add_sub_cancel_left,gd,mul_zero,add_zero] at c1
  simp only [show r ≤ 2*d+r by omega,show d ≤ 2*d+r by omega,ite_true,Nat.add_sub_cancel,
    show 2*d+r-d = d+r by omega,tail,zero_add] at c2
  have values (i : ℕ) : (f*g).coeff i ∈ K := (bin i).elim (fun e => e ▸ K.zero_mem) (fun e => e ▸ K.one_mem)
  have relation : u*(1+g.coeff (2*d)) ∈ K := by
    have eq : (f*g).coeff r-(f*g).coeff (d+r)+(f*g).coeff (2*d+r) = u*(1+g.coeff (2*d)) := by linarith
    exact eq ▸ K.add_mem (K.sub_mem (values r) (values (d+r))) (values _)
  have denom : 1+g.coeff (2*d) ∈ K := K.add_mem K.one_mem (two.elim (fun e => e ▸ K.zero_mem) (fun e => e ▸ K.one_mem))
  have nz : 1+g.coeff (2*d) ≠ 0 := by linarith [gp (2*d)]
  have rat : u ∈ K := by simpa [nz] using K.div_mem relation denom
  apply rational_factor fm gm fp gp bin
  intro i
  rw [shape,coeff_add,coeff_add,coeff_C_mul]
  apply K.add_mem (K.add_mem ?_ (K.mul_mem rat ?_)) ?_
  · simp [coeff_one]; split <;> simp [K]
  · rw [coeff_X_pow]; split <;> simp [K]
  · rw [coeff_X_pow]; split <;> simp [K]

/-- Four singleton corners leave room for only one multiply represented
total outside a full deficient row in the limiting cardinality case. -/
private theorem outside_equal {S C R : Finset ℤ} (ub : S.card ≤ R.card+5)
    (cs : C ⊆ S) (rs : R ⊆ S) (cr : Disjoint C R) (four : 4 ≤ C.card)
    {x y : ℤ} (xs : x ∈ S) (xc : x ∉ C) (xr : x ∉ R) (ys : y ∈ S) (yc : y ∉ C) (yr : y ∉ R) : x = y := by
  by_contra neq
  have sub : insert x (insert y (C∪R)) ⊆ S := by
    intro v h
    rcases mem_insert.mp h with rfl|h
    · exact xs
    rcases mem_insert.mp h with rfl|h
    · exact ys
    exact (mem_union.mp h).elim (fun h => cs h) (fun h => rs h)
  have h := card_le_card sub
  rw [card_insert_of_notMem (by simp [neq,xc,xr]),card_insert_of_notMem (by simp [yc,yr]),
    card_union_of_disjoint cr] at h
  omega

private theorem singleton_totals {A B S H K : Finset ℤ} (ha : H ⊆ A) (kb : K ⊆ B)
    (cover : ∀ x ∈ A, ∀ y ∈ B, x+y ∈ S)
    (unique : ∀ x ∈ H, ∀ y ∈ K, ∀ u ∈ A, ∀ v ∈ B, x+y = u+v → x = u ∧ y = v) :
    ∃ C ⊆ S, C.card = H.card*K.card ∧ ∀ x ∈ A, ∀ y ∈ B, x+y ∈ C ↔ x ∈ H ∧ y ∈ K := by
  classical
  let C := (H ×ˢ K).image (fun z => z.1+z.2)
  refine ⟨C,?_,?_,?_⟩
  · intro v hv
    obtain ⟨⟨x,y⟩,xy,rfl⟩ := mem_image.mp hv
    exact cover x (ha (mem_product.mp xy).1) y (kb (mem_product.mp xy).2)
  · rw [←Finset.card_product]
    apply card_image_of_injOn
    rintro ⟨x,y⟩ xy ⟨u,v⟩ uv e
    have h := unique x (mem_product.mp xy).1 y (mem_product.mp xy).2 u
      (ha (mem_product.mp uv).1) v (kb (mem_product.mp uv).2) e
    exact Prod.ext h.1 h.2
  · intro x hx y hy
    constructor
    · rintro h
      obtain ⟨⟨u,v⟩,uv,e⟩ := mem_image.mp h
      obtain ⟨uh,vk⟩ := mem_product.mp uv
      obtain ⟨rfl,rfl⟩ := unique u uh v vk x hx y hy e
      exact ⟨uh,vk⟩
    · rintro ⟨xh,yk⟩
      exact mem_image.mpr ⟨(x,y),mem_product.mpr ⟨xh,yk⟩,rfl⟩

open Green28 Green28UniformSums Green28UnpairedSites Green28OutputCardinality

private theorem card_le_three {P : PMF ℤ} (pf : P.support.Finite) (E : Extremes P.support)
    (L : Extremes (lowerSites P E.lo)) (same : L.hi = L.lo) (few : (endpointSites P E.lo).ncard ≤ 2) :
    P.support.ncard ≤ 3 := by
  classical
  have hf : (endpointSites P E.lo).Finite := pf.subset fun _ h => h.1
  have sub : pf.toFinset ⊆ insert L.lo hf.toFinset := by
    intro x hx
    have occupied := pf.mem_toFinset.mp hx
    by_cases high : (P x).toReal = (P E.lo).toReal
    · exact mem_insert_of_mem (hf.mem_toFinset.mpr ⟨occupied,high⟩)
    · have l : x ∈ lowerSites P E.lo := ⟨occupied,high⟩
      exact mem_insert.mpr (Or.inl (le_antisymm (same ▸ L.greatest.2 l) (L.least.2 l)))
  have c := (card_le_card sub).trans (card_insert_le _ _)
  rw [Set.ncard_eq_toFinset_card _ pf]
  rw [Set.ncard_eq_toFinset_card _ hf] at few
  omega

private theorem boundary_geometry {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (L : Alignment P Q)
    (large : 5 < Q.support.ncard) (limit : S.card ≤ Q.support.ncard+5) :
    P.support.ncard ≤ 3 ∧ L.right.hi-L.right.lo = 2*(L.left.hi-L.left.lo) := by
  classical
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  let a := L.left.lo
  let b := L.right.lo
  let d := L.left.hi
  let e := L.right.hi
  let p := L.leftLow.lo
  let q := L.rightLow.lo
  let p' := L.leftLow.hi
  let q' := L.rightLow.hi
  have hf : (endpointSites P a).Finite := pf.subset fun _ h => h.1
  have kf : (endpointSites Q b).Finite := qf.subset fun _ h => h.1
  let H := hf.toFinset
  let K := kf.toFinset
  let A := pf.toFinset
  let B := qf.toFinset
  obtain ⟨hp,kp,bound⟩ := aligned_output_count ne sum L
  change 2 ≤ (endpointSites P a).ncard at hp
  change 2 ≤ (endpointSites Q b).ncard at kp
  have prod : (endpointSites P a).ncard*(endpointSites Q b).ncard ≤ 4 := by
    change (endpointSites P a).ncard*(endpointSites Q b).ncard+
      max (Q.support.ncard+((endpointSites P a).ncard-1)) (P.support.ncard+((endpointSites Q b).ncard-1)) ≤ S.card at bound
    omega
  have smallP : (endpointSites P a).ncard ≤ 2 := by nlinarith
  have smallQ : (endpointSites Q b).ncard ≤ 2 := by nlinarith
  have four : 4 ≤ H.card*K.card := by
    rw [Set.ncard_eq_toFinset_card _ hf] at hp
    rw [Set.ncard_eq_toFinset_card _ kf] at kp
    exact Nat.mul_le_mul hp kp
  obtain ⟨topP,topQ,rect⟩ := maximal_rectangle flat L.left L.right
  have aH : a ∈ H := hf.mem_toFinset.mpr ⟨L.left.least.1,rfl⟩
  have dH : d ∈ H := hf.mem_toFinset.mpr ⟨L.left.greatest.1,topP⟩
  have bK : b ∈ K := kf.mem_toFinset.mpr ⟨L.right.least.1,rfl⟩
  have eK : e ∈ K := kf.mem_toFinset.mpr ⟨L.right.greatest.1,topQ⟩
  have hA : H ⊆ A := fun _ h => pf.mem_toFinset.mpr (hf.mem_toFinset.mp h).1
  have kB : K ⊆ B := fun _ h => qf.mem_toFinset.mpr (kf.mem_toFinset.mp h).1
  have pA : p ∈ A := pf.mem_toFinset.mpr L.leftLow.least.1.1
  have qB : q ∈ B := qf.mem_toFinset.mpr L.rightLow.least.1.1
  have pA' : p' ∈ A := pf.mem_toFinset.mpr L.leftLow.greatest.1.1
  have qB' : q' ∈ B := qf.mem_toFinset.mpr L.rightLow.greatest.1.1
  have pH : p ∉ H := fun h => L.leftLow.least.1.2 (hf.mem_toFinset.mp h).2
  have qK : q ∉ K := fun h => L.rightLow.least.1.2 (kf.mem_toFinset.mp h).2
  have pH' : p' ∉ H := fun h => L.leftLow.greatest.1.2 (hf.mem_toFinset.mp h).2
  have qK' : q' ∉ K := fun h => L.rightLow.greatest.1.2 (kf.mem_toFinset.mp h).2
  have da : d ≠ a := by
    intro eq
    have lo : a ≤ p := L.left.least.2 L.leftLow.least.1.1
    have hi : p ≤ d := L.left.greatest.2 L.leftLow.least.1.1
    exact pH ((show a = p by omega) ▸ aH)
  have lower : p-a = q-b := L.lower_eq
  have upper : d-p' = e-q' := L.upper_eq
  have cover (x : ℤ) (hx : x ∈ A) (y : ℤ) (hy : y ∈ B) : x+y ∈ S := by
    have mem : x+y ∈ (indepSum P Q).support := (PMF.mem_support_bind_iff _ _ _).mpr ⟨x,pf.mem_toFinset.mp hx,
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨y,qf.mem_toFinset.mp hy,(PMF.mem_support_pure_iff _ _).mpr rfl⟩⟩
    rwa [sum,PMF.support_uniformOfFinset] at mem
  have unique (x : ℤ) (hx : x ∈ H) (y : ℤ) (hy : y ∈ K) (u : ℤ) (hu : u ∈ A) (v : ℤ) (hv : v ∈ B)
      (z : x+y = u+v) : x = u ∧ y = v := by
    have xh := hf.mem_toFinset.mp hx
    have yh := kf.mem_toFinset.mp hy
    exact ((rect x xh.1 y yh.1).mpr ⟨xh.2,yh.2⟩) u (pf.mem_toFinset.mp hu) v (qf.mem_toFinset.mp hv) z
  obtain ⟨C,cs,cc,hit⟩ := singleton_totals hA kB cover unique
  let R := B.image (fun y => p+y)
  have rc : R.card = B.card := card_image_of_injective _ (fun _ _ h => add_left_cancel h)
  have rs : R ⊆ S := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
    exact cover p pA y hy
  have cr : Disjoint C R := by
    apply disjoint_left.mpr
    intro z zc zr
    obtain ⟨y,hy,rfl⟩ := mem_image.mp zr
    exact pH (((hit p pA y hy).mp zc).1)
  have ub : S.card ≤ R.card+5 := by rwa [rc,←Set.ncard_eq_toFinset_card _ qf]
  have er : d+q ∉ R := by
    intro h
    obtain ⟨y,hy,eq⟩ := mem_image.mp h
    exact da (unique d dH b bK a (hA aH) y hy (by omega)).1
  have ec : d+q ∉ C := fun h => qK (((hit d (hA dH) q qB).mp h).2)
  have outside {z : ℤ} (s : z ∈ S) (c : z ∉ C) (r : z ∉ R) : z = d+q :=
    outside_equal ub cs rs cr (cc ▸ four) s c r (cover d (hA dH) q qB) ec er
  have same : p' = p := by
    by_contra dif
    have ord : p ≤ p' := L.leftLow.least.2 L.leftLow.greatest.1
    have far : p'+e ∉ R := by
      intro h
      obtain ⟨y,hy,eq⟩ := mem_image.mp h
      have boundY : y ≤ e := L.right.greatest.2 (qf.mem_toFinset.mp hy)
      omega
    have eq := outside (cover p' pA' e (kB eK)) (fun h => pH' (((hit p' pA' e (kB eK)).mp h).1)) far
    have equal : q' = q := by omega
    exact (by have h := card_le_three qf L.right L.rightLow equal smallQ; omega)
  have far : a+q' ∉ R := by
    intro h
    obtain ⟨y,hy,eq⟩ := mem_image.mp h
    exact da ((unique a aH e eK d (hA dH) y hy (by omega)).1.symm)
  have eq := outside (cover a (hA aH) q' qB') (fun h => qK' (((hit a (hA aH) q' qB').mp h).2)) far
  refine ⟨card_le_three pf L.left L.leftLow same smallP,?_⟩
  change e-b = 2*(d-a)
  omega

open Green28PrimitiveSupport Green28AlgebraicWidth

private theorem three_term_factor {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) (few : f.support.card ≤ 3) (width : g.natDegree ≤ 2*f.natDegree) :
    Binary f ∧ Binary g := by
  classical
  by_cases fb : Binary f
  · apply rational_factor fm gm fp gp bin
    intro i
    rcases fb i with h|h
    · exact ⟨0,by simpa using h.symm⟩
    · exact ⟨1,by simpa using h.symm⟩
  unfold Binary at fb
  push Not at fb
  obtain ⟨r,nz,no⟩ := fb
  let d := f.natDegree
  have rp : 0 < r := by by_contra! h; exact no (by simpa [show r = 0 by omega] using fc)
  have rd : r < d := by
    rcases lt_trichotomy r d with h|e|h
    · exact h
    · exact (no (e ▸ fm.coeff_natDegree)).elim
    · exact (nz (coeff_eq_zero_of_natDegree_lt h)).elim
  have trip : ({0,r,d} : Finset ℕ) ⊆ f.support := by
    intro n hn
    simp only [mem_insert,mem_singleton] at hn
    rcases hn with rfl|rfl|rfl
    · exact mem_support_iff.mpr (by simp [fc])
    · exact mem_support_iff.mpr nz
    · exact mem_support_iff.mpr (by rw [fm.coeff_natDegree]; norm_num)
  have card : ({0,r,d} : Finset ℕ).card = 3 := by simp [ne_of_lt rp,ne_of_lt rd,show 0 ≠ d by omega]
  have eq := eq_of_subset_of_card_le trip (card ▸ few)
  apply binary_trinomial_of_double_width fm gm fc gc fp gp bin rp rd rfl (f.coeff r) _ width
  ext n
  rw [coeff_add,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X_pow,coeff_one]
  by_cases n0 : n = 0
  · subst n; simp [fc,show 0 ≠ r by omega,show 0 ≠ d by omega]
  by_cases nr : r = n
  · subst n; simp [rp.ne',rd.ne]
  by_cases nd : d = n
  · subst n; simp [d,fm.coeff_natDegree,show f.natDegree ≠ 0 by change d ≠ 0; omega,show f.natDegree ≠ r by exact rd.ne']
  have missing : n ∉ f.support := by rw [←eq]; simp [n0,Ne.symm nr,Ne.symm nd]
  simp [n0,Ne.symm nr,Ne.symm nd,notMem_support_iff.mp missing]

/-- Three atoms on one side suffice when the partner has width at most
twice its width. The published trinomial theorem allows an arbitrary partner. -/
theorem uniform_of_three_of_double_width {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (size : P.support.ncard ≤ 3) (width : Green28AlgebraicWidth.width Q ≤ 2*Green28AlgebraicWidth.width P) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  classical
  obtain ⟨S,ne,sum⟩ := flat
  obtain ⟨f,g,a,_,_,_,pf,pg,fm,gm,fw,gw,fc,gc,_⟩ := mask_factorization ne sum
  have chart (n : ℕ) (hn : n ∈ f.support) : a+(n:ℤ) ∈ P.support := by
    apply (P.mem_support_iff _).mpr
    intro h
    have e := pf.coeff n
    rw [h,ENNReal.toReal_zero] at e
    exact (mul_ne_zero pf.pos.ne' (mem_support_iff.mp hn)) e.symm
  have sub : f.support.image (fun n : ℕ => a+(n:ℤ)) ⊆ pf.finite.toFinset := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hx
    exact pf.finite.mem_toFinset.mpr (chart n hn)
  have card := card_le_card sub
  rw [card_image_of_injective _ (by intro i j h; dsimp at h; omega),←Set.ncard_eq_toFinset_card _ pf.finite] at card
  have bin := ((pf.mul pg).uniform_iff (fm.mul gm)).mp ⟨S,ne,sum⟩
  obtain ⟨fb,gb⟩ := three_term_factor fm gm fc gc pf.nonneg pg.nonneg bin (card.trans size)
    (by rw [gw,fw]; exact width)
  exact ⟨(pf.uniform_iff fm).mpr fb,(pg.uniform_iff gm).mpr gb⟩

private theorem oriented_boundary {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (qb : 5 < Q.support.ncard)
    (limit : S.card ≤ Q.support.ncard+5) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  rcases alignment_alternative flat with fair|w
  · exact fair
  · obtain ⟨L⟩ := w
    obtain ⟨size,width⟩ := boundary_geometry ne sum L qb limit
    obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
    rw [←width_of_extremes qf L.right,←width_of_extremes pf L.left] at width
    exact uniform_of_three_of_double_width flat size (by omega)

/-- Every counterexample to Green 28 must gain at least six output sites
over its larger marginal. -/
theorem uniform_or_six_more {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) :
    (IsUniformOnSupport P ∧ IsUniformOnSupport Q) ∨ max P.support.ncard Q.support.ncard+6 ≤ S.card := by
  by_cases enough : max P.support.ncard Q.support.ncard+6 ≤ S.card
  · exact Or.inr enough
  left
  by_cases p : P.support.ncard ≤ 5
  · by_cases q : Q.support.ncard ≤ 5
    · exact Green28FiveSiteCertificate.uniform_of_at_most_five_atoms ⟨S,ne,sum⟩ p q
    · exact oriented_boundary ne sum (by omega) (by omega)
  · rcases le_total P.support.ncard Q.support.ncard with h|h
    · exact oriented_boundary ne sum (by omega) (by omega)
    · exact (oriented_boundary ne ((indepSum_comm P Q).symm.trans sum) (by omega) (by omega)).symm

/-- Every uniform sum on at most eleven integer sites has uniform summands. -/
theorem uniform_of_eleven_outputs {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (size : S.card ≤ 11) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  rcases uniform_or_six_more ne sum with fair|many
  · exact fair
  · exact Green28FiveSiteCertificate.uniform_of_at_most_five_atoms ⟨S,ne,sum⟩ (by omega) (by omega)

private noncomputable def uniform_extremes {P : PMF ℤ} {A : Finset ℤ} (an : A.Nonempty)
    (pa : P = PMF.uniformOfFinset A an) : Extremes P.support :=
  ⟨A.min' an,A.max' an,by rw [pa,PMF.support_uniformOfFinset]; exact A.isLeast_min' an,
    by rw [pa,PMF.support_uniformOfFinset]; exact A.isGreatest_max' an⟩

/-- A prime-size uniform output with two uniform summands has a constant
summand, since every pair of occupied sites gives a distinct total. -/
theorem pure_of_prime_of_uniform {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (prime : S.card.Prime)
    (fair : IsUniformOnSupport P ∧ IsUniformOnSupport Q) :
    (∃ x, P = PMF.pure x) ∨ (∃ y, Q = PMF.pure y) := by
  classical
  obtain ⟨⟨A,an,pa⟩,⟨B,bn,qb⟩⟩ := fair
  let E := uniform_extremes an pa
  let F := uniform_extremes bn qb
  have ps : P.support = (A:Set ℤ) := by rw [pa,PMF.support_uniformOfFinset]
  have qs : Q.support = (B:Set ℤ) := by rw [qb,PMF.support_uniformOfFinset]
  have ss : (indepSum P Q).support = (S:Set ℤ) := by rw [sum,PMF.support_uniformOfFinset]
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  have unique := (maximal_rectangle flat E F).2.2
  have equal_mass {R : PMF ℤ} {T : Finset ℤ} (tn : T.Nonempty) (rt : R = PMF.uniformOfFinset T tn)
      (x y : ℤ) (hx : x ∈ T) (hy : y ∈ T) : (R x).toReal = (R y).toReal := by
    rw [rt,PMF.uniformOfFinset_apply_of_mem tn hx,PMF.uniformOfFinset_apply_of_mem tn hy]
  have site (x : ℤ) (hx : x ∈ A) := equal_mass an pa x E.lo hx (show E.lo ∈ (A:Set ℤ) from ps ▸ E.least.1)
  have site' (y : ℤ) (hy : y ∈ B) := equal_mass bn qb y F.lo hy (show F.lo ∈ (B:Set ℤ) from qs ▸ F.least.1)
  have seteq : (A ×ˢ B).image (fun z => z.1+z.2) = S := by
    ext z
    constructor
    · intro h
      obtain ⟨⟨x,y⟩,xy,rfl⟩ := mem_image.mp h
      apply (show x+y ∈ (indepSum P Q).support ↔ x+y ∈ S by rw [ss]; rfl).mp
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨x,ps ▸ (mem_product.mp xy).1,
        (PMF.mem_support_bind_iff _ _ _).mpr ⟨y,qs ▸ (mem_product.mp xy).2,(PMF.mem_support_pure_iff _ _).mpr rfl⟩⟩
    · intro h
      have mem : z ∈ (indepSum P Q).support := ss ▸ h
      obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp mem
      obtain ⟨y,hy,e⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
      exact mem_image.mpr ⟨(x,y),mem_product.mpr ⟨show x ∈ (A:Set ℤ) from ps ▸ hx,show y ∈ (B:Set ℤ) from qs ▸ hy⟩,((PMF.mem_support_pure_iff _ _).mp e).symm⟩
  have card : S.card = A.card*B.card := by
    rw [←seteq,←card_product]
    apply card_image_of_injOn
    rintro ⟨x,y⟩ xy ⟨v,w⟩ vw e
    obtain ⟨hx,hy⟩ := mem_product.mp xy
    obtain ⟨hv,hw⟩ := mem_product.mp vw
    have eq := ((unique x (ps ▸ hx) y (qs ▸ hy)).mpr ⟨site _ hx,site' _ hy⟩)
      v (ps ▸ hv) w (qs ▸ hw) e
    exact Prod.ext eq.1 eq.2
  have pure_single {R : PMF ℤ} {T : Finset ℤ} (tn : T.Nonempty) (rt : R = PMF.uniformOfFinset T tn)
      (one : T.card = 1) : ∃ x, R = PMF.pure x := by
    obtain ⟨x,rfl⟩ := card_eq_one.mp one
    refine ⟨x,PMF.ext fun y => ?_⟩
    rw [rt,PMF.uniformOfFinset_apply,PMF.pure_apply]
    simp
  rcases Nat.prime_mul_iff.mp (card ▸ prime) with h|h
  · exact Or.inr (pure_single bn qb h.2)
  · exact Or.inl (pure_single an pa h.2)

/-- In particular there is no nonconstant independent decomposition of the
uniform law on any set of exactly eleven integers. -/
theorem pure_of_eleven_outputs {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (size : S.card = 11) :
    (∃ x, P = PMF.pure x) ∨ (∃ y, Q = PMF.pure y) :=
  pure_of_prime_of_uniform ne sum (by rw [size]; decide) (uniform_of_eleven_outputs ne sum size.le)

#print axioms binary_trinomial_of_double_width
#print axioms uniform_of_three_of_double_width
#print axioms uniform_or_six_more
#print axioms uniform_of_eleven_outputs
#print axioms pure_of_prime_of_uniform
#print axioms pure_of_eleven_outputs
end Green28OutputBoundary
