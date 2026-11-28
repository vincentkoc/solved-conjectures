import Green28DeficientFibre

/-! Restrictions on a three-level marginal opposite a single deficient atom in Green 28. -/

namespace Green28ThreeLevelPartner

open Finset Green28 Green28UniformSums Green28AlgebraicWidth Green28DeficientFibre Green28UnpairedSites
open scoped ENNReal

private theorem separate {x : ℝ} (irr : ∀ q : ℚ, (q:ℝ) ≠ x) (c d : ℤ)
    (eq : (c:ℝ)+(d:ℝ)*x = 0) : c = 0 ∧ d = 0 := by
  by_cases dz : d = 0
  · subst d; simp only [Int.cast_zero,zero_mul,add_zero] at eq
    exact ⟨by exact_mod_cast eq,rfl⟩
  · exfalso
    apply irr (-(c:ℚ)/d)
    push_cast
    exact (div_eq_iff (by exact_mod_cast dz)).mpr (by linarith)

private theorem integral_coordinates {u x y : ℝ} (comp : u = 1-x) (xp : 0 < x)
    (mem : y ∈ Algebra.adjoin ℤ {u}) (A B C D : ℤ)
    (r : x*x = (A:ℝ)*x+(B:ℝ)*y) (s : x*y = (C:ℝ)*x+(D:ℝ)*y) :
    ∃ k l : ℤ, y = (k:ℝ)+(l:ℝ)*x := by
  have quad : x*x = ((A+D:ℤ):ℝ)*x+((B*C-A*D:ℤ):ℝ) := by
    apply mul_left_cancel₀ xp.ne'
    push_cast
    linear_combination x*r + (B:ℝ)*s - (D:ℝ)*r
  clear r s
  induction mem using Algebra.adjoin_induction with
  | mem v h => obtain rfl : v = u := h; exact ⟨1,-1,by simp [comp]; ring⟩
  | algebraMap z => exact ⟨z,0,by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨c,d,h⟩ := hv; obtain ⟨e,f,h'⟩ := hw
    exact ⟨c+e,d+f,by rw [h,h']; push_cast; ring⟩
  | mul v w _ _ hv hw =>
    obtain ⟨c,d,h⟩ := hv; obtain ⟨e,f,h'⟩ := hw
    refine ⟨c*e+d*f*(B*C-A*D),c*f+d*e+d*f*(A+D),?_⟩
    rw [h,h']; push_cast at quad ⊢
    linear_combination (d:ℝ)*(f:ℝ)*quad

/-- Arithmetic of three fibre equations. With two deficient values, one
complementary to the exceptional weight, the complement is a quadratic
unit, and the other deficient weight has one of two prescribed forms. -/
theorem count_classification {u x y : ℝ} (comp : u = 1-x) (xp : 0 < x) (xl : x < 1) (yp : 0 < y)
    (irr : ∀ q : ℚ, (q:ℝ) ≠ x) (mem : y ∈ Algebra.adjoin ℤ {u})
    (m n a b c e : ℕ) (mp : 0 < m) (np : 0 < n)
    (boundary : (m:ℝ)*x+n*y = 1)
    (rowX : u*x+a*x+b*y = 1) (rowY : u*y+c*x+e*y = 1) :
    n = 1 ∧ b = 0 ∧ 2 ≤ a ∧ x^2-(a+1)*x+1 = 0 ∧ y = 1-m*x ∧
      (m = a ∨ (m = 1 ∧ a = 2)) := by
  obtain ⟨k,l,h⟩ := integral_coordinates comp xp mem (1-(m:ℤ)+a) ((b:ℤ)-n)
    ((c:ℤ)-m) (1-(n:ℤ)+e)
    (by push_cast; rw [comp] at rowX; nlinarith only [boundary,rowX])
    (by push_cast; rw [comp] at rowY; nlinarith only [boundary,rowY])
  have coef := separate irr ((n:ℤ)*k-1) ((m:ℤ)+n*l) (by
    push_cast; rw [h] at boundary; linarith only [boundary])
  have nh := Int.eq_one_or_neg_one_of_mul_eq_one (show (n:ℤ)*k = 1 by omega)
  have n1 : n = 1 := by omega
  subst n
  simp only [Nat.cast_one,one_mul] at boundary
  have val : y = 1-m*x := by linarith only [boundary]
  rw [comp,val] at rowX rowY
  have quad : x^2 = ((1+(a:ℤ)-b*m:ℤ):ℝ)*x+((b:ℤ)-1:ℤ) := by
    push_cast; nlinarith only [rowX]
  have z := separate irr (((m:ℤ)*((b:ℤ)-1))+e)
    ((m:ℤ)*(1+(a:ℤ)-b*m)-m-1+c-e*m) (by
      push_cast at quad ⊢; linear_combination rowY - (m:ℝ)*quad)
  have b0 : b = 0 := by
    by_contra! bn
    have b1 : b = 1 := by
      by_contra! nb
      have hi : 0<(m:ℤ)*((b:ℤ)-1) := mul_pos (by omega) (by omega)
      omega
    rw [b1] at quad
    simp only [Nat.cast_one,sub_self,Int.cast_zero,add_zero] at quad
    have eq : (((1+(a:ℤ)-1*m:ℤ):ℝ)) = x := by
      apply mul_left_cancel₀ xp.ne'
      nlinarith only [quad]
    exact irr ((1+(a:ℤ)-1*m:ℤ):ℚ) (by exact_mod_cast eq)
  subst b
  push_cast at quad
  simp only [Nat.cast_zero,zero_mul,sub_zero,zero_sub] at quad z
  have poly : x^2-(a+1)*x+1 = 0 := by nlinarith only [quad]
  have a2 : 2 ≤ a := by
    by_contra! small
    have aa : (a:ℝ) ≤ 1 := by exact_mod_cast (show a ≤ 1 by omega)
    nlinarith [mul_le_mul_of_nonneg_right aa xp.le,sq_pos_of_pos (sub_pos.mpr xl)]
  refine ⟨rfl,rfl,a2,poly,val,?_⟩
  have am : m ≤ a := by
    by_contra! gt
    have hma : (a:ℝ)+1 ≤ m := by exact_mod_cast (show a+1 ≤ m by omega)
    nlinarith [mul_le_mul_of_nonneg_right hma xp.le,sq_nonneg x]
  have E : (e:ℤ) = m := by omega
  have cnt : (m:ℤ)*((a:ℤ)-m) ≤ 1 := by
    obtain ⟨_,hz⟩ := z
    rw [E] at hz
    nlinarith only [hz,Int.natCast_nonneg c]
  by_cases eq : m = a
  · exact Or.inl eq
  · right
    have one : (1:ℤ) ≤ (a:ℤ)-m := by omega
    have small := mul_le_mul_of_nonneg_left one (Int.natCast_nonneg m)
    have m1 : m = 1 := by omega
    subst m
    simp only [Nat.cast_one,one_mul] at cnt
    exact ⟨rfl,by omega⟩

private theorem atom_pos {P : PMF ℤ} {i : ℤ} (hi : i ∈ P.support) : 0<(P i).toReal :=
  ENNReal.toReal_pos ((P.mem_support_iff _).mp hi) (P.apply_ne_top _)

private theorem low_weight {P : PMF ℤ} {a : ℤ} (top : IsGreatest P.support a)
    (ep : EndpointWeights P) {v : ℝ} (hv : v ∈ deficientWeights P a) :
    0 < v ∧ v < 1 ∧ ∀ q : ℚ, (q:ℝ) ≠ v := by
  obtain ⟨i,hi,lt,rfl⟩ := hv
  obtain ⟨b,hb,le,h⟩ := ep
  obtain rfl := top.unique (show IsGreatest P.support b from ⟨hb,le⟩)
  have pos : 0 < weight P a i := div_pos (atom_pos hi) (atom_pos top.1)
  have small : weight P a i < 1 := (div_lt_one (atom_pos top.1)).mpr lt
  exact ⟨pos,small,fun q eq => ((h i).2.2.2 ⟨q,eq⟩).elim pos.ne' small.ne⟩

private theorem complementary_site {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q)) (w : Boundary P Q) :
    1-weight Q w.b w.d ∈ deficientWeights P w.a := by
  classical
  obtain ⟨al⟩ := (alignment_alternative flat).resolve_left bad
  have pa := al.left.greatest.unique w.topP
  have qb := al.right.greatest.unique w.topQ
  obtain ⟨pends,qends,_⟩ := maximal_rectangle flat al.left al.right
  rw [pa] at pends; rw [qb] at qends
  have right : al.rightLow.lo = w.d := by
    by_contra ne
    have val := w.other _ al.rightLow.least.1.1 ne
    exact al.rightLow.least.1.2 (val.trans qends)
  obtain ⟨E,rows,eq⟩ := deficient_remainder flat w al.left.least.1
  have corner : weight P w.a al.left.lo = 1 := by
    rw [weight,←pends,div_self (atom_pos w.topP.1).ne']
  rw [corner,mul_one] at eq
  have same (i : ℤ) (hi : i ∈ E) : i = al.leftLow.lo := by
    obtain ⟨_,pi,qi,small⟩ := rows i hi
    have lo := al.leftLow.least.2 (show i ∈ lowerSites P al.left.lo from
      ⟨pi,fun h => small.ne (h.trans pends.symm)⟩)
    have rhs := al.right.least.2 qi
    have offset := al.lower_eq
    rw [right] at offset
    omega
  have live : E.Nonempty := by
    by_contra! z
    rw [z,sum_empty,add_zero] at eq
    exact (div_lt_one (atom_pos w.topQ.1)).mpr w.deficient |>.ne eq
  obtain ⟨i,hi⟩ := live
  have sing : E = {i} := eq_singleton_iff_unique_mem.mpr ⟨hi,fun j hj => (same j hj).trans (same i hi).symm⟩
  rw [sing,sum_singleton] at eq
  exact ⟨i,(rows i hi).2.1,(rows i hi).2.2.2,by linarith only [eq]⟩

private theorem boundary_sum {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q)) (w : Boundary P Q) :
    ∃ E : Finset ℤ, (∀ i ∈ E, weight P w.a i ∈ deficientWeights P w.a) ∧
      (∑ i ∈ E,weight P w.a i) = 1 := by
  obtain ⟨a,top,E,_,low,eq⟩ := subset_mass_of_one_deficit flat one bad
  obtain rfl := top.unique w.topP
  exact ⟨E,fun i hi => ⟨i,(low i hi).1,(low i hi).2,rfl⟩,by
    simp only [weight,←sum_div,eq,div_self (atom_pos w.topP.1).ne']⟩

private theorem palette {P : PMF ℤ} (pf : P.support.Finite) (three : massLevels P ≤ 3)
    {a : ℤ} (top : IsGreatest P.support a) {x y : ℝ}
    (hx : x ∈ deficientWeights P a) (hy : y ∈ deficientWeights P a) (ne : x ≠ y) :
    ∀ t ∈ deficientWeights P a, t = x ∨ t = y := by
  classical
  let F := (pf.image fun i : ℤ => (P i).toReal).toFinset
  let S := F.image (fun z : ℝ => z/(P a).toReal)
  have fc : F.card = massLevels P := (Set.ncard_eq_toFinset_card _ _).symm
  have size : S.card ≤ 3 := card_image_le.trans (fc ▸ three)
  have inc {i : ℤ} (hi : i ∈ P.support) : weight P a i ∈ S :=
    mem_image.mpr ⟨(P i).toReal,(pf.image _).mem_toFinset.mpr ⟨i,hi,rfl⟩,rfl⟩
  have inclow {t : ℝ} (h : t ∈ deficientWeights P a) : t ∈ S ∧ t < 1 := by
    obtain ⟨i,hi,lt,rfl⟩ := h
    exact ⟨inc hi,(div_lt_one (atom_pos top.1)).mpr lt⟩
  have one : (1:ℝ) ∈ S := by simpa only [weight,div_self (atom_pos top.1).ne'] using inc top.1
  have xi := inclow hx; have yi := inclow hy
  have sub : ({1,x,y}:Finset ℝ) ⊆ S := by simpa only [insert_subset_iff,singleton_subset_iff] using
    (show 1 ∈ S ∧ x ∈ S ∧ y ∈ S from ⟨one,xi.1,yi.1⟩)
  have card : ({1,x,y}:Finset ℝ).card = 3 := by simp [ne,xi.2.ne',yi.2.ne']
  have eq := Finset.eq_of_subset_of_card_le sub (card ▸ size)
  intro t ht
  obtain ⟨tm,lt⟩ := inclow ht
  rw [←eq] at tm
  simpa only [mem_insert,mem_singleton,lt.ne,false_or] using tm

private theorem counts (E : Finset ℤ) (f : ℤ→ℝ) (x y : ℝ)
    (h : ∀ i ∈ E, f i = x ∨ f i = y) : ∃ a b : ℕ,
    (∑ i ∈ E,f i) = (a:ℝ)*x+b*y ∧ a ≤ E.card ∧ (b = 0 → ∀ i ∈ E, f i = x) := by
  classical
  let A := E.filter fun i => f i = x
  let B := E.filter fun i => f i ≠ x
  refine ⟨A.card,B.card,?_,card_le_card (filter_subset _ _),?_⟩
  · rw [←sum_filter_add_sum_filter_not E (fun i => f i = x)]
    have sA : (∑ i ∈ A,f i) = A.card • x := sum_eq_card_nsmul fun i hi => (mem_filter.mp hi).2
    have sB : (∑ i ∈ B,f i) = B.card • y := sum_eq_card_nsmul fun i hi =>
      (h i (mem_filter.mp hi).1).resolve_left (mem_filter.mp hi).2
    simpa only [nsmul_eq_mul] using congrArg₂ (·+·) sA sB
  · intro bz i hi
    by_contra neq
    have bi : i ∈ B := mem_filter.mpr ⟨hi,neq⟩
    exact (card_pos.mpr ⟨i,bi⟩).ne' bz

/-- A nonuniform three-level partner would have exactly two deficient weights.
Each row of the complementary weight must collide with at least `k` distinct
other rows of that same weight when paired with the exceptional column. -/
structure ThreeLevelData (P Q : PMF ℤ) (w : Boundary P Q) where
  x : ℝ
  y : ℝ
  k : ℕ
  two : 2 ≤ k
  xmem : x ∈ deficientWeights P w.a
  ymem : y ∈ deficientWeights P w.a
  different : x ≠ y
  only : ∀ t ∈ deficientWeights P w.a, t = x ∨ t = y
  complement : weight Q w.b w.d = 1-x
  quadratic : x^2-(k+1)*x+1 = 0
  other : y = 1-k*x ∨ (k = 2 ∧ y = 1-x)
  neighbours : ∀ i ∈ P.support, weight P w.a i = x → ∃ E : Finset ℤ, k ≤ E.card ∧
    ∀ j ∈ E, j ≠ i ∧ j ∈ P.support ∧ weight P w.a j = x ∧ i+w.d-j ∈ Q.support

/-- Necessary quadratic-unit and spatial conditions on the actual integer laws. -/
theorem three_level_data {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q))
    (three : massLevels P ≤ 3) (w : Boundary P Q) : Nonempty (ThreeLevelData P Q w) := by
  classical
  let u := weight Q w.b w.d
  let x := 1-u
  have comp : u = 1-x := by dsimp [x]; ring
  have xm : x ∈ deficientWeights P w.a := complementary_site flat bad w
  have ep := (endpoint_weights flat).1
  obtain ⟨xp,xl,irr⟩ := low_weight w.topP ep xm
  obtain ⟨S,sl,eq⟩ := boundary_sum flat one bad w
  have second : ∃ y ∈ deficientWeights P w.a, x ≠ y := by
    by_contra! all
    have e := sum_eq_card_nsmul (s := S) (b := x) (fun i hi => (all _ (sl i hi)).symm)
    rw [eq,nsmul_eq_mul] at e
    have ne : (S.card:ℝ) ≠ 0 := fun z => by rw [z,zero_mul] at e; exact one_ne_zero e
    apply irr (S.card:ℚ)⁻¹
    push_cast
    field_simp [ne]; linarith only [e]
  obtain ⟨y,ym,diff⟩ := second
  have colors := palette (finite_of_uniform_sum flat).1 three w.topP xm ym diff
  obtain ⟨yp,_,yirr⟩ := low_weight w.topP ep ym
  obtain ⟨m,n,rs,_,_⟩ := counts S (weight P w.a) x y (fun i h => colors _ (sl i h))
  rw [eq] at rs
  have nonzero (t : ℝ) (no : ∀ q : ℚ, (q:ℝ) ≠ t) (b : ℕ) (h : 1 = (b:ℝ)*t) : False := by
    have bn : (b:ℝ) ≠ 0 := fun z => by rw [z,zero_mul] at h; exact one_ne_zero h
    apply no (b:ℚ)⁻¹
    push_cast; field_simp [bn]; linarith only [h]
  have mp : 0 < m := by
    by_contra! z
    obtain rfl : m = 0 := by omega
    exact nonzero y yirr n (by simpa using rs)
  have np : 0 < n := by
    by_contra! z
    obtain rfl : n = 0 := by omega
    exact nonzero x irr m (by simpa using rs)
  have mem : y ∈ Algebra.adjoin ℤ {u} := by
    have inc : y ∈ Submodule.span ℤ (deficientWeights P w.a) := Submodule.subset_span ym
    rw [deficient_integer_span flat one bad w] at inc
    exact inc
  obtain ⟨j,jp,jl,jw⟩ := ym
  obtain ⟨F,fr,fy⟩ := deficient_remainder flat w jp
  obtain ⟨c,e,fv,_,_⟩ := counts F (weight P w.a) x y (fun i hi =>
    colors _ ⟨i,(fr i hi).2.1,(fr i hi).2.2.2,rfl⟩)
  rw [jw,fv] at fy
  have row (i : ℤ) (ip : i ∈ P.support) (wi : weight P w.a i = x) :
      ∃ a : ℕ, 2 ≤ a ∧ x^2-(a+1)*x+1 = 0 ∧ (y = 1-a*x ∨ (a = 2 ∧ y = 1-x)) ∧
        ∃ E : Finset ℤ, a ≤ E.card ∧ ∀ j ∈ E, j ≠ i ∧ j ∈ P.support ∧ weight P w.a j = x ∧ i+w.d-j ∈ Q.support := by
    obtain ⟨E,er,f⟩ := deficient_remainder flat w ip
    obtain ⟨a,b,ev,sz,zero⟩ := counts E (weight P w.a) x y (fun j hj =>
      colors _ ⟨j,(er j hj).2.1,(er j hj).2.2.2,rfl⟩)
    rw [wi,ev] at f
    obtain ⟨_,b0,a2,quad,yval,mval⟩ := count_classification comp xp xl yp irr mem m n a b c e mp np
      rs.symm (by dsimp only [u]; linarith only [f]) (by dsimp only [u]; linarith only [fy])
    refine ⟨a,a2,quad,?_,E,sz,fun j hj => ⟨(er j hj).1,(er j hj).2.1,zero b0 j hj,(er j hj).2.2.1⟩⟩
    rcases mval with rfl|⟨rfl,rfl⟩
    · exact Or.inl yval
    · exact Or.inr ⟨rfl,by simpa using yval⟩
  obtain ⟨i,ip,il,iw⟩ := xm
  obtain ⟨k,k2,poly,yval,_⟩ := row _ ip iw
  refine ⟨⟨x,y,k,k2,⟨i,ip,il,iw⟩,
    ⟨j,jp,jl,jw⟩,
    diff,colors,comp,poly,yval,?_⟩⟩
  intro z hz zw
  obtain ⟨a,_,p,_,ex⟩ := row _ hz zw
  have same : (a:ℝ) = k := by apply mul_left_cancel₀ xp.ne'; nlinarith only [p,poly]
  exact (show a = k by exact_mod_cast same) ▸ ex

/-- There are at least `k` occupied columns strictly on each side of the
exceptional site. The count uses the extreme rows of weight `x`. -/
theorem flank_sizes {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {w : Boundary P Q} (h : ThreeLevelData P Q w) :
    h.k ≤ (Q.support ∩ Set.Iio w.d).ncard ∧ h.k ≤ (Q.support ∩ Set.Ioi w.d).ncard := by
  classical
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  let X := pf.toFinset.filter fun i => weight P w.a i = h.x
  have spec {i : ℤ} : i ∈ X ↔ i ∈ P.support ∧ weight P w.a i = h.x := by simp [X]
  obtain ⟨i,ip,_,iw⟩ := h.xmem
  have live : X.Nonempty := ⟨i,spec.mpr ⟨ip,iw⟩⟩
  have side {r : ℤ} (hr : r ∈ X) (T : Set ℤ) (ht : T.Finite)
      (inside : ∀ j ∈ X, j ≠ r → r+w.d-j ∈ Q.support → r+w.d-j ∈ T) :
      h.k ≤ T.ncard := by
    obtain ⟨E,sz,neigh⟩ := h.neighbours _ (spec.mp hr).1 (spec.mp hr).2
    let shift (j : ℤ) := r+w.d-j
    have inj : Function.Injective shift := by intro j l e; dsimp [shift] at e; omega
    have inc : E.image shift ⊆ ht.toFinset := by
      intro j hj; obtain ⟨l,hl,rfl⟩ := mem_image.mp hj
      obtain ⟨ne,pl,wl,ql⟩ := neigh l hl
      exact ht.mem_toFinset.mpr (inside l (spec.mpr ⟨pl,wl⟩) ne ql)
    have cnt := card_le_card inc
    rw [card_image_of_injective _ inj,←Set.ncard_eq_toFinset_card T ht] at cnt
    exact sz.trans cnt
  constructor
  · apply side (X.min'_mem live) _ (qf.inter_of_left _)
    intro j hj ne q
    exact ⟨q,by apply Set.mem_Iio.mpr; have := X.min'_le j hj; omega⟩
  · apply side (X.max'_mem live) _ (qf.inter_of_left _)
    intro j hj ne q
    exact ⟨q,by apply Set.mem_Ioi.mpr; have := X.le_max' j hj; omega⟩

/-- If the unique possible deficient atom has at most one occupied neighbour
strictly on either the left or the right, a three-level partner must be uniform. -/
theorem uniform_of_edge_deficit {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (three : massLevels P ≤ 3)
    (edge : ∀ d ∈ Q.support, (∃ j, Q d < Q j) →
      (Q.support ∩ Set.Iio d).ncard ≤ 1 ∨ (Q.support ∩ Set.Ioi d).ncard ≤ 1) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  by_contra bad
  obtain ⟨w⟩ := boundary_of_one_deficit flat one bad
  obtain ⟨data⟩ := three_level_data flat one bad three w
  obtain ⟨l,r⟩ := flank_sizes flat data
  have two := data.two
  have small := edge w.d w.lowQ ⟨w.b,(ENNReal.toReal_lt_toReal (Q.apply_ne_top _) (Q.apply_ne_top _)).mp w.deficient⟩
  omega

/-- A four-site marginal with at most one deficient atom may be paired with a
marginal of arbitrary size taking at most three different positive values. -/
theorem uniform_of_four_sites {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (three : massLevels P ≤ 3) (four : Q.support.ncard ≤ 4) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  classical
  obtain ⟨_,qf⟩ := finite_of_uniform_sum flat
  apply uniform_of_edge_deficit flat one three
  intro d hd _
  let L := qf.toFinset.filter fun j => j < d
  let R := qf.toFinset.filter fun j => d < j
  have dis : Disjoint L R := disjoint_left.mpr (fun {_} l r => (mem_filter.mp l).2.not_gt (mem_filter.mp r).2)
  have off : d ∉ L∪R := by simp [L,R]
  have inc : insert d (L∪R) ⊆ qf.toFinset := insert_subset (qf.mem_toFinset.mpr hd)
    (union_subset (filter_subset _ _) (filter_subset _ _))
  have size := card_le_card inc
  rw [card_insert_of_notMem off,card_union_of_disjoint dis,←Set.ncard_eq_toFinset_card Q.support qf] at size
  have lc : (Q.support ∩ Set.Iio d).ncard = L.card := by
    rw [←Set.ncard_coe_finset]; congr 1; ext; simp [L]
  have rc : (Q.support ∩ Set.Ioi d).ncard = R.card := by
    rw [←Set.ncard_coe_finset]; congr 1; ext; simp [R]
  rw [lc,rc]; omega

/-- The exceptional ratio must be at least the positive root of
`u²+u = 1` whenever a three-level opposite law fails to be uniform. -/
theorem uniform_of_small_exception {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (three : massLevels P ≤ 3)
    (small : ∀ b, IsGreatest Q.support b → ∀ d ∈ Q.support, (Q d).toReal<(Q b).toReal →
      (weight Q b d)^2+weight Q b d < 1) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  by_contra bad
  obtain ⟨w⟩ := boundary_of_one_deficit flat one bad
  obtain ⟨h⟩ := three_level_data flat one bad three w
  have low := small _ w.topQ _ w.lowQ w.deficient
  rw [h.complement] at low
  have k : (2:ℝ) ≤ h.k := by exact_mod_cast h.two
  have xp := (low_weight w.topP (endpoint_weights flat).1 h.xmem).1
  nlinarith only [low,h.quadratic,mul_le_mul_of_nonneg_right k xp.le]

#print axioms count_classification
#print axioms three_level_data
#print axioms flank_sizes
#print axioms uniform_of_edge_deficit
#print axioms uniform_of_four_sites
#print axioms uniform_of_small_exception
end Green28ThreeLevelPartner
