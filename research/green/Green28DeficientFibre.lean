import Green28UnpairedSites
import Green28TwoMassLevels

/-! A fibre supported on deficient partner atoms for an independent sum
with a single deficient atom in one input. -/

namespace Green28DeficientFibre

open scoped ENNReal Polynomial

open Finset Green28 Green28UniformSums Green28UnpairedSites Green28AlgebraicWidth

/-- On a finite set of integer rows, some low row must have a step leaving
the support if every low row has a low predecessor and every step from a
high row leaves. A positive allowed step suffices. -/
theorem exists_leaving_step {S L C : Finset ℤ} (live : L.Nonempty)
    {c : ℤ} (step : c ∈ C) (pos : 0 < c)
    (pre : ∀ x ∈ L, ∃ z ∈ L, ∃ t ∈ C, z+t = x)
    (exit : ∀ x ∈ S, x ∉ L → ∀ t ∈ C, x+t ∉ S) :
    ∃ x ∈ L, ∃ t ∈ C, x+t ∉ S := by
  by_contra! closed
  have swap (z : ℤ) (zl : z ∈ L) (t : ℤ) (tc : t ∈ C) (next : z+t ∈ L) : z+c ∈ L := by
    by_contra high
    exact exit (z+c) (closed z zl c step) high t tc
      (by simpa [add_right_comm] using closed _ next c step)
  have run (n : ℕ) : ∃ x : ℤ, ∀ j : ℕ, j ≤ n → x+(j:ℤ)*c ∈ L := by
    induction n with
    | zero =>
      obtain ⟨x,hx⟩ := live
      refine ⟨x,?_⟩
      intro j h
      have eq : j = 0 := by omega
      simpa [eq] using hx
    | succ n ih =>
      obtain ⟨x,path⟩ := ih
      obtain ⟨z,zl,t,tc,zt⟩ := pre x (by simpa using path 0 (Nat.zero_le _))
      refine ⟨z,?_⟩
      intro j
      induction j with
      | zero => intro _; simpa using zl
      | succ j h =>
        intro bound
        have last : z+(j:ℤ)*c+t ∈ L := by
          rw [add_right_comm,zt]
          exact path j (by omega)
        have use := swap _ (h (by omega)) t tc last
        simpa [Nat.cast_succ,add_mul,add_assoc] using use
  let lo := L.min' live
  let hi := L.max' live
  let n := (hi-lo+1).toNat
  obtain ⟨x,path⟩ := run n
  have xlo : lo ≤ x := L.min'_le _ (by simpa using path 0 (Nat.zero_le _))
  have xhi : x+(n:ℤ)*c ≤ hi := L.le_max' _ (path n le_rfl)
  have large : (n:ℤ) ≤ (n:ℤ)*c := by
    simpa using mul_le_mul_of_nonneg_left (show 1 ≤ c by omega) (Int.natCast_nonneg n)
  dsimp [n] at xhi large
  omega

/-- If the column side of a singleton rectangle misses just one column,
there is an occupied sum all of whose rows are outside the rectangle and
all of whose columns are in it. -/
theorem deficient_fibre {A B L : Finset ℤ} {d b : ℤ} (ls : L ⊆ A) (live : L.Nonempty)
    (dm : d ∈ B) (bm : b ∈ B) (db : d < b)
    (rect : ∀ x ∈ A, ∀ y ∈ B, (∀ i ∈ A, ∀ j ∈ B, x+y = i+j → x = i ∧ y = j) ↔ x ∉ L ∧ y ≠ d) :
    ∃ z : ℤ, (∃ x ∈ A, z-x ∈ B) ∧ ∀ x ∈ A, z-x ∈ B → x ∈ L ∧ z-x ≠ d := by
  classical
  let C := (B.erase d).image (fun y => y-d)
  have mk {y : ℤ} (hy : y ∈ B) (ne : y ≠ d) : y-d ∈ C := mem_image.mpr ⟨y,mem_erase.mpr ⟨ne,hy⟩,rfl⟩
  have pre (x : ℤ) (xl : x ∈ L) : ∃ i ∈ L, ∃ t ∈ C, i+t = x := by
    have no := mt (rect x (ls xl) d dm).mp (by simp)
    push Not at no
    obtain ⟨i,ia,j,jb,eq,ne⟩ := no
    have jd : j ≠ d := by rintro rfl; exact ne (by omega) rfl
    have il : i ∈ L := by
      by_contra high
      exact jd (((rect i ia j jb).mpr ⟨high,jd⟩) x (ls xl) d dm eq.symm).2
    exact ⟨i,il,j-d,mk jb jd,by omega⟩
  have outside (x : ℤ) (xa : x ∈ A) (xh : x ∉ L) (t : ℤ) (tc : t ∈ C) : x+t ∉ A := by
    obtain ⟨y,ym,rfl⟩ := mem_image.mp tc
    obtain ⟨ne,yb⟩ := mem_erase.mp ym
    intro hit
    exact ne (((rect x xa y yb).mpr ⟨xh,ne⟩) _ hit d dm (by omega)).2
  obtain ⟨x,xl,t,tc,miss⟩ := exists_leaving_step live (mk bm db.ne.symm) (by omega) pre outside
  obtain ⟨y,ym,rfl⟩ := mem_image.mp tc
  obtain ⟨yd,yb⟩ := mem_erase.mp ym
  refine ⟨x+y,⟨x,ls xl,by simpa using yb⟩,?_⟩
  intro i ia jb
  have jd : x+y-i ≠ d := fun h => miss (by rwa [show x+(y-d) = i by omega])
  refine ⟨?_,jd⟩
  by_contra ih
  have eq := ((rect i ia _ jb).mpr ⟨ih,jd⟩) x (ls xl) y yb (by omega)
  exact ih (eq.1 ▸ xl)

/-- A sum whose distinct contributing rows all have below-maximum mass,
while every contributing column has the maximum column mass. -/
structure Boundary (P Q : PMF ℤ) where
  a : ℤ
  b : ℤ
  d : ℤ
  z : ℤ
  topP : IsGreatest P.support a
  topQ : IsGreatest Q.support b
  lowQ : d ∈ Q.support
  deficient : (Q d).toReal<(Q b).toReal
  other : ∀ j ∈ Q.support, j ≠ d → (Q j).toReal = (Q b).toReal
  occupied : ∃ x ∈ P.support, z-x ∈ Q.support
  rows : ∀ x ∈ P.support, z-x ∈ Q.support → (P x).toReal<(P a).toReal ∧ z-x ≠ d

private theorem data_at_top {P : PMF ℤ} (endpoint : EndpointWeights P) {e : ℤ}
    (top : IsGreatest P.support e) : ∀ x : ℤ,
    (P x).toReal ≤ (P e).toReal ∧
    ((∃ q : ℚ, (q:ℝ) = (P x).toReal/(P e).toReal) →
      (P x).toReal/(P e).toReal = 0 ∨ (P x).toReal/(P e).toReal = 1) := by
  obtain ⟨b,hb,le,weights⟩ := endpoint
  obtain rfl := top.unique (show IsGreatest P.support b from ⟨hb,le⟩)
  have pos := ENNReal.toReal_pos ((P.mem_support_iff _).mp top.1) (P.apply_ne_top _)
  intro x
  obtain ⟨_,ub,_,rat⟩ := weights x
  exact ⟨by simpa using (div_le_iff₀ pos).mp ub,rat⟩

/-- One deficient column in any failure forces an entire occupied fibre
of deficient rows and maximal columns. -/
theorem boundary_of_one_deficit {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q)) :
    Nonempty (Boundary P Q) := by
  classical
  obtain ⟨al⟩ := (alignment_alternative flat).resolve_left bad
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  obtain ⟨pt,qt,rect⟩ := maximal_rectangle flat al.left al.right
  obtain ⟨pe,qe⟩ := endpoint_weights flat
  have pb := data_at_top pe al.left.greatest
  have qb := data_at_top qe al.right.greatest
  let d := al.rightLow.lo
  have ld : d ∈ lowerSites Q al.right.lo := al.rightLow.least.1
  have dl : (Q d).toReal<(Q al.right.hi).toReal :=
    lt_of_le_of_ne (qb d).1 (fun e => ld.2 (e.trans qt))
  have below : d < al.right.hi := lt_of_le_of_ne (al.right.greatest.2 ld.1) (fun e => dl.ne (e ▸ rfl))
  obtain ⟨r,only⟩ := one
  have rd : d = r := only d ld.1 ⟨_,(ENNReal.toReal_lt_toReal (Q.apply_ne_top _) (Q.apply_ne_top _)).mp dl⟩
  have other (j : ℤ) (jq : j ∈ Q.support) (ne : j ≠ d) : (Q j).toReal = (Q al.right.hi).toReal := by
    by_contra diff
    have lt := lt_of_le_of_ne (qb j).1 diff
    exact ne ((only j jq ⟨_,(ENNReal.toReal_lt_toReal (Q.apply_ne_top _) (Q.apply_ne_top _)).mp lt⟩).trans rd.symm)
  let L := pf.toFinset.filter fun x => (P x).toReal ≠ (P al.left.lo).toReal
  have lm {x : ℤ} : x ∈ L ↔ x ∈ P.support ∧ (P x).toReal ≠ (P al.left.lo).toReal := by
    simp only [L,mem_filter,pf.mem_toFinset]
  have live : L.Nonempty := ⟨al.leftLow.lo,lm.mpr al.leftLow.least.1⟩
  have test (x) (hx : x ∈ pf.toFinset) (y) (hy : y ∈ qf.toFinset) :
      (∀ i ∈ pf.toFinset, ∀ j ∈ qf.toFinset, x+y = i+j → x = i ∧ y = j) ↔ x ∉ L ∧ y ≠ d := by
    simp only [pf.mem_toFinset,qf.mem_toFinset,rect x (pf.mem_toFinset.mp hx) y (qf.mem_toFinset.mp hy),
      lm,pf.mem_toFinset.mp hx,true_and,not_not]
    constructor
    · rintro ⟨v,w⟩; exact ⟨v,fun h => ld.2 (h ▸ w)⟩
    · rintro ⟨v,w⟩; exact ⟨v,(other y (qf.mem_toFinset.mp hy) w).trans qt⟩
  obtain ⟨z,occ,rows⟩ := deficient_fibre (filter_subset _ _ : L ⊆ pf.toFinset) live
    (qf.mem_toFinset.mpr ld.1) (qf.mem_toFinset.mpr al.right.greatest.1) below test
  refine ⟨⟨al.left.hi,al.right.hi,d,z,al.left.greatest,al.right.greatest,ld.1,dl,other,?_,?_⟩⟩
  · simpa only [pf.mem_toFinset,qf.mem_toFinset] using occ
  · intro x hx hy
    obtain ⟨low,ne⟩ := rows x (pf.mem_toFinset.mpr hx) (qf.mem_toFinset.mpr hy)
    exact ⟨lt_of_le_of_ne (pb x).1 (fun e => (lm.mp low).2 (e.trans pt)),ne⟩

/-- On every occupied sum the real convolution equals the product of the two endpoint probabilities. -/
theorem sum_at_occupied {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (pf : P.support.Finite) {a b : ℤ} (pa : IsGreatest P.support a) (qb : IsGreatest Q.support b)
    {y : ℤ} (occ : ∃ x ∈ P.support, y-x ∈ Q.support) :
    (∑ x ∈ pf.toFinset,(P x).toReal*(Q (y-x)).toReal) = (P a).toReal*(Q b).toReal := by
  obtain ⟨U,un,hU⟩ := flat
  have entry (i : ℤ) (pi : i ∈ P.support) (j : ℤ) (qj : j ∈ Q.support) :
      indepSum P Q (i+j) = (U.card:ℝ≥0∞)⁻¹ := by
    have mem : i+j ∈ (indepSum P Q).support := (PMF.mem_support_bind_iff _ _ _).mpr ⟨i,pi,
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨j,qj,(PMF.mem_support_pure_iff _ _).mpr rfl⟩⟩
    rw [hU,PMF.support_uniformOfFinset] at mem
    rw [hU,PMF.uniformOfFinset_apply_of_mem un mem]
  obtain ⟨i,hi,hj⟩ := occ
  have eq := (entry i hi (y-i) hj).trans (entry a pa.1 b qb.1).symm
  rw [show i+(y-i) = y by omega] at eq
  rw [←sum_coeff P Q _ pf,eq,sum_coeff P Q _ pf,sum_eq_single a]
  · simp
  · intro x hx ne
    have le := pa.2 (pf.mem_toFinset.mp hx)
    have off : a+b-x ∉ Q.support := fun h => by have := qb.2 h; omega
    simp [(Q.apply_eq_zero_iff _).mpr off]
  · exact fun h => (h (pf.mem_toFinset.mpr pa.1)).elim

/-- In a nonuniform decomposition with one deficient column, a nonempty
set of distinct below-maximum row masses sums to the maximal row mass. -/
theorem subset_mass_of_one_deficit {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q)) :
    ∃ a : ℤ, IsGreatest P.support a ∧ ∃ E : Finset ℤ, E.Nonempty ∧
      (∀ x ∈ E, x ∈ P.support ∧ (P x).toReal<(P a).toReal) ∧
      ∑ x ∈ E,(P x).toReal = (P a).toReal := by
  classical
  obtain ⟨w⟩ := boundary_of_one_deficit flat one bad
  obtain ⟨pf,_⟩ := finite_of_uniform_sum flat
  let E := pf.toFinset.filter fun x => w.z-x ∈ Q.support
  have em {x : ℤ} : x ∈ E ↔ x ∈ P.support ∧ w.z-x ∈ Q.support := by simp [E]
  obtain ⟨x,px,qx⟩ := w.occupied
  refine ⟨w.a,w.topP,E,⟨x,em.mpr ⟨px,qx⟩⟩,fun y hy =>
    ⟨(em.mp hy).1,(w.rows y (em.mp hy).1 (em.mp hy).2).1⟩,?_⟩
  have total := sum_at_occupied flat pf w.topP w.topQ w.occupied
  have restrict : (∑ x ∈ E,(P x).toReal*(Q (w.z-x)).toReal)=
      ∑ x ∈ pf.toFinset,(P x).toReal*(Q (w.z-x)).toReal := by
    apply sum_subset (filter_subset _ _)
    intro j hj off
    have absent : w.z-j ∉ Q.support := fun h => off (em.mpr ⟨pf.mem_toFinset.mp hj,h⟩)
    simp [(Q.apply_eq_zero_iff _).mpr absent]
  apply mul_right_cancel₀ (ENNReal.toReal_pos ((Q.mem_support_iff _).mp w.topQ.1) (Q.apply_ne_top _)).ne'
  rw [sum_mul,←total,←restrict]
  apply sum_congr rfl
  intro j hj
  obtain ⟨pj,qj⟩ := em.mp hj
  rw [w.other _ qj (w.rows _ pj qj).2]

/-- The below-maximum positive atom probabilities are pairwise rationally
proportional, with the maximum taken at the rightmost support point. -/
def CommensurableDeficits (P : PMF ℤ) : Prop :=
  ∀ a : ℤ, IsGreatest P.support a → ∀ x ∈ P.support, ∀ y ∈ P.support,
    (P x).toReal<(P a).toReal → (P y).toReal<(P a).toReal →
    ∃ q : ℚ, (P x).toReal = (q:ℝ)*(P y).toReal

/-- One deficient atom on one side and commensurable deficient masses
on the other suffice, without width, cardinality or gap restrictions. -/
theorem uniform_of_commensurable_deficits {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (comm : CommensurableDeficits P) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  classical
  by_contra bad
  obtain ⟨a,top,E,⟨y,yE⟩,low,eq⟩ := subset_mass_of_one_deficit flat one bad
  obtain ⟨yp,yl⟩ := low y yE
  have yp' := ENNReal.toReal_pos ((P.mem_support_iff _).mp yp) (P.apply_ne_top _)
  have ap := ENNReal.toReal_pos ((P.mem_support_iff _).mp top.1) (P.apply_ne_top _)
  choose q hq using fun x (hx : x ∈ E) => comm a top x (low x hx).1 y yp (low x hx).2 yl
  let c : ℚ := ∑ x ∈ E.attach, q x.val x.property
  have sc : (c:ℝ)*(P y).toReal = (P a).toReal := by
    change (↑(∑ x ∈ E.attach,q x.val x.property):ℝ)*(P y).toReal = (P a).toReal
    push_cast
    rw [sum_mul,←eq,←Finset.sum_attach E (fun i => (P i).toReal)]
    exact sum_congr rfl (fun i _ => (hq i.val i.property).symm)
  have rat : (↑c⁻¹:ℝ) = (P y).toReal/(P a).toReal := by
    push_cast
    have cn : (c:ℝ) ≠ 0 := by intro h; rw [h,zero_mul] at sc; exact ap.ne sc
    field_simp [cn,ap.ne']
    linarith
  rcases (data_at_top (endpoint_weights flat).1 top y).2 ⟨c⁻¹,rat⟩ with z|u
  · exact (div_pos yp' ap).ne' z
  · exact (div_lt_one ap).mpr yl |>.ne u

/-- In particular, the opposite marginal can have any number of atoms
as long as it has at most two positive mass values. -/
theorem uniform_of_two_levels {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (two : Green28TwoMassLevels.AtMostTwo P) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  apply uniform_of_commensurable_deficits flat one
  obtain ⟨u,v,levels⟩ := two
  intro a top x hx y hy xl yl
  refine ⟨1,?_⟩
  simp only [Rat.cast_one,one_mul]
  rcases levels a top.1 with h|h <;> rcases levels x hx with h'|h' <;>
    rcases levels y hy with h''|h'' <;> linarith

open Polynomial Green28PolynomialReduction

/-- Atom probability divided by the mass at a specified endpoint. -/
noncomputable def weight (P : PMF ℤ) (a x : ℤ) : ℝ := (P x).toReal/(P a).toReal

/-- The set of distinct normalized weights of occupied deficient atoms. -/
def deficientWeights (P : PMF ℤ) (a : ℤ) : Set ℝ :=
  {t | ∃ x ∈ P.support, (P x).toReal<(P a).toReal ∧ weight P a x = t}

private theorem span_one {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q))
    (w : Boundary P Q) : 1 ∈ Submodule.span ℤ (deficientWeights P w.a) := by
  obtain ⟨a,ta,E,_,low,eq⟩ := subset_mass_of_one_deficit flat one bad
  have ea : a = w.a := ta.unique w.topP
  subst a
  have ap := ENNReal.toReal_pos ((P.mem_support_iff _).mp w.topP.1) (P.apply_ne_top _)
  have e : (∑ x ∈ E,weight P w.a x) = 1 := by simp only [weight,←sum_div,eq,div_self ap.ne']
  rw [←e]
  exact Submodule.sum_mem _ (fun x hx => Submodule.subset_span ⟨x,(low x hx).1,(low x hx).2,rfl⟩)

/-- Every row paired with the exceptional column has a complementary sum
of deficient row weights at distinct other sites in the same fibre. -/
theorem deficient_remainder {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (w : Boundary P Q) {y : ℤ} (hy : y ∈ P.support) :
    ∃ E : Finset ℤ, (∀ x ∈ E, x ≠ y ∧ x ∈ P.support ∧ y+w.d-x ∈ Q.support ∧
      (P x).toReal<(P w.a).toReal) ∧
      weight Q w.b w.d*weight P w.a y+(∑ x ∈ E,weight P w.a x) = 1 := by
  classical
  obtain ⟨pf,_⟩ := finite_of_uniform_sum flat
  let A := pf.toFinset
  let h (x : ℤ) := (P x).toReal*(Q (y+w.d-x)).toReal
  let scale := (P w.a).toReal*(Q w.b).toReal
  have pp := ENNReal.toReal_pos ((P.mem_support_iff _).mp w.topP.1) (P.apply_ne_top _)
  have qp := ENNReal.toReal_pos ((Q.mem_support_iff _).mp w.topQ.1) (Q.apply_ne_top _)
  have sp : 0 < scale := mul_pos pp qp
  have ya : y ∈ A := pf.mem_toFinset.mpr hy
  have tot : ∑ x ∈ A,h x = scale := sum_at_occupied flat pf w.topP w.topQ
    (show ∃ x ∈ P.support, y+w.d-x ∈ Q.support from ⟨y,hy,by simpa using w.lowQ⟩)
  have ey : h y = (P y).toReal*(Q w.d).toReal := by simp [h]
  have yp : 0 < h y := by
    rw [ey]; exact mul_pos (ENNReal.toReal_pos ((P.mem_support_iff _).mp hy) (P.apply_ne_top _))
      (ENNReal.toReal_pos ((Q.mem_support_iff _).mp w.lowQ) (Q.apply_ne_top _))
  let E := (A.erase y).filter fun x => y+w.d-x ∈ Q.support
  have rows {x : ℤ} (hx : x ∈ E) : x ≠ y ∧ x ∈ P.support ∧ y+w.d-x ∈ Q.support ∧
      (P x).toReal<(P w.a).toReal := by
    obtain ⟨inA,hit⟩ := mem_filter.mp hx
    obtain ⟨ne,xa⟩ := mem_erase.mp inA
    have high := w.other _ hit (by omega)
    have less : h x < scale := by
      rw [←tot]
      exact single_lt_sum ne.symm xa ya yp (fun z _ _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    exact ⟨ne,pf.mem_toFinset.mp xa,hit,(mul_lt_mul_iff_left₀ qp).mp
      (by simpa only [h,scale,high] using less)⟩
  refine ⟨E,fun _ hx => rows hx,?_⟩
  have total : (∑ x ∈ A,h x/scale) = 1 := by rw [←sum_div,tot,div_self sp.ne']
  rw [←total,←add_sum_erase _ _ ya]
  congr 1
  · rw [ey]; dsimp only [weight,scale]; ring
  · change (∑ x ∈ (A.erase y).filter _,weight P w.a x) = _
    rw [sum_filter]
    apply sum_congr rfl
    intro x hx
    split_ifs with hit
    · have eq := w.other _ hit (by have := (mem_erase.mp hx).1; omega)
      simp only [h,scale,weight,eq]; field_simp
    · simp [h,(Q.apply_eq_zero_iff _).mpr hit]

private theorem times_defect {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (w : Boundary P Q) (T : Submodule ℤ ℝ) (one : (1:ℝ) ∈ T)
    (low : deficientWeights P w.a ⊆ T) {y : ℤ} (hy : y ∈ P.support) :
    weight Q w.b w.d*weight P w.a y ∈ T := by
  obtain ⟨E,rows,eq⟩ := deficient_remainder flat w hy
  rw [eq_sub_iff_add_eq.mpr eq]
  exact T.sub_mem one (T.sum_mem (fun x hx => low ⟨x,(rows x hx).2.1,(rows x hx).2.2.2,rfl⟩))

/-- The coefficients of a monic marginal model are the weights normalized at its rightmost support point. -/
theorem model_weight {P : PMF ℤ} {f : ℝ[X]} {l a : ℤ} {s : ℝ}
    (m : Models P f l s) (mon : f.Monic) (top : IsGreatest P.support a) (i : ℕ) :
    weight P a (l+i) = f.coeff i := by
  have lead := m.coeff f.natDegree
  rw [mon.coeff_natDegree,mul_one] at lead
  have inP : l+(f.natDegree:ℤ) ∈ P.support := (P.mem_support_iff _).mpr (by
    intro off; rw [off,ENNReal.toReal_zero] at lead; exact m.pos.ne lead)
  have eq : l+(f.natDegree:ℤ) = a := by
    apply le_antisymm (top.2 inP)
    by_contra! above
    have off := m.coeff (a-l).toNat
    rw [show l+↑(a-l).toNat = a by omega,coeff_eq_zero_of_natDegree_lt
      (by omega : f.natDegree<(a-l).toNat),mul_zero] at off
    exact (ENNReal.toReal_pos ((P.mem_support_iff _).mp top.1) (P.apply_ne_top _)).ne' off
  rw [eq] at lead
  rw [weight,m.coeff,lead]
  field_simp [m.pos.ne']

/-- At a deficient boundary the opposite deficient weights, by integer linear
combinations alone, generate the whole ring of integer polynomials in the
unique normalized exceptional mass. -/
theorem deficient_integer_span {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q))
    (w : Boundary P Q) : Submodule.span ℤ (deficientWeights P w.a)=
      (Algebra.adjoin ℤ {weight Q w.b w.d}).toSubmodule := by
  classical
  let u := weight Q w.b w.d
  let R := Algebra.adjoin ℤ ({u}:Set ℝ)
  let T := Submodule.span ℤ (deficientWeights P w.a)
  change T = R.toSubmodule
  apply le_antisymm
  · obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
    obtain ⟨f,l,s,m,fm,_,_⟩ := chart P pf
    obtain ⟨g,k,t,n,gm,_,_⟩ := chart Q qf
    have bin := ((m.mul n).uniform_iff (fm.mul gm)).mp flat
    have qpos := ENNReal.toReal_pos ((Q.mem_support_iff _).mp w.topQ.1) (Q.apply_ne_top _)
    have gmemb (i : ℕ) : g.coeff i ∈ R.toSubring := by
      rw [←model_weight n gm w.topQ i]
      by_cases site : k+(i:ℤ) ∈ Q.support
      · by_cases eq : k+(i:ℤ) = w.d
        · rw [eq]; exact Algebra.subset_adjoin (Set.mem_singleton u)
        · rw [weight,w.other _ site eq,div_self qpos.ne']; exact R.one_mem
      · rw [weight,(Q.apply_eq_zero_iff _).mpr site,ENNReal.toReal_zero,zero_div]; exact R.zero_mem
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,_,rfl⟩
    have lo : l ≤ x := by by_contra! lt; exact (P.mem_support_iff _).mp hx (m.below _ lt)
    have val := model_weight m fm w.topP (x-l).toNat
    rw [show l+↑(x-l).toNat = x by omega] at val
    rw [val]
    exact coeff_mem_of_monic_factor gm (by simpa only [mul_comm g f] using bin)
      R.toSubring gmemb _
  · have h1 : (1:ℝ) ∈ T := span_one flat one bad w
    have stable (v : ℝ) (hv : v ∈ T) : u*v ∈ T := by
      induction hv using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨y,hy,_,rfl⟩ := ht
        exact times_defect flat w T h1 (fun _ hx => Submodule.subset_span hx) hy
      | zero => simp
      | add x y _ _ hx hy => simpa only [mul_add] using T.add_mem hx hy
      | smul z x _ hx => simpa only [zsmul_eq_mul,mul_left_comm u] using T.smul_mem z hx
    intro v hv
    change v ∈ R at hv
    have action : ∀ x ∈ T, v*x ∈ T := by
      induction hv using Algebra.adjoin_induction with
      | mem t ht => obtain rfl : t = u := ht; exact stable
      | algebraMap z => intro x hx; simpa only [Algebra.smul_def] using T.smul_mem z hx
      | add r s _ _ hr hs => intro x hx; simpa only [add_mul] using T.add_mem (hr x hx) (hs x hx)
      | mul r s _ _ hr hs => intro x hx; simpa only [mul_assoc] using hr _ (hs x hx)
    simpa using action 1 h1

#print axioms exists_leaving_step
#print axioms deficient_fibre
#print axioms boundary_of_one_deficit
#print axioms subset_mass_of_one_deficit
#print axioms uniform_of_commensurable_deficits
#print axioms uniform_of_two_levels
#print axioms deficient_remainder
#print axioms sum_at_occupied
#print axioms model_weight
#print axioms deficient_integer_span
end Green28DeficientFibre
