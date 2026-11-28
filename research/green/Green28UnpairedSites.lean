import Green28AlgebraicWidth

/-! Extremal deficient sites and reflection of the original supports in Green 28. -/

namespace Green28UnpairedSites

open Green28 Green28UniformSums Green28AlgebraicWidth Finset
open scoped ENNReal

/-- Each occupied site except possibly one has its reflection in the support. -/
def AtMostOneUnpaired (A : Set ℤ) : Prop :=
  ∃ lo hi e : ℤ, IsLeast A lo ∧ IsGreatest A hi ∧ ∀ x ∈ A, lo+hi-x ∉ A → x=e

private def Single (A B : Set ℤ) (x y : ℤ) : Prop :=
  ∀ s ∈ A, ∀ t ∈ B, x+y=s+t → x=s ∧ y=t

private def Rectangle (A B : Set ℤ) (u v : ℤ → Prop) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, Single A B x y ↔ u x ∧ v y

private theorem flip {A B : Set ℤ} {u v : ℤ → Prop} (rect : Rectangle A B u v) : Rectangle B A v u := by
  intro y hy x hx
  have eq : Single B A y x ↔ Single A B x y := by
    constructor
    · intro h s hs t ht e
      exact (h t ht s hs (by simpa only [add_comm] using e)).symm
    · intro h t ht s hs e
      exact (h s hs t ht (by simpa only [add_comm] using e)).symm
  rw [eq,rect _ hx _ hy,and_comm]

private theorem first_offset_le {A B : Set ℤ} {u v : ℤ → Prop} (rect : Rectangle A B u v)
    {a b c d : ℤ} (amin : IsLeast A a) (bmin : IsLeast B b)
    (firstA : IsLeast {x | x∈A ∧ ¬u x} c) (firstB : IsLeast {y | y∈B ∧ ¬v y} d) :
    d-b ≤ c-a := by
  have notSingle : ¬Single A B c b := fun h => firstA.1.2 ((rect _ firstA.1.1 _ bmin.1).mp h).1
  unfold Single at notSingle
  push Not at notSingle
  obtain ⟨x,hx,y,hy,e,ne⟩ := notSingle
  have yb : b < y := lt_of_le_of_ne (bmin.2 hy) (by rintro rfl; exact ne (by omega) rfl)
  have xc : x < c := by omega
  have high : u x := by by_contra bad; exact xc.not_ge (firstA.2 ⟨hx,bad⟩)
  have low : ¬v y := by
    intro vy
    obtain ⟨r,s⟩ := (rect x hx y hy).mpr ⟨high,vy⟩ c firstA.1.1 b bmin.1 e.symm
    exact ne r.symm s.symm
  have := firstB.2 ⟨hy,low⟩
  have := amin.2 hx
  omega

private theorem last_offset_le {A B : Set ℤ} {u v : ℤ → Prop} (rect : Rectangle A B u v)
    {a b c d : ℤ} (amax : IsGreatest A a) (bmax : IsGreatest B b)
    (lastA : IsGreatest {x | x∈A ∧ ¬u x} c) (lastB : IsGreatest {y | y∈B ∧ ¬v y} d) :
    b-d ≤ a-c := by
  have notSingle : ¬Single A B c b := fun h => lastA.1.2 ((rect _ lastA.1.1 _ bmax.1).mp h).1
  unfold Single at notSingle
  push Not at notSingle
  obtain ⟨x,hx,y,hy,e,ne⟩ := notSingle
  have yb : y < b := lt_of_le_of_ne (bmax.2 hy) (by rintro rfl; exact ne (by omega) rfl)
  have xc : c < x := by omega
  have high : u x := by by_contra bad; exact xc.not_ge (lastA.2 ⟨hx,bad⟩)
  have low : ¬v y := by
    intro vy
    obtain ⟨r,s⟩ := (rect x hx y hy).mpr ⟨high,vy⟩ c lastA.1.1 b bmax.1 e.symm
    exact ne r.symm s.symm
  have := lastB.2 ⟨hy,low⟩
  have := amax.2 hx
  omega

private theorem sum_coeff (P Q : PMF ℤ) (z : ℤ) (pf : P.support.Finite) :
    (indepSum P Q z).toReal = ∑ x ∈ pf.toFinset, (P x).toReal*(Q (z-x)).toReal := by
  have conv : indepSum P Q z = ∑' x, P x * Q (z-x) := by
    change (P.bind fun x => Q.bind fun y => PMF.pure (x+y)) z = _
    rw [PMF.bind_apply]
    congr 1
    funext x
    rw [PMF.bind_apply,tsum_eq_single (z-x)]
    · simp [PMF.pure_apply]
    · intro y hy
      have ne : z ≠ x+y := by omega
      simp [PMF.pure_apply,ne]
  have off (x : ℤ) (hx : x ∉ pf.toFinset) : P x*Q (z-x)=0 := by
    rw [(P.apply_eq_zero_iff x).mpr (fun k => hx (pf.mem_toFinset.mpr k)),zero_mul]
  rw [conv,tsum_eq_sum off,ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top (P.apply_ne_top _) (Q.apply_ne_top _))]
  simp only [ENNReal.toReal_mul]

private theorem prob_rectangle {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    {a b : ℤ} (amin : IsLeast P.support a) (bmin : IsLeast Q.support b) :
    Rectangle P.support Q.support (fun x => (P x).toReal=(P a).toReal)
      (fun y => (Q y).toReal=(Q b).toReal) ∧
      (∀ x ∈ P.support, (P x).toReal ≤ (P a).toReal) ∧ (∀ y ∈ Q.support, (Q y).toReal ≤ (Q b).toReal) := by
  classical
  obtain ⟨pf,_⟩ := finite_of_uniform_sum sum
  obtain ⟨S,non,law⟩ := sum
  let c : ℝ := (S.card:ℝ)⁻¹
  have pos {R : PMF ℤ} {x} (h : x∈R.support) := ENNReal.toReal_pos ((R.mem_support_iff _).mp h) (R.apply_ne_top _)
  have entry (x : ℤ) (hx : x∈P.support) (y : ℤ) (hy : y∈Q.support) :
      (P x).toReal*(Q y).toReal ≤ c ∧ (Single P.support Q.support x y ↔ (P x).toReal*(Q y).toReal=c) := by
    let f (z : ℤ) := (P z).toReal*(Q (x+y-z)).toReal
    have sx : x∈pf.toFinset := pf.mem_toFinset.mpr hx
    have point : f x = (P x).toReal*(Q y).toReal := by simp [f]
    have mem : x+y ∈ (indepSum P Q).support := (PMF.mem_support_bind_iff _ _ _).mpr ⟨x,hx,
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨y,hy,(PMF.mem_support_pure_iff _ _).mpr rfl⟩⟩
    rw [law,PMF.support_uniformOfFinset] at mem
    have total : ∑ z ∈ pf.toFinset, f z = c := by
      rw [←sum_coeff P Q _ pf,law,PMF.uniformOfFinset_apply_of_mem non mem]
      simp [c]
    have nonneg (z : ℤ) : 0 ≤ f z := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    rw [←point,←total]
    refine ⟨single_le_sum (fun k _ => nonneg k) sx,?_,?_⟩
    · intro alone
      symm
      apply sum_eq_single x
      · intro z hz ne
        have miss : x+y-z ∉ Q.support := fun ok => ne
          (alone z (pf.mem_toFinset.mp hz) (x+y-z) ok (by omega)).1.symm
        simp [f,(Q.apply_eq_zero_iff _).mpr miss]
      · exact fun no => (no sx).elim
    · intro equal z hz t ht eq
      by_cases same : z=x
      · exact ⟨same.symm,by omega⟩
      · have nz : 0 < f z := by
          simpa only [f,show x+y-z=t by omega] using mul_pos (pos hz) (pos ht)
        exact ((single_lt_sum (f := f) same sx (pf.mem_toFinset.mpr hz) nz (fun z _ _ => nonneg z)).ne equal).elim
  have bottom : Single P.support Q.support a b := by
    intro x hx y hy e
    have := amin.2 hx
    have := bmin.2 hy
    exact ⟨by omega,by omega⟩
  have ab := (entry a amin.1 b bmin.1).2.mp bottom
  have ub (x) (hx : x∈P.support) := (mul_le_mul_iff_left₀ (pos bmin.1)).mp ((entry x hx b bmin.1).1.trans_eq ab.symm)
  have vb (y) (hy : y∈Q.support) := (mul_le_mul_iff_right₀ (pos amin.1)).mp ((entry a amin.1 y hy).1.trans_eq ab.symm)
  refine ⟨?_,ub,vb⟩
  intro x hx y hy
  rw [(entry x hx y hy).2,←ab]
  constructor
  · intro equal
    constructor
    · by_contra ne
      exact ((mul_lt_mul_of_pos_right (lt_of_le_of_ne (ub x hx) ne) (pos hy)).trans_le
        (mul_le_mul_of_nonneg_left (vb y hy) (pos amin.1).le)).ne equal
    · by_contra ne
      exact ((mul_lt_mul_of_pos_left (lt_of_le_of_ne (vb y hy) ne) (pos hx)).trans_le
        (mul_le_mul_of_nonneg_right (ub x hx) (pos bmin.1).le)).ne equal
  · rintro ⟨h,k⟩
    rw [h,k]

/-- The two extreme occupied integers of a nonempty finite set. -/
structure Extremes (A : Set ℤ) where
  lo : ℤ
  hi : ℤ
  least : IsLeast A lo
  greatest : IsGreatest A hi

private noncomputable def extremes (A : Set ℤ) (finite : A.Finite) (ne : A.Nonempty) : Extremes A :=
  let s := finite.toFinset
  let live := finite.toFinset_nonempty.mpr ne
  ⟨s.min' live,s.max' live,finite.coe_toFinset ▸ s.isLeast_min' live,
    finite.coe_toFinset ▸ s.isGreatest_max' live⟩

/-- Occupied sites whose mass differs from the mass at the left endpoint. -/
def lowerSites (P : PMF ℤ) (a : ℤ) : Set ℤ := {x | x∈P.support ∧ (P x).toReal≠(P a).toReal}

/-- Both endpoint offsets match. Reflecting any of the four extreme deficient
sites about the midpoint of its own support gives an unoccupied integer. -/
structure Alignment (P Q : PMF ℤ) where
  left : Extremes P.support
  right : Extremes Q.support
  leftLow : Extremes (lowerSites P left.lo)
  rightLow : Extremes (lowerSites Q right.lo)
  lower_eq : leftLow.lo-left.lo=rightLow.lo-right.lo
  upper_eq : left.hi-leftLow.hi=right.hi-rightLow.hi
  left_first_missing : left.lo+left.hi-leftLow.lo ∉ P.support
  left_last_missing : left.lo+left.hi-leftLow.hi ∉ P.support
  right_first_missing : right.lo+right.hi-rightLow.lo ∉ Q.support
  right_last_missing : right.lo+right.hi-rightLow.hi ∉ Q.support

private theorem reflect_gap {A B : Set ℤ} {u v : ℤ → Prop} (rect : Rectangle A B u v)
    {p lo hi y : ℤ} (pA : p∈A) (loA : lo∈A) (hiB : hi∈B) (yB : y∈B)
    (up : u lo) (vp : v hi) (bad : ¬v y) (eq : p+y=lo+hi) : False := by
  obtain ⟨_,same⟩ := (rect lo loA hi hiB).mpr ⟨up,vp⟩ p pA y yB eq.symm
  exact bad (same ▸ vp)

private theorem high_ends {A B : Set ℤ} {u v : ℤ → Prop} (rect : Rectangle A B u v)
    (L : Extremes A) (R : Extremes B) : u L.hi ∧ v R.hi := by
  apply (rect _ L.greatest.1 _ R.greatest.1).mp
  intro x hx y hy e
  have := L.greatest.2 hx
  have := R.greatest.2 hy
  exact ⟨by omega,by omega⟩

/-- The endpoint masses at both ends are equal. For the two original PMFs,
a sum has a unique representation exactly when both contributing sites
have their endpoint masses. -/
theorem maximal_rectangle {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (A : Extremes P.support) (B : Extremes Q.support) :
    (P A.hi).toReal = (P A.lo).toReal ∧ (Q B.hi).toReal = (Q B.lo).toReal ∧
    ∀ x ∈ P.support, ∀ y ∈ Q.support,
      (∀ u ∈ P.support, ∀ v ∈ Q.support, x+y = u+v → x = u ∧ y = v) ↔
        (P x).toReal = (P A.lo).toReal ∧ (Q y).toReal = (Q B.lo).toReal := by
  have rect := (prob_rectangle sum A.least B.least).1
  have top := high_ends rect A B
  exact ⟨top.1,top.2,rect⟩

private theorem ratios_of_empty {P : PMF ℤ} {a : ℤ} (empty : ¬ (lowerSites P a).Nonempty) : RationalRatios P := by
  have eq (x : ℤ) (hx : x∈P.support) : (P x).toReal=(P a).toReal := by
    by_contra h
    exact empty ⟨x,hx,h⟩
  intro x y hy
  have pos := ENNReal.toReal_pos ((P.mem_support_iff y).mp hy) (P.apply_ne_top y)
  by_cases hx : x∈P.support
  · exact ⟨1,by rw [eq x hx,←eq y hy]; simp [pos.ne']⟩
  · exact ⟨0,by simp [(P.apply_eq_zero_iff x).mpr hx]⟩

/-- Every failure of marginal uniformity supplies the four missing reflected
sites and the two offset identities for the original probability laws. -/
theorem alignment_alternative {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q)) :
    (IsUniformOnSupport P ∧ IsUniformOnSupport Q) ∨ Nonempty (Alignment P Q) := by
  classical
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum sum
  let A := extremes P.support pf P.support_nonempty
  let B := extremes Q.support qf Q.support_nonempty
  obtain ⟨rect,_,_⟩ := prob_rectangle sum A.least B.least
  by_cases hp : (lowerSites P A.lo).Nonempty
  · by_cases hq : (lowerSites Q B.lo).Nonempty
    · let X := extremes (lowerSites P A.lo) (pf.subset (fun _ hx => hx.1)) hp
      let Y := extremes (lowerSites Q B.lo) (qf.subset (fun _ hy => hy.1)) hq
      have top := high_ends rect A B
      have low : X.lo-A.lo=Y.lo-B.lo := le_antisymm
        (first_offset_le (flip rect) B.least A.least Y.least X.least)
        (first_offset_le rect A.least B.least X.least Y.least)
      have high : A.hi-X.hi=B.hi-Y.hi := le_antisymm
        (last_offset_le (flip rect) B.greatest A.greatest Y.greatest X.greatest)
        (last_offset_le rect A.greatest B.greatest X.greatest Y.greatest)
      refine Or.inr ⟨⟨A,B,X,Y,low,high,?_,?_,?_,?_⟩⟩
      · intro mem
        exact reflect_gap rect mem A.greatest.1 B.least.1 Y.least.1.1 top.1 rfl Y.least.1.2 (by omega)
      · intro mem
        exact reflect_gap rect mem A.least.1 B.greatest.1 Y.greatest.1.1 rfl top.2 Y.greatest.1.2 (by omega)
      · intro mem
        exact reflect_gap (flip rect) mem B.greatest.1 A.least.1 X.least.1.1 top.2 rfl X.least.1.2 (by omega)
      · intro mem
        exact reflect_gap (flip rect) mem B.least.1 A.greatest.1 X.greatest.1.1 rfl top.1 X.greatest.1.2 (by omega)
    · exact Or.inl (uniform_of_rational_ratios sum (Or.inr (ratios_of_empty hq)))
  · exact Or.inl (uniform_of_rational_ratios sum (Or.inl (ratios_of_empty hp)))

private theorem collapse {A : Set ℤ} (shape : AtMostOneUnpaired A) (E : Extremes A)
    {x y : ℤ} (hx : x∈A) (hy : y∈A) (mx : E.lo+E.hi-x∉A) (my : E.lo+E.hi-y∉A) : x=y := by
  obtain ⟨l,h,e,lo,hi,one⟩ := shape
  have leq : l=E.lo := lo.unique E.least
  have heq : h=E.hi := hi.unique E.greatest
  subst l; subst h
  exact (one x hx mx).trans (one y hy my).symm

/-- With only one unpaired occupied site, only one occupied site can have less
than maximal probability, whatever the opposite support and weights. -/
theorem one_deficit_of_one_unpaired {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (shape : AtMostOneUnpaired P.support) : OneDeficit P := by
  rcases alignment_alternative sum with fair|alternative
  · obtain ⟨S,ne,rfl⟩ := fair.1
    refine ⟨0,?_⟩
    rintro x hx ⟨y,less⟩
    rw [PMF.support_uniformOfFinset] at hx
    rw [PMF.uniformOfFinset_apply_of_mem ne hx,PMF.uniformOfFinset_apply] at less
    split at less <;> simp_all
  · obtain ⟨M⟩ := alternative
    have equal := collapse shape M.left M.leftLow.least.1.1 M.leftLow.greatest.1.1
      M.left_first_missing M.left_last_missing
    obtain ⟨_,bound,_⟩ := prob_rectangle sum M.left.least M.right.least
    refine ⟨M.leftLow.lo,?_⟩
    rintro x hx ⟨y,less⟩
    have hy := (P.mem_support_iff y).mpr ((bot_le : 0 ≤ P x).trans_lt less).ne'
    have lt := (ENNReal.toReal_lt_toReal (P.apply_ne_top _) (P.apply_ne_top _)).mpr less
    have low : x ∈ lowerSites P M.left.lo := ⟨hx,(lt.trans_le (bound y hy)).ne⟩
    have ll := M.leftLow.least.2 low
    have rr := M.leftLow.greatest.2 low
    omega

/-- Interchanging the two independent integer laws preserves their sum. -/
theorem indepSum_comm (P Q : PMF ℤ) : indepSum P Q=indepSum Q P := by
  change (P.bind fun x => Q.bind fun y => PMF.pure (x+y)) = _
  rw [PMF.bind_comm]
  simp only [indepSum, Bind.bind, add_comm]

/-- Both supports may have arbitrarily many sites, arbitrary gaps, and
arbitrary weights. Each has at most one site missing its reflected partner. -/
theorem uniform_of_one_unpaired_each {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (left : AtMostOneUnpaired P.support) (right : AtMostOneUnpaired Q.support) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  by_cases size : width Q ≤ width P
  · exact uniform_of_one_deficit_of_width sum (one_deficit_of_one_unpaired sum left) size
  · have rev := indepSum_comm P Q ▸ sum
    exact (uniform_of_one_deficit_of_width rev (one_deficit_of_one_unpaired rev right) (by omega)).symm

/-- The support width measured at any pair of certified extrema. -/
theorem width_of_extremes {P : PMF ℤ} (pf : P.support.Finite) (E : Extremes P.support) :
    (width P : ℤ) = E.hi-E.lo := by
  classical
  let s := pf.toFinset
  let ne := pf.toFinset_nonempty.mpr P.support_nonempty
  have lo : s.min' ne=E.lo := (pf.coe_toFinset ▸ s.isLeast_min' ne : IsLeast P.support _).unique E.least
  have hi : s.max' ne=E.hi := (pf.coe_toFinset ▸ s.isGreatest_max' ne : IsGreatest P.support _).unique E.greatest
  unfold width
  rw [dif_pos pf]
  change (((s.max' ne-s.min' ne).toNat : ℕ) : ℤ)=_
  rw [hi,lo,Int.toNat_of_nonneg (sub_nonneg.mpr (E.least.2 E.greatest.1))]

/-- Against an unrestricted partner, a single unpaired site forces two
unpaired sites across a gap equal to the difference in support widths.
The unique left deficiency also obeys the degree and mass-level bounds. -/
theorem one_unpaired_alternative {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (shape : AtMostOneUnpaired P.support) :
    (IsUniformOnSupport P ∧ IsUniformOnSupport Q) ∨ ∃ M : Alignment P Q,
      M.leftLow.lo=M.leftLow.hi ∧ M.rightLow.lo < M.rightLow.hi ∧
      M.rightLow.hi-M.rightLow.lo=(width Q : ℤ)-(width P : ℤ) ∧
      let u := (P M.leftLow.lo).toReal/(P M.left.hi).toReal
      0 < u ∧ u < 1 ∧ 2 ≤ (minpoly ℚ u).natDegree ∧
        ((minpoly ℚ u).natDegree-1)*width P ≤ width Q ∧ (minpoly ℚ u).natDegree ≤ massLevels Q := by
  rcases alignment_alternative sum with fair|alt
  · exact Or.inl fair
  obtain ⟨M⟩ := alt
  rcases one_deficit_alternative sum (one_deficit_of_one_unpaired sum shape) with fair|arith
  · exact Or.inl fair
  obtain ⟨a,e,ha,he,top,hpos,hlt,degree,wide,bound,levels⟩ := arith
  have ee : e=M.left.hi := (show IsGreatest P.support e from ⟨he,top⟩).unique M.left.greatest
  subst e
  have same := collapse shape M.left M.leftLow.least.1.1 M.leftLow.greatest.1.1
    M.left_first_missing M.left_last_missing
  obtain ⟨r,_,_⟩ := prob_rectangle sum M.left.least M.right.least
  have highest := (high_ends r M.left M.right).1
  have pos := ENNReal.toReal_pos ((P.mem_support_iff _).mp M.left.greatest.1) (P.apply_ne_top _)
  have low : a∈lowerSites P M.left.lo := by
    refine ⟨ha,?_⟩
    intro eq
    rw [eq,←highest,div_self pos.ne'] at hlt
    exact lt_irrefl _ hlt
  have lowL := M.leftLow.least.2 low
  have lowR := M.leftLow.greatest.2 low
  have ea : a=M.leftLow.lo := by omega
  subst a
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum sum
  have wL := width_of_extremes pf M.left
  have wR := width_of_extremes qf M.right
  have first := M.lower_eq
  have last := M.upper_eq
  exact Or.inr ⟨M,same,by omega,by omega,hpos,hlt,degree,bound,levels⟩

#print axioms indepSum_comm
#print axioms width_of_extremes
#print axioms maximal_rectangle
#print axioms one_unpaired_alternative
#print axioms alignment_alternative
#print axioms one_deficit_of_one_unpaired
#print axioms uniform_of_one_unpaired_each

end Green28UnpairedSites
