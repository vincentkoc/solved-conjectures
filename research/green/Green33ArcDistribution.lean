import Green33LowRank
import Mathlib.LinearAlgebra.Matrix.Circulant

/-! Uniform distribution of the labels of almost optimal cyclic two-bases. -/

open Finset Filter Green33LowRank Green33Multiplicity Green33ShiftVariation
open scoped Pointwise Topology Matrix

namespace Green33ArcDistribution

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- The absolute sum of the errors of the convolution square. -/
noncomputable def squareError (f : G → ℝ) : ℝ := ∑ z, |∑ x, f (z-x)*f x|

private theorem square_cap (f : G → ℝ) (u : EuclideanSpace ℝ G) :
    ‖(table f).toEuclideanLin u‖^2 ≤ squareError f*‖u‖^2 := by
  let B := table f
  have comm : B*B.transpose=B.transpose*B := by
    change Matrix.circulant f*(Matrix.circulant f).transpose=(Matrix.circulant f).transpose*Matrix.circulant f
    rw [Matrix.transpose_circulant,Matrix.circulant_mul_comm]
  have same : (B.transpose*B).transpose*(B.transpose*B)=(B*B).transpose*(B*B) := by
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose]
    calc B.transpose*B*(B.transpose*B)=B.transpose*(B*B.transpose)*B := by noncomm_ring
         _ = _ := by rw [comm]; noncomm_ring
  have bound : ‖(B*B).toEuclideanLin u‖ ≤ squareError f*‖u‖ := by
    change ‖(Matrix.circulant f*Matrix.circulant f).toEuclideanLin u‖ ≤ _
    rw [Matrix.circulant_mul]
    exact table_cap (fun z => ∑ x, f (z-x)*f x) u
  let v := (B.transpose*B).toEuclideanLin u
  have eq : ‖B.toEuclideanLin u‖^2=∑ i, u i*v i := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change ∑ i, ((B *ᵥ WithLp.ofLp u) i)^2 = (WithLp.ofLp u) ⬝ᵥ ((B.transpose*B) *ᵥ WithLp.ofLp u)
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    simp only [sq,dotProduct]
  have cs := Real.sum_mul_le_sqrt_mul_sqrt univ (fun i => u i) (fun i => v i)
  rw [← EuclideanSpace.real_norm_sq_eq,← EuclideanSpace.real_norm_sq_eq,Real.sqrt_sq (norm_nonneg u),
    Real.sqrt_sq (norm_nonneg v)] at cs
  have hv : ‖v‖≤squareError f*‖u‖ := (gram_norm same u).le.trans bound
  exact (eq.le.trans cs).trans ((mul_le_mul_of_nonneg_left hv (norm_nonneg u)).trans_eq (by ring))

private def ind (A : Finset G) (x : G) : ℝ := if x∈A then 1 else 0

/-- Mixing between two arbitrary finite sets, controlled by the centered
sum profile once `f` is chosen as the centered seed indicator. -/
theorem rectangle_bound (f : G → ℝ) (I J : Finset G) :
    |∑ i ∈ I, ∑ j ∈ J, f (i-j)| ≤ Real.sqrt (squareError f)*Real.sqrt I.card*Real.sqrt J.card := by
  let u : EuclideanSpace ℝ G := WithLp.toLp 2 (ind J)
  let v := (table f).toEuclideanLin u
  have iu : ‖u‖^2=J.card := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change ∑ i, (if i∈J then (1:ℝ) else 0)^2=_
    simp [ite_pow]
  have vi (i) : v i=∑ j ∈ J, f (i-j) := by
    change ∑ j, f (i-j)*(if j∈J then (1:ℝ) else 0)=_
    simp [mul_ite]
  have cap := square_cap f u
  rw [iu] at cap
  have nonneg : 0≤squareError f := sum_nonneg fun _ _ => abs_nonneg _
  have norm : ‖v‖ ≤ Real.sqrt (squareError f)*Real.sqrt J.card := by
    rw [← Real.sqrt_mul nonneg]
    exact Real.le_sqrt_of_sq_le cap
  have cs := Real.sum_mul_le_sqrt_mul_sqrt I (fun _ => (1:ℝ)) (fun i => |v i|)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,sq_abs] at cs
  have part : ∑ i ∈ I, (v i)^2≤‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
  rw [show (∑ i ∈ I, ∑ j ∈ J, f (i-j))=∑ i ∈ I, v i by simp_rw [vi]]
  calc
    _ ≤ ∑ i ∈ I, |v i| := abs_sum_le_sum_abs _ _
    _ ≤ _ := cs
    _ ≤ Real.sqrt I.card*‖v‖ := by
      gcongr
      exact (Real.sqrt_le_sqrt part).trans_eq (Real.sqrt_sq (norm_nonneg _))
    _ ≤ _ := (mul_le_mul_of_nonneg_left norm (Real.sqrt_nonneg _)).trans_eq (by ring)


private theorem indicator_conv (A : Finset G) (z : G) :
    ∑ x, ind A (z-x)*ind A x=(reps A z:ℝ) := by
  let S := A.filter fun x => z-x∈A
  have eq : S.card=reps A z := by
    apply card_nbij' (fun x => (z-x,x)) (fun p => p.2)
    · intro x hx
      obtain ⟨ha,hb⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨mk_mem_product hb ha,sub_add_cancel ..⟩
    · rintro ⟨x,y⟩ hy
      obtain ⟨hp,e⟩ := mem_filter.mp hy
      obtain ⟨hx,hy⟩ := mem_product.mp hp
      change x+y=z at e
      exact mem_filter.mpr ⟨hy,by simpa [← e] using hx⟩
    · intro _ _;rfl
    · rintro ⟨x,y⟩ hz
      have e := (mem_filter.mp hz).2
      change x+y=z at e
      simp [← e]
  rw [← eq]
  simp [ind, mul_ite, S, Finset.sum_boole]

/-- The indicator with its mean subtracted. -/
noncomputable def centered (A : Finset G) (x : G) : ℝ := ind A x-(A.card:ℝ)/Fintype.card G

private theorem centered_conv (A : Finset G) (z : G) :
    ∑ x, centered A (z-x)*centered A x=(reps A z:ℝ)-(A.card:ℝ)^2/Fintype.card G := by
  let c : ℝ := (A.card:ℝ)/Fintype.card G
  have sumI : ∑ x, ind A x=(A.card:ℝ) := by simp [ind]
  have reverse : ∑ x, ind A (z-x)=(A.card:ℝ) := ((Equiv.subLeft z).sum_comp (ind A)).trans sumI
  have term (x) : centered A (z-x)*centered A x=ind A (z-x)*ind A x - c*ind A (z-x)-c*ind A x+c^2 := by
    change (_-c)*(_-c)=_;ring
  simp only [term,sum_add_distrib,sum_sub_distrib,← mul_sum,indicator_conv,reverse,sumI,
    sum_const,card_univ,nsmul_eq_mul,c]
  field_simp [show (Fintype.card G:ℝ)≠0 by exact_mod_cast Fintype.card_ne_zero]
  ring

private theorem squareError_bound (A : Finset G) :
    squareError (centered A)≤deviation A+Fintype.card G*|2-(A.card:ℝ)^2/Fintype.card G| := by
  simp only [squareError,centered_conv,deviation]
  calc
    _ ≤ ∑ z : G, (|(reps A z:ℝ)-2|+|2-(A.card:ℝ)^2/Fintype.card G|) := by
      apply sum_le_sum
      intro z _
      convert abs_add_le ((reps A z:ℝ)-2) (2-(A.card:ℝ)^2/Fintype.card G) using 1
      congr 1
      ring
    _ = _ := by simp [sum_add_distrib]

variable {M : ℕ+}

/-- A cyclic interval with a specified starting point and integer length. -/
def arc (x : ZMod M) (w : ℕ) : Finset (ZMod M) := (range w).image fun j : ℕ => x+(j:ZMod M)

private theorem arc_card_le (x : ZMod M) (w : ℕ) : (arc x w).card≤w :=
  card_image_le.trans_eq (card_range _)

theorem arc_card (x : ZMod M) {w : ℕ} (fit : w≤M.val) : (arc x w).card=w := by
  have inj : Set.InjOn (fun j : ℕ => x+(j:ZMod M)) (range w) := by
    intro i hi j hj eq
    have e := congrArg ZMod.val (add_left_cancel eq)
    rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt ((mem_range.mp hi).trans_le fit),
      Nat.mod_eq_of_lt ((mem_range.mp hj).trans_le fit)] at e
    exact e
  exact (card_image_iff.mpr inj).trans (card_range _)

private theorem arc_counts (A : Finset (ZMod M)) (x : ZMod M) (w h : ℕ) (j : ZMod M) (hj : j∈arc 0 h) :
    ((arc (x+(h:ZMod M)) (w-h)).filter (fun i => i-j∈A)).card≤(A∩arc x w).card ∧
    (A∩arc x w).card≤((arc x (w+h)).filter (fun i => i-j∈A)).card := by
  obtain ⟨b,hb,eq⟩ := mem_image.mp hj
  simp only [zero_add] at eq
  subst j
  have bl := mem_range.mp hb
  constructor
  · apply card_le_card_of_injOn (fun i => i-(b:ZMod M))
    · intro i hi
      obtain ⟨hm,ha⟩ := mem_filter.mp hi
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hm
      have tl := mem_range.mp ht
      have sub : b≤h+t := by omega
      apply mem_inter.mpr ⟨ha,mem_image.mpr ⟨h+t-b,mem_range.mpr (by omega),?_⟩⟩
      rw [Nat.cast_sub sub,Nat.cast_add]; abel
    · exact (Equiv.subRight (b:ZMod M)).injective.injOn
  · apply card_le_card_of_injOn (fun i => i+(b:ZMod M))
    · intro i hi
      obtain ⟨ha,hm⟩ := mem_inter.mp hi
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hm
      have tl := mem_range.mp ht
      refine mem_filter.mpr ⟨mem_image.mpr ⟨t+b,mem_range.mpr (by omega),?_⟩,by simpa using ha⟩
      rw [Nat.cast_add]; abel
    · exact (Equiv.addRight (b:ZMod M)).injective.injOn

private theorem mixed_counts (A I J : Finset (ZMod M)) :
    |(∑ j ∈ J, (((I.filter fun i => i-j∈A).card):ℝ))-I.card*J.card*((A.card:ℝ)/M)| ≤
      Real.sqrt (squareError (centered A))*Real.sqrt I.card*Real.sqrt J.card := by
  have e := rectangle_bound (centered A) I J
  rw [sum_comm] at e
  have row (j) : ∑ i ∈ I, centered A (i-j)=((I.filter fun i => i-j∈A).card:ℝ)-
      I.card*((A.card:ℝ)/M) := by
    simp [centered,ind,sum_sub_distrib,Finset.sum_boole,ZMod.card]
  simpa only [row,sum_sub_distrib,sum_const,nsmul_eq_mul,mul_left_comm,mul_assoc] using e


/-- A smoothing window of length `h` tests all cyclic arcs, with an explicit
boundary term and a term from the convolution-square error. -/
theorem arc_discrepancy (A : Finset (ZMod M)) (x : ZMod M) (w h : ℕ)
    (hw : w≤M.val) (hh : h≤M.val) (pos : 0<h) :
    |((A∩arc x w).card:ℝ)-(w:ℝ)*((A.card:ℝ)/M)| ≤
      h*((A.card:ℝ)/M)+Real.sqrt (squareError (centered A))*Real.sqrt (2*(M:ℝ))/Real.sqrt h := by
  let L := arc (x+(h:ZMod M)) (w-h)
  let U := arc x (w+h)
  let J : Finset (ZMod M) := arc 0 h
  let c : ℝ := (A.card:ℝ)/M
  let b : ℝ := Real.sqrt (squareError (centered A))*Real.sqrt (2*(M:ℝ))*Real.sqrt h
  let n : ℝ := (A∩arc x w).card
  let count (I : Finset (ZMod M)) := ∑ j ∈ J, ((I.filter fun i => i-j∈A).card:ℝ)
  have jc : J.card=h := arc_card _ hh
  have lc : L.card=w-h := arc_card _ ((Nat.sub_le ..).trans hw)
  have uc : U.card≤w+h := arc_card_le _ _
  have bounds (I : Finset (ZMod M)) (le : I.card≤2*M.val) :
      |count I-(I.card:ℝ)*h*c|≤b := by
    have e := mixed_counts A I J
    rw [jc] at e
    refine e.trans ?_
    dsimp [b]
    gcongr
    exact_mod_cast le
  have l := (abs_le.mp (bounds L (by rw [lc]; omega))).1
  have u := (abs_le.mp (bounds U (by omega))).2
  have lower : count L≤h*n := by
    have e := sum_le_sum (s:=J) fun j hj => (show (((L.filter fun i => i-j∈A).card):ℝ)≤n by
      dsimp only [L,n]; exact_mod_cast (arc_counts A x w h j hj).1)
    simpa only [sum_const,jc,nsmul_eq_mul] using e
  have upper : h*n≤count U := by
    have e := sum_le_sum (s:=J) fun j hj => (show n≤(((U.filter fun i => i-j∈A).card):ℝ) by
      dsimp only [U,n]; exact_mod_cast (arc_counts A x w h j hj).2)
    simpa only [sum_const,jc,nsmul_eq_mul] using e
  have hp : (0:ℝ)<h := by exact_mod_cast pos
  have cp : 0≤c := by dsimp [c]; positivity
  have hi : (U.card:ℝ)*h*c≤(w+h)*h*c := by gcongr; exact_mod_cast uc
  have lo : (w:ℝ)*h*c≤(L.card+h)*h*c := by
    gcongr
    exact_mod_cast (show w≤L.card+h by rw [lc]; omega)
  have br : b/(h:ℝ)=Real.sqrt (squareError (centered A))*Real.sqrt (2*(M:ℝ))/Real.sqrt h := by
    have hr := Real.sqrt_pos.mpr hp
    have sq := Real.sq_sqrt hp.le
    dsimp [b]
    field_simp
    ring_nf
    rw [sq]
  change |n-w*c|≤h*c+_
  rw [← br,abs_le]
  constructor
  · apply (mul_le_mul_iff_of_pos_right hp).mp
    rw [neg_mul,add_mul,div_mul_cancel₀ _ hp.ne']
    nlinarith
  · apply (mul_le_mul_iff_of_pos_right hp).mp
    rw [add_mul,div_mul_cancel₀ _ hp.ne']
    nlinarith

private theorem error_vanish {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1)) :
    Tendsto (fun i => squareError (centered (A i))/(N i:ℝ)) atTop (𝓝 0) := by
  have dev := deviation_vanish N A big size cover
  have quad : Tendsto (fun i => ((A i).card:ℝ)^2/(N i:ℝ)) atTop (𝓝 2) := by
    simpa only [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sq_sqrt (Nat.cast_nonneg _)] using size.pow 2
  have dom := dev.add ((tendsto_const_nhds (x:=(2:ℝ))).sub quad).abs
  simp only [sub_self,abs_zero,add_zero] at dom
  apply squeeze_zero (fun i => div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)) _ dom
  intro i
  have m : (0:ℝ)<N i := by exact_mod_cast (N i).pos
  have be := div_le_div_of_nonneg_right (squareError_bound (A i)) m.le
  simpa only [squareError,ZMod.card,add_div,mul_div_cancel_left₀ _ m.ne'] using be

/-- For critical-size sets covering a fraction tending to one, the count
in any moving cyclic interval, divided by the square root of the order,
differs from its uniform prediction by a quantity tending to zero. -/
theorem arc_distribution {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    (x : ∀ i, ZMod (N i)) (w : ℕ → ℕ) (width : ∀ i, w i≤(N i).val) :
    Tendsto (fun i => (((A i∩arc (x i) (w i)).card:ℝ)-(w i)*((A i).card/(N i:ℝ)))/Real.sqrt (N i)) atTop (𝓝 0) := by
  let m (i : ℕ) : ℝ := N i
  let E i := squareError (centered (A i))
  let r i := Real.sqrt (E i/m i)
  let h i := ⌈m i*r i⌉₊+1
  have mp (i) : 0 < m i := by dsimp [m]; exact_mod_cast (N i).pos
  have ep (i) : 0≤E i := sum_nonneg fun _ _ => abs_nonneg _
  have rp (i) : 0≤r i := Real.sqrt_nonneg _
  have rl : Tendsto r atTop (𝓝 0) := by
    simpa only [r,E,m,Function.comp_def,Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (error_vanish A big size cover)
  have inv : Tendsto (fun i => 1/m i) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp big)
  have hl : Tendsto (fun i => (h i:ℝ)/m i) atTop (𝓝 0) := by
    have dom := rl.add (inv.const_mul 2)
    simp only [mul_zero,add_zero] at dom
    apply squeeze_zero (fun i => div_nonneg (by positivity) (mp i).le) _ dom
    intro i
    have ceil := Nat.ceil_lt_add_one (mul_nonneg (mp i).le (rp i))
    change ((⌈m i*r i⌉₊+1:ℕ):ℝ)/m i≤_
    rw [Nat.cast_add,Nat.cast_one,div_le_iff₀ (mp i)]
    field_simp [(mp i).ne']
    linarith
  have fit : ∀ᶠ i in atTop, h i≤(N i).val := by
    filter_upwards [hl.eventually_lt_const zero_lt_one] with i hi
    have e := (div_lt_iff₀ (mp i)).mp hi
    change (h i:ℝ)<1*((N i).val:ℝ) at e
    rw [one_mul] at e
    exact_mod_cast e.le
  have eh (i) : E i≤(h i:ℝ)*r i := by
    have lo := Nat.le_ceil (m i*r i)
    have bound : m i*r i≤(h i:ℝ) := by dsimp [h]; push_cast; linarith
    have rt : (r i)^2=E i/m i := Real.sq_sqrt (div_nonneg (ep i) (mp i).le)
    have v := (eq_div_iff (mp i).ne').mp rt
    nlinarith [mul_le_mul_of_nonneg_right bound (rp i)]
  have smooth : Tendsto (fun i => Real.sqrt 2*Real.sqrt (r i)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero,mul_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp rl).const_mul (Real.sqrt 2)
  have dom := (hl.mul size).add smooth
  simp only [zero_mul,add_zero] at dom
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun i => abs_nonneg _) _ dom
  filter_upwards [fit] with i fi
  have hp : (0:ℝ)<h i := by exact_mod_cast Nat.succ_pos _
  have ms := Real.sqrt_pos.mpr (mp i)
  have hs := Real.sqrt_pos.mpr hp
  have D := (div_le_div_of_nonneg_right (arc_discrepancy (A i) (x i) _ _ (width i) fi (Nat.succ_pos _)) ms.le)
  rw [abs_div,abs_of_nonneg ms.le]
  apply D.trans
  rw [add_div]
  apply add_le_add
  · change (h i*((A i).card/(m i)))/Real.sqrt (m i)≤(h i:ℝ)/m i*((A i).card/Real.sqrt (m i))
    exact le_of_eq (by ring)
  · change Real.sqrt (E i)*Real.sqrt (2*m i)/Real.sqrt (h i)/Real.sqrt (m i)≤_
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    have sq := Real.sqrt_le_sqrt (eh i)
    rw [Real.sqrt_mul hp.le] at sq
    field_simp [hs.ne',ms.ne']
    nlinarith [mul_le_mul_of_nonneg_right sq (Real.sqrt_nonneg 2)]

#print axioms rectangle_bound
#print axioms arc_card
#print axioms arc_discrepancy
#print axioms arc_distribution
end Green33ArcDistribution
