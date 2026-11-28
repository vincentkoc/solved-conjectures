import Mathlib

/-! # Simultaneous sign rounding for affine threshold tests -/

open Finset
namespace Green53Threshold
private theorem perturb_box {I : Type*} [Fintype I] (x h : I → ℝ)
    (box : ∀ i, |x i| ≤ 1) (support : ∀ i, h i ≠ 0 → |x i| < 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, |x i+t*h i| ≤ 1 ∧ |x i-t*h i| ≤ 1 := by
  classical
  let step (i : I) := if h i=0 then 1 else (1-|x i|)/(1+|h i|)
  have pos (i : I) : 0 < step i := by
    by_cases hi : h i=0
    · simp [step,hi]
    · simpa only [step,if_neg hi] using div_pos (sub_pos.mpr (support i hi)) (by positivity : 0<1+|h i|)
  let T : Finset ℝ := insert (1:ℝ) (Finset.univ.image step)
  have ne : T.Nonempty := ⟨1,mem_insert_self _ _⟩
  let t := T.min' ne
  have ht : 0<t := by
    obtain hi|hi := mem_insert.mp (T.min'_mem ne)
    · simpa only [t,hi] using (zero_lt_one : (0:ℝ)<1)
    · obtain ⟨i,_,eq⟩ := mem_image.mp hi
      exact (pos i).trans_le eq.le
  refine ⟨t,ht,fun i => ?_⟩
  have hs : t ≤ step i := T.min'_le _ (mem_insert_of_mem (mem_image_of_mem _ (mem_univ i)))
  have mag : t*|h i| ≤ 1-|x i| := by
    by_cases hi : h i=0
    · simp only [hi,abs_zero,mul_zero]; linarith [box i]
    · have le := (le_div_iff₀ (by positivity : 0<1+|h i|)).mp (by simpa only [step,if_neg hi] using hs)
      nlinarith
  have plus := abs_add_le (x i) (t*h i)
  rw [abs_mul,abs_of_pos ht] at plus
  constructor
  · linarith
  · calc
      _ ≤ |x i|+|t*h i| := abs_sub _ _
      _ ≤ 1 := by rw [abs_mul,abs_of_pos ht]; linarith
private theorem extreme_free_kernel {J : Type*} [Fintype J] {r : ℕ}
    (A : (J → ℝ) →ₗ[ℝ] (Fin r → ℝ)) :
    ∃ x : J → ℝ, (∀ i, |x i| ≤ 1) ∧ A x=0 ∧
      ∀ h : J → ℝ, A h=0 → (∀ i, h i ≠ 0 → |x i|<1) → h=0 := by
  classical
  let C : Set (J → ℝ) := Set.Icc (fun _ => (-1:ℝ)) (fun _ => (1:ℝ)) ∩ A ⁻¹' {0}
  have cp : IsCompact C := isCompact_Icc.inter_right (isClosed_singleton.preimage A.continuous_of_finiteDimensional)
  have z : (0:J → ℝ) ∈ C := by
    exact ⟨⟨fun _ => by norm_num,fun _ => by norm_num⟩,map_zero A⟩
  obtain ⟨x,hx⟩ := cp.extremePoints_nonempty ⟨0,z⟩
  obtain ⟨hx,ext⟩ := mem_extremePoints_iff_left.mp hx
  have bd (i : J) : |x i|≤1 := abs_le.mpr ⟨hx.1.1 i,hx.1.2 i⟩
  have ax : A x=0 := hx.2
  refine ⟨x,bd,ax,?_⟩
  intro h ah sp
  obtain ⟨t,ht,pm⟩ := perturb_box x h bd sp
  have pin : x+t•h ∈ C := by
    refine ⟨⟨fun i => (abs_le.mp (pm i).1).1,fun i => (abs_le.mp (pm i).1).2⟩,?_⟩
    change A (x+t•h)=0; simp [ax,ah]
  have min : x-t•h ∈ C := by
    refine ⟨⟨fun i => (abs_le.mp (pm i).2).1,fun i => (abs_le.mp (pm i).2).2⟩,?_⟩
    change A (x-t•h)=0; simp [ax,ah]
  have seg : x ∈ openSegment ℝ (x+t•h) (x-t•h) := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    ext i; simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; ring
  have eq := ext _ pin _ min seg
  funext i
  have ei := congrFun eq i
  change x i + t*h i = x i at ei
  exact (mul_eq_zero.mp (by linarith : t*h i=0)).resolve_left ht.ne'


/-- A point in the centered cube section has at most one free coordinate per row. -/
theorem fractional {J : Type*} [Fintype J] {r : ℕ}
    (A : (J → ℝ) →ₗ[ℝ] (Fin r → ℝ)) :
    ∃ x : J → ℝ, (∀ i, |x i| ≤ 1) ∧ A x=0 ∧
      (univ.filter (fun i => |x i|<1)).card ≤ r := by
  classical
  obtain ⟨x,box,ax,ext⟩ := extreme_free_kernel A
  let S := univ.filter (fun i => |x i|<1)
  let U (j : J) : (S → ℝ) →ₗ[ℝ] ℝ :=
    if h : j∈S then LinearMap.proj ⟨j,h⟩ else 0
  let L := LinearMap.pi U
  have inj : Function.Injective (A.comp L) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v h
    have zero : L v=0 := ext _ h (by
      intro j nonzero
      by_contra! bad
      have out : j∉S := fun hj => (not_lt.mpr bad) (mem_filter.mp hj).2
      apply nonzero
      simp [L,U,out])
    funext j
    have eq := congrFun zero j.val
    simpa [L,U,j.property] using eq
  have bound := (A.comp L).finrank_le_finrank_of_injective inj
  refine ⟨x,box,ax,?_⟩
  change S.card ≤ r
  rw [←Fintype.card_coe]
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using bound


/-- The floating-variables bound for a simultaneous real signing, scaled row by row. -/
theorem sign_balance {J : Type*} [Fintype J] {r : ℕ} (A : Matrix (Fin r) J ℝ)
    (M : Fin r → ℝ) (pos : ∀ i, 0 ≤ M i) (bounds : ∀ i j, |A i j| ≤ M i) :
    ∃ e : J → ℝ, (∀ j, e j=1 ∨ e j = -1) ∧
      ∀ i, |∑ j, A i j * e j| ≤ r*M i := by
  classical
  obtain ⟨x,box,ax,size⟩ := fractional A.mulVecLin
  let S := univ.filter (fun j => |x j|<1)
  let e (j : J) : ℝ := if 0≤x j then 1 else -1
  have signs (j : J) : e j=1 ∨ e j = -1 := by
    by_cases h : 0≤x j <;> simp [e,h]
  have err (j : J) : |e j-x j| ≤ 1 := by
    have h := abs_le.mp (box j)
    by_cases p : 0≤x j
    · rw [show e j = 1 by simp [e,p], abs_le]; constructor <;> linarith
    · rw [show e j = -1 by simp [e,p], abs_le]; constructor <;> linarith
  have outside {j : J} (h : j∉S) : e j=x j := by
    have p : 1 ≤ |x j| := by simpa [S] using h
    have q := (box j).antisymm p
    by_cases hx : 0≤x j
    · simpa [e,hx,abs_of_nonneg hx] using q.symm
    · have m : x j<0 := lt_of_not_ge hx
      rw [abs_of_neg m] at q
      simp only [e,if_neg hx]; linarith
  refine ⟨e,signs,?_⟩
  intro i
  have z : ∑ j, A i j * x j = 0 := congrFun ax i
  have eq : ∑ j, A i j * e j = ∑ j∈S, A i j*(e j-x j) := by
    calc
      _ = ∑ j, A i j*(e j-x j) := by simp only [mul_sub,sum_sub_distrib,z,sub_zero]
      _ = _ := (sum_subset (subset_univ _) (fun j _ hj => by simp [outside hj])).symm
  rw [eq]
  calc
    _ ≤ ∑ j∈S, |A i j*(e j-x j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j∈S, M i := sum_le_sum (fun j _ => by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul (bounds i j) (err j) (abs_nonneg _) (pos i))
    _ = (S.card:ℝ)*M i := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast size) (pos i)


private theorem sign_on {J : Type*} [Fintype J] {r : ℕ} (A : Fin r → J → ℝ)
    (s : Finset J) (M : Fin r → ℝ) (pos : ∀ i, 0 ≤ M i)
    (bound : ∀ i j, j∈s → |A i j|≤M i) :
    ∃ e : J → ℝ, (∀ j, e j=1 ∨ e j= -1) ∧
        ∀ i, |∑ j∈s, A i j*e j| ≤ r*M i := by
  classical
  let a : Matrix (Fin r) J ℝ := fun i j => if j∈s then A i j else 0
  have small (i j) : |a i j| ≤ M i := by
    by_cases h : j∈s
    · simpa [a,h] using bound i j h
    · simpa [a,h] using pos i
  obtain ⟨e,sign,ok⟩ := sign_balance a M pos small
  refine ⟨e,sign,fun i => ?_⟩
  simpa [a,ite_mul,Finset.sum_ite_mem] using ok i

/-- Two independent rounding steps keep both ends of a prescribed sign flip close to the center. -/
theorem two_signs {J : Type*} [Fintype J] [DecidableEq J] {r : ℕ} (A : Fin r → J → ℝ)
    (s t : Finset J) (ts : t ⊆ s) (M : Fin r → ℝ) (pos : ∀ i,0 ≤ M i)
    (bound : ∀ i j, j∈s → |A i j|≤M i) :
    ∃ e : J → ℝ, (∀ j, e j=1 ∨ e j= -1) ∧
      ∀ i, |∑ j∈s, A i j*e j| ≤ (2*r:ℕ)*M i ∧
        |∑ j∈s, A i j*(if j∈t then -e j else e j)| ≤ (2*r:ℕ)*M i := by
  classical
  obtain ⟨f,uf,p⟩ := sign_on A t M pos (fun i j hj => bound i j (ts hj))
  obtain ⟨g,ug,h⟩ := sign_on A (s\t) M pos (fun i j hj => bound i j (mem_sdiff.mp hj).1)
  let e (j : J) := if j∈t then f j else g j
  refine ⟨e,fun j => ?_,fun i => ?_⟩
  · by_cases hj : j∈t
    · simpa only [e,if_pos hj] using uf j
    · simpa only [e,if_neg hj] using ug j
  · have eq : s=t∪(s\t) := (union_sdiff_of_subset ts).symm
    have dis : Disjoint t (s\t) := disjoint_sdiff
    let P := ∑ j∈t, A i j*f j
    let Q := ∑ j∈s\t, A i j*g j
    have total : ∑ j∈s, A i j*e j = P+Q := by
      conv_lhs => rw [eq,sum_union dis]
      congr 1
      · exact sum_congr rfl (fun j hj => by simp [e,hj])
      · exact sum_congr rfl (fun j hj => by simp [e,(mem_sdiff.mp hj).2])
    have flip : ∑ j∈s, A i j*(if j∈t then -e j else e j) = -P+Q := by
      conv_lhs => rw [eq,sum_union dis]
      congr 1
      · dsimp only [P]
        rw [←sum_neg_distrib]
        exact sum_congr rfl (fun j hj => by simp [e,hj])
      · exact sum_congr rfl (fun j hj => by simp [e,(mem_sdiff.mp hj).2])
    rw [total,flip]
    have p' : |P| ≤ r*M i := p i
    have q' : |Q| ≤ r*M i := h i
    have both := abs_add_le P Q
    have flipped := abs_add_le (-P) Q
    rw [abs_neg] at flipped
    push_cast
    constructor <;> linarith


end Green53Threshold

#print axioms Green53Threshold.fractional
#print axioms Green53Threshold.sign_balance
#print axioms Green53Threshold.two_signs
