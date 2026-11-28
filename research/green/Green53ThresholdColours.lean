import Green53ThresholdRounding
import Green52Complements

/-! # Colour classes determined by affine thresholds in a common basis -/

open Finset
open scoped Classical Pointwise
namespace Green53Threshold
private theorem largest {J : Type*} (a : J → ℝ) (s : Finset J) (k : ℕ) :
    ∃ t ⊆ s, t.card = min k s.card ∧ ∀ i∈t, ∀ j∈s, j∉t → a j ≤ a i := by
  classical
  induction k generalizing s with
  | zero => exact ⟨∅,empty_subset _,by simp,by simp⟩
  | succ k ih =>
    rcases s.eq_empty_or_nonempty with rfl|hs
    · exact ⟨∅,by simp,by simp,by simp⟩
    obtain ⟨i,hi,hmax⟩ := s.exists_max_image a hs
    obtain ⟨t,ht,hcard,htop⟩ := ih (s.erase i)
    have no : i∉t := fun mem => notMem_erase i s (ht mem)
    refine ⟨insert i t,insert_subset hi (ht.trans (erase_subset _ _)),?_,?_⟩
    · rw [card_insert_of_notMem no,hcard,card_erase_of_mem hi]
      have := card_pos.mpr hs
      omega
    · intro b hb j hj hnot
      rcases mem_insert.mp hb with rfl|hb
      · exact hmax _ hj
      · exact htop b hb j (mem_erase.mpr ⟨fun h => hnot (h ▸ mem_insert_self i t),hj⟩)
          (fun h => hnot (mem_insert_of_mem h))
private theorem pin_large {J : Type*} (a : J → ℝ) (s : Finset J) (b : ℝ) (h : ℕ) :
    ∃ (t : Finset J) (e : J → ℝ) (M : ℝ), t ⊆ s ∧ t.card ≤ h ∧
      (∀ j, e j=1 ∨ e j= -1) ∧ 0 ≤ M ∧
      (∀ j ∈ s, j∉t → |a j| ≤ M) ∧ (h:ℝ)*M ≤ |b+∑ j∈t, a j*e j| := by
  classical
  obtain ⟨t,sub,card,order⟩ := largest (fun j => |a j|) s h
  let d (y : ℝ) : ℝ := if 0≤y then 1 else -1
  have unit (y : ℝ) : d y=1 ∨ d y= -1 := by by_cases h : 0≤y <;> simp [d,h]
  have mul (y : ℝ) : y*d y=|y| := by by_cases h : 0≤y <;> simp [d,h,abs_of_nonneg,abs_of_neg,lt_of_not_ge]
  let e (j : J) := d (a j)*d b
  have sign_e (j : J) : e j=1 ∨ e j= -1 := by
    rcases unit (a j) with u|u <;> rcases unit b with v|v <;> simp [e,u,v]
  have nonneg : 0 ≤ ∑ j∈t, |a j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have aligned : (∑ j∈t, |a j|) ≤ |b+∑ j∈t, a j*e j| := by
    simp only [e,←mul_assoc,mul,←sum_mul]
    by_cases hb : 0≤b
    · rw [show d b=1 by simp [d,hb],mul_one,abs_of_nonneg (add_nonneg hb nonneg)]; linarith
    · rw [show d b= -1 by simp [d,hb],mul_neg_one,abs_of_nonpos (by linarith)]; linarith
  have le := card.trans_le (min_le_left _ _)
  by_cases hs : (s\t).Nonempty
  · obtain ⟨j,hj,maxj⟩ := (s\t).exists_max_image (fun j => |a j|) hs
    have hj' := mem_sdiff.mp hj
    have lt : t.card<s.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, fun eq => hj'.2 (eq ▸ hj'.1)⟩)
    have eq : t.card=h := by omega
    refine ⟨t,e,|a j|,sub,le,sign_e,abs_nonneg _,fun l hl hlt => maxj l (mem_sdiff.mpr ⟨hl,hlt⟩),?_⟩
    calc
      _ = ∑ _i∈t, |a j| := by simp [eq]
      _ ≤ ∑ i∈t, |a i| := sum_le_sum (fun i hi => order i hi j hj'.1 hj'.2)
      _ ≤ _ := aligned
  · exact ⟨t,e,0,sub,le,sign_e,le_rfl,fun j hj h => (hs ⟨j,mem_sdiff.mpr ⟨hj,h⟩⟩).elim,
        by rw [mul_zero]; exact abs_nonneg _⟩

private def pinCount (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => 2*pinCount c r+c

private theorem stabilize {J : Type*} (c : ℕ) (s : Finset J) {r : ℕ}
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (e : J → ℝ), t ⊆ s ∧ t.card ≤ pinCount c r ∧
      (∀ j, e j=1 ∨ e j= -1) ∧ ∀ i j, j∈s → j∉t →
        (c:ℝ)*|A i j| ≤ |b i+∑ l∈t, A i l*e l| := by
  classical
  induction r generalizing s with
  | zero => exact ⟨∅,fun _ => 1,empty_subset _,by simp [pinCount],by simp,fun i => i.elim0⟩
  | succ r ih =>
    let k := pinCount c r
    obtain ⟨u,f,M,us,uc,fu,hm,bounds,margin⟩ := pin_large (A 0) s (b 0) (k+c)
    obtain ⟨v,g,vs,vc,gu,hmarg⟩ := ih (s\u) (fun i => A i.succ)
      (fun i => b i.succ + ∑ l∈u, A i.succ l*f l)
    let e (j : J) := if j∈u then f j else g j
    have dis : Disjoint u v := Finset.disjoint_left.mpr (by intro j hj hv; exact (mem_sdiff.mp (vs hv)).2 hj)
    have eq (i : Fin (r+1)) : ∑ l∈u∪v, A i l*e l =
        (∑ l∈u,A i l*f l) + ∑ l∈v,A i l*g l := by
      rw [sum_union dis]
      congr 1
      · exact sum_congr rfl (fun j hj => by simp [e,hj])
      · exact sum_congr rfl (fun j hj => by simp [e,(mem_sdiff.mp (vs hj)).2])
    refine ⟨u∪v,e,union_subset us (vs.trans sdiff_subset),?_,?_,?_⟩
    · rw [card_union_of_disjoint dis, pinCount]
      change u.card + v.card ≤ 2*k+c
      change v.card ≤ k at vc
      omega
    · intro j
      by_cases h : j∈u
      · simpa only [e,if_pos h] using fu j
      · simpa only [e,if_neg h] using gu j
    · intro i j hs jnot
      have ju : j∉u := fun hj => jnot (mem_union_left _ hj)
      have jv : j∉v := fun hj => jnot (mem_union_right _ hj)
      rw [eq,←add_assoc]
      refine Fin.cases ?_ (fun i => hmarg i j (mem_sdiff.mpr ⟨hs,ju⟩) jv) i
      have absG : ∀ l, |g l|=1 := fun l => (gu l).elim (fun h => by simp [h]) (fun h => by simp [h])
      have loss : |∑ l∈v, A 0 l*g l| ≤ (k:ℝ)*M := by
        calc
          _ ≤ ∑ l∈v, |A 0 l*g l| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _l∈v, M := sum_le_sum (fun l hl => by
            have h := mem_sdiff.mp (vs hl)
            simpa only [abs_mul,absG,mul_one] using bounds l h.1 h.2)
          _ = (v.card:ℝ)*M := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast vc) hm
      let B := b 0+∑ l∈u, A 0 l*f l
      let G := ∑ l∈v,A 0 l*g l
      have tri : |B| ≤ |B+G| + |G| := by simpa using abs_add_le (B+G) (-G)
      dsimp only [B,G] at tri
      have desired := mul_le_mul_of_nonneg_left (bounds j hs ju) (Nat.cast_nonneg (α:=ℝ) c)
      push_cast at margin
      linarith [add_mul (k:ℝ) (c:ℝ) M]

private theorem row_cap {J : Type*} (s : Finset J) (a : J → ℝ) :
    ∃ M : ℝ, 0≤M ∧ (∀ j∈s, |a j|≤M) ∧ (M=0 ∨ ∃ j∈s, |a j|=M) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl|hs
  · exact ⟨0,le_rfl,by simp,Or.inl rfl⟩
  obtain ⟨j,h,m⟩ := s.exists_max_image (fun j => |a j|) hs
  exact ⟨_,abs_nonneg _,m,Or.inr ⟨j,h,rfl⟩⟩


private theorem stable_side {B x m u : ℝ} (hm : 0 ≤ m) (noise : |x| ≤ u*m)
    (margin : (u+1)*m ≤ |B|) : 0 ≤ B+x ↔ 0 ≤ B := by
  rcases eq_or_lt_of_le hm with h|h
  · subst m
    simp only [mul_zero,abs_nonpos_iff] at noise
    simp [noise]
  · have gap : |x| < |B| := by nlinarith
    have bounds := abs_le.mp noise
    by_cases hb : 0 ≤ B
    · rw [abs_of_nonneg hb] at gap
      have := (abs_lt.mp gap).1
      constructor <;> intro <;> linarith
    · rw [abs_of_neg (lt_of_not_ge hb)] at gap
      have := (abs_lt.mp gap).2
      constructor <;> intro <;> linarith

/-- The binary vector recording the weak positive side of each affine test. -/
noncomputable def readings {J : Type*} [Fintype J] {r : ℕ}
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) (x : J → ℝ) : Fin r → Bool :=
  fun i => decide (0 ≤ b i + ∑ j, A i j*x j)

/-- Every flip outside a fixed set of coordinates can be realized within the same joint cell. -/
theorem sign_cell {J : Type*} [Fintype J] [DecidableEq J] {r : ℕ}
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (y : Fin r → Bool), t.card ≤ (2*r+1)*(2^r-1) ∧
      ∀ (d : Finset J), Disjoint d t →
        ∃ e : J → ℝ, (∀ j, e j=1 ∨ e j= -1) ∧ readings A b e=y ∧
          readings A b (fun j => if j∈d then -e j else e j)=y := by
  classical
  let c := 2*r+1
  obtain ⟨t,f,_,tc,fs,mar⟩ := stabilize c (univ : Finset J) A b
  let U := univ \ t
  let B (i : Fin r) := b i+∑ j∈t,A i j*f j
  choose M nonneg cap attained using fun i => row_cap U (A i)
  have buffer i : ((2*r:ℕ):ℝ)*M i + M i ≤ |B i| := by
    rcases attained i with h|⟨j,hj,h⟩
    · simp [h]
    · have ref := mar i j (mem_univ j) (mem_sdiff.mp hj).2
      rw [h] at ref
      simpa [B,c,Nat.cast_add,add_mul] using ref
  have count (k : ℕ) : pinCount c k+c = c*2^k := by
    induction k with
    | zero => simp [pinCount]
    | succ k ih => simp only [pinCount,pow_succ]; nlinarith
  have count' := count r
  have positive : 0 < 2^r := pow_pos (by decide) _
  have card : t.card ≤ (2*r+1)*(2^r-1) := by
    change t.card ≤ c*(2^r-1)
    rw [Nat.mul_sub_left_distrib,Nat.mul_one]
    omega
  refine ⟨t,fun i => decide (0 ≤ B i),card,?_⟩
  intro d dis
  have du : d⊆U := fun j hj => mem_sdiff.mpr ⟨mem_univ _,fun h => Finset.disjoint_left.mp dis hj h⟩
  obtain ⟨g,gs,loss⟩ := two_signs A U d du M nonneg cap
  let x (j : J) := if j∈t then f j else g j
  have cut : (univ : Finset J)=t∪U := (union_sdiff_of_subset (subset_univ t)).symm
  have sep : Disjoint t U := disjoint_sdiff
  have split (w w' : J → ℝ) (p : ∀ j∈t, w j = f j) (h : ∀ j∈U,w j=w' j) (i : Fin r) :
      b i+∑ j,A i j*w j = B i+∑ j∈U,A i j*w' j := by
    conv_lhs => rw [cut,sum_union sep]
    rw [←add_assoc]
    have ep : ∑ j∈t,A i j*w j = ∑ j∈t,A i j*f j := sum_congr rfl (fun j hj => by rw [p j hj])
    have ef : ∑ j∈U,A i j*w j = ∑ j∈U,A i j*w' j := sum_congr rfl (fun j hj => by rw [h j hj])
    rw [ep,ef]
  have pin j (hj : j∈t) : x j=f j := by simp [x,hj]
  have free j (hj : j∈U) : x j=g j := by simp [x,(mem_sdiff.mp hj).2]
  refine ⟨x,fun j => ?_,?_,?_⟩
  · by_cases h : j∈t
    · simpa only [x,if_pos h] using fs j
    · simpa only [x,if_neg h] using gs j
  · funext i
    apply decide_eq_decide.mpr
    rw [split x g pin free i]
    apply stable_side (nonneg i) (loss i).1
    simpa only [add_mul,one_mul] using buffer i
  · funext i
    apply decide_eq_decide.mpr
    let v (j : J) := if j∈d then -x j else x j
    let w (j : J) := if j∈d then -g j else g j
    have p j (hj : j∈t) : v j=f j := by
      have h : j∉d := fun hd => Finset.disjoint_left.mp dis hd hj
      simp [v,h,pin j hj]
    have h j (hj : j∈U) : v j=w j := by simp [v,w,free j hj]
    rw [split v w p h i]
    apply stable_side (nonneg i) (loss i).2
    simpa only [add_mul,one_mul] using buffer i

open Green52Complements
/-- The real sign assigned to a binary coordinate. -/
def spin (v : ZMod 2) : ℝ := if v=0 then 1 else -1

private theorem spin_add (u v : ZMod 2) :
    spin (u+v) = if v≠0 then -spin u else spin u := by
  have binary : ∀ x : ZMod 2, x=0 ∨ x=1 := by decide
  have two : (1:ZMod 2)+1=0 := by decide
  rcases binary u with rfl|rfl <;> rcases binary v with rfl|rfl <;> norm_num [spin,two]
  decide

/-- A joint threshold cell realizes every difference vanishing on the selected coordinates. -/
theorem coordinate_differences {n r : ℕ} (A : Fin r → Fin n → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset (Fin n)) (y : Fin r → Bool), t.card ≤ (2*r+1)*(2^r-1) ∧
      ∀ z : Cube n, (∀ j∈t,z j=0) →
        z ∈ {x : Cube n | readings A b (fun j => spin (x j))=y} +
          {x : Cube n | readings A b (fun j => spin (x j))=y} := by
  classical
  obtain ⟨t,y,size,cell⟩ := sign_cell A b
  refine ⟨t,y,size,?_⟩
  intro z zero
  let d := univ.filter (fun j => z j≠0)
  have dis : Disjoint d t := Finset.disjoint_left.mpr (by
    intro j hd ht; exact (mem_filter.mp hd).2 (zero j ht))
  obtain ⟨e,se,first,second⟩ := cell d dis
  let x (j : Fin n) : ZMod 2 := if e j=1 then 0 else 1
  have sides (j : Fin n) : spin (x j)=e j := by
    rcases se j with h|h <;> norm_num [spin,x,h]
  have toggle (j : Fin n) : spin (x j+z j)=(if j∈d then -e j else e j) := by
    simp [spin_add,sides,d]
  refine ⟨x,?_,x+z,?_,?_⟩
  · simpa only [Set.mem_ofPred_eq,sides] using first
  · simpa only [Set.mem_ofPred_eq,Pi.add_apply,toggle] using second
  · funext j
    exact (by decide : ∀ u v : ZMod 2, u+(u+v)=v) (x j) (z j)

/-- In any common linear basis, every readout of r thresholds has a colour whose
double contains a linear subspace of codimension at most (2r+1)(2^r−1). -/
theorem threshold_subspace {n r : ℕ} {C : Type*}
    (A : Fin r → Fin n → ℝ) (b : Fin r → ℝ) (L : Cube n ≃ₗ[ZMod 2] Cube n)
    (colour : (Fin r → Bool) → C) :
    ∃ (i : C) (W : Submodule (ZMod 2) (Cube n)),
      n ≤ Module.finrank (ZMod 2) W + (2*r+1)*(2^r-1) ∧
      (W : Set (Cube n)) ⊆
        {x | colour (readings A b (fun j => spin (L x j)))=i} +
        {x | colour (readings A b (fun j => spin (L x j)))=i} := by
  classical
  obtain ⟨t,y,size,cover⟩ := coordinate_differences A b
  let P : Cube n →ₗ[ZMod 2] (t → ZMod 2) := LinearMap.pi (fun i => LinearMap.proj i.val)
  let H := P.comp L.toLinearMap
  refine ⟨colour y,H.ker,?_,?_⟩
  · have eq := H.finrank_range_add_finrank_ker
    have bound := Submodule.finrank_le (LinearMap.range H)
    have dom : Module.finrank (ZMod 2) (Cube n)=n := by simp [Cube]
    have ran : Module.finrank (ZMod 2) (t → ZMod 2)=t.card := by simp
    rw [dom] at eq
    rw [ran] at bound
    omega
  · intro z hz
    have zero (j : Fin n) (hj : j∈t) : L z j=0 :=
      congrFun (LinearMap.mem_ker.mp hz) (⟨j,hj⟩ : t)
    obtain ⟨x,hx,w,hw,add⟩ := cover (L z) zero
    change readings A b (fun j => spin (x j))=y at hx
    change readings A b (fun j => spin (w j))=y at hw
    refine ⟨L.symm x,?_,L.symm w,?_,?_⟩
    · simp only [Set.mem_ofPred_eq,LinearEquiv.apply_symm_apply,hx]
    · simp only [Set.mem_ofPred_eq,LinearEquiv.apply_symm_apply,hw]
    · apply L.injective; simpa only [map_add,LinearEquiv.apply_symm_apply] using add

/-- The Green 53 partition conclusion for colourings depending on a bounded
number of threshold tests in any single basis. -/
theorem threshold_partition_green53 (rows : ℕ → ℕ) :
    ∃ c : ℕ → ℕ, ∀ (n k : ℕ) (as : Fin k → Set (Cube n)),
      (⋃ i, as i) = Set.univ → Pairwise (fun i j => Disjoint (as i) (as j)) →
      (∃ (A : Fin (rows k) → Fin n → ℝ) (b : Fin (rows k) → ℝ)
          (L : Cube n ≃ₗ[ZMod 2] Cube n) (colour : (Fin (rows k) → Bool) → Fin k),
        ∀ i, as i={x | colour (readings A b (fun j => spin (L x j)))=i}) →
      ∃ i, Flat n (c k) (as i) := by
  refine ⟨fun k => (2*rows k+1)*(2^(rows k)-1),?_⟩
  rintro n k as _ _ ⟨A,b,L,colour,classes⟩
  obtain ⟨i,W,dim,sub⟩ := threshold_subspace A b L colour
  refine ⟨i,W.toAffineSubspace,?_,?_⟩
  · rw [classes]; exact sub
  · rw [Submodule.toAffineSubspace_direction]
    exact dim

end Green53Threshold

#print axioms Green53Threshold.sign_cell
#print axioms Green53Threshold.coordinate_differences
#print axioms Green53Threshold.threshold_subspace
#print axioms Green53Threshold.threshold_partition_green53
