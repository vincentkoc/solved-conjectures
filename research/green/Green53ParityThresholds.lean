import Green53ThresholdColours

/-! # Repairing sign assignments on an affine parity slice -/

open Finset Green53Threshold
open scoped Pointwise Classical
namespace Green53ParityThreshold

/-- Field of the Boolean cube. -/
abbrev F := ZMod 2
/-- The image of a coordinate subspace has a spanning collection of at most
`finrank F V` coordinate images. These same coordinates suffice for every correction. -/
theorem sparse_correction {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : (J → F) →ₗ[F] V) (U : Finset J) :
    ∃ T ⊆ U, T.card ≤ Module.finrank F V ∧
      ∀ x : J → F, (∀ j, j∉U → x j=0) →
        ∃ y : J → F, (∀ j,j∉T → y j=0) ∧ Q y=Q x := by
  classical
  let col (j : J) := Q (Pi.single j 1)
  let S := col '' (U : Set J)
  obtain ⟨B,sub,hcard,sp,_⟩ := Submodule.exists_finset_span_eq_linearIndepOn F S
  have hit (v : B) : ∃ j∈U,col j=v.val := sub v.property
  choose pre mempre idpre using hit
  let T := univ.image pre
  have tb : T.card ≤ B.card := (card_image_le).trans_eq (by simp)
  refine ⟨T,?_,tb.trans (hcard.le.trans (Submodule.finrank_le _)),?_⟩
  · intro j hj
    obtain ⟨v,_,rfl⟩ := mem_image.mp hj; exact mempre v
  · intro x xs
    have decomp : ∑ j, x j • Pi.single j (1:F) = x := by
      funext j; simp [Finset.sum_apply,Pi.single_apply]
    have ins : Q x∈Submodule.span F S := by
      rw [←decomp,map_sum]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      rw [map_smul]
      by_cases jU : j∈U
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,jU,rfl⟩)
      · simp [xs j jU]
    have br : Set.range (fun v : B => v.val) = (B : Set V) := by ext v; simp
    have hmem : Q x∈Submodule.span F (Set.range (fun v : B => v.val)) := by
      simpa only [br,sp] using ins
    obtain ⟨a,formula⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmem
    let y := ∑ v : B,a v • (Pi.single (pre v) (1:F) : J → F)
    refine ⟨y,?_,?_⟩
    · intro j no
      have diff (v : B) : j ≠ pre v := fun eq => no (mem_image.mpr ⟨v,mem_univ _,eq.symm⟩)
      simp [y,Finset.sum_apply,diff]
    · dsimp only [y]; rw [map_sum]
      simpa only [map_smul,←idpre,col] using formula

/-- Repair both endpoints by the same set of at most `finrank F V` free flips. -/
theorem correct_pair {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : (J → F) →ₗ[F] V) (t : Finset J) (x₀ x z : J → F)
    (pinned : ∀ j∈t,x j=x₀ j) (dir : Q z=0) :
    ∃ (T : Finset J) (v : J → F), Disjoint t T ∧ T.card ≤ Module.finrank F V ∧
      (∀ j,j∉T → v j=0) ∧ Q (x+v)=Q x₀ ∧ Q (x+v+z)=Q x₀ := by
  classical
  let U := univ\t
  obtain ⟨T,sub,card,cover⟩ := sparse_correction Q U
  have supp (j : J) (jn : j∉U) : (x₀-x) j=0 := by
    have jt : j∈t := by simpa [U] using jn
    simp [pinned j jt]
  obtain ⟨v,hv,eq⟩ := cover (x₀-x) supp
  have hit : Q (x+v)=Q x₀ := by rw [map_add,eq,map_sub]; abel
  refine ⟨T,v,?_,card,hv,hit,?_⟩
  · exact Finset.disjoint_left.mpr (by intro j ht hT; exact (mem_sdiff.mp (sub hT)).2 ht)
  · rw [map_add,hit,dir,add_zero]

/-- The positive sign corresponds to zero in the Boolean cube. -/
def decode : Bool ≃ F where
  toFun b := if b then 0 else 1
  invFun a := decide (a=0)
  left_inv b := by cases b <;> decide
  right_inv := by decide
/-- Identify a Boolean signing with its vector over `ZMod 2`. -/
def cube {J : Type*} : (J → Bool) ≃ (J → F) := Equiv.piCongrRight (fun _ => decode)

/-- A nonempty parity slice occupies at least 2^(−dim V) of the cube. -/
theorem slice_size {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : (J → F) →ₗ[F] V) (x₀ : J → F) :
    2^(Fintype.card J) ≤ 2^(Module.finrank F V)*
      (univ.filter (fun x : J → Bool => Q (cube x)=Q x₀)).card := by
  classical
  let G := univ.filter (fun x : J → Bool => Q (cube x)=Q x₀)
  let E : Q.ker ≃ G := {
    toFun := fun u => ⟨cube.symm (x₀+u.val), mem_filter.mpr ⟨mem_univ _,by
      rw [Equiv.apply_symm_apply,map_add,LinearMap.mem_ker.mp u.property,add_zero]⟩⟩
    invFun := fun x => ⟨cube x.val-x₀, by
      rw [LinearMap.mem_ker,map_sub,(mem_filter.mp x.property).2,sub_self]⟩
    left_inv := fun u => by ext j; simp
    right_inv := fun x => by apply Subtype.ext; simp }
  have g : G.card=2^(Module.finrank F Q.ker) := by
    calc
      _ = Fintype.card Q.ker := by rw [Fintype.card_congr E,Fintype.card_coe]
      _ = _ := by simpa only [ZMod.card] using (Module.card_eq_pow_finrank (K:=F) (V:=Q.ker))
  change _ ≤ 2^_*G.card
  rw [g,←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have dim := Q.finrank_range_add_finrank_ker
  have bound := Q.range.finrank_le
  simpa only [Module.finrank_fintype_fun_eq_card] using dim.symm.le.trans (Nat.add_le_add_right bound _)

/-- Flipping at most k signs with individual weight at most M changes the total by at most 2kM. -/
theorem correction_error {J : Type*} [Fintype J] (S : Finset J) (a x y : J → ℝ) (M : ℝ)
    (cap : ∀ j∈S,|a j|≤M) (sx : ∀ j,|x j|≤1) (sy : ∀ j,|y j|≤1)
    (outside : ∀ j,j∉S → y j=x j) :
    |(∑ j,a j*y j)-(∑ j,a j*x j)| ≤ 2*S.card*M := by
  classical
  have eq : (∑ j,a j*y j)-(∑ j,a j*x j) = ∑ j∈S,a j*(y j-x j) := by
    rw [←sum_sub_distrib]
    simp_rw [←mul_sub]
    exact (sum_subset (subset_univ _) (fun j _ hj => by simp [outside j hj])).symm
  rw [eq]
  calc
    _ ≤ ∑ j∈S, |a j*(y j-x j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j∈S, M*2 := sum_le_sum (fun j hj => by
      rw [abs_mul]
      have dist := abs_sub (y j) (x j)
      have small : |y j-x j| ≤ 2 := by linarith [sx j,sy j]
      exact (mul_le_mul_of_nonneg_left small (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (cap j hj) (by norm_num)))
    _ = _ := by simp; ring

private theorem stable_after_repair {M B R S P T : ℝ} (hm : 0≤M)
    (a : |P-B|≤R*M) (b : |T-P|≤S*M) (margin : (R+S+1)*M≤|B|) :
    0≤T ↔ 0≤B := by
  have e : |T-B| ≤ (R+S)*M := by
    have triangle := abs_add_le (T-P) (P-B)
    rw [sub_add_sub_cancel] at triangle
    rw [add_mul]; linarith
  rcases eq_or_lt_of_le hm with he|he
  · subst M; simp only [mul_zero,abs_nonpos_iff,sub_eq_zero] at e; simp [e]
  · have strict : |T-B| < |B| := by nlinarith
    by_cases h : 0≤B
    · rw [abs_of_nonneg h] at strict; have := (abs_lt.mp strict).1
      constructor <;> intro <;> linarith
    · rw [abs_of_neg (lt_of_not_ge h)] at strict; have := (abs_lt.mp strict).2
      constructor <;> intro <;> linarith

private theorem rounded_pair {J : Type*} [Fintype J] {r : ℕ} (A : Fin r → J → ℝ)
    (t : Finset J) (x₀ z : J → F) (zero : ∀ j∈t,z j=0)
    (M : Fin r → ℝ) (nonneg : ∀ i,0≤M i) (cap : ∀ i j,j∉t → |A i j|≤M i) :
    ∃ x : J → F, (∀ j∈t,x j=x₀ j) ∧ ∀ i,
      |(∑ j,A i j*spin (x j)) - ∑ j∈t,A i j*spin (x₀ j)| ≤ (2*r:ℕ)*M i ∧
      |(∑ j,A i j*spin ((x+z) j)) - ∑ j∈t,A i j*spin (x₀ j)| ≤ (2*r:ℕ)*M i := by
  classical
  let U := univ\t
  let D := univ.filter (fun j => z j≠0)
  have du : D⊆U := by
    intro j hj
    exact mem_sdiff.mpr ⟨mem_univ _,fun ht => (mem_filter.mp hj).2 (zero j ht)⟩
  obtain ⟨g,unit,loss⟩ := two_signs A U D du M nonneg (fun i j hj => cap i j (mem_sdiff.mp hj).2)
  let x (j : J) : F := if j∈t then x₀ j else if g j=1 then 0 else 1
  have p j (ht : j∈t) : x j=x₀ j := by simp [x,ht]
  have f j (hj : j∈U) : spin (x j)=g j := by
    have ht := (mem_sdiff.mp hj).2
    rcases unit j with h|h <;> norm_num [spin,x,ht,h]
  refine ⟨x,p,fun i => ?_⟩
  have split (w g' : J → ℝ) (pin : ∀ j∈t,w j=spin (x₀ j)) (free : ∀ j∈U,w j=g' j) :
      (∑ j,A i j*w j) - ∑ j∈t,A i j*spin (x₀ j) = ∑ j∈U,A i j*g' j := by
    have full : univ=t∪U := (union_sdiff_of_subset (subset_univ t)).symm
    have sep : Disjoint t U := disjoint_sdiff
    have a : ∑ j∈t,A i j*w j = ∑ j∈t,A i j*spin (x₀ j) := sum_congr rfl (fun j hj => by rw [pin j hj])
    have b : ∑ j∈U,A i j*w j = ∑ j∈U,A i j*g' j := sum_congr rfl (fun j hj => by rw [free j hj])
    rw [full,sum_union sep,a,b]; abel
  have fst := split (fun j => spin (x j)) g (fun j hj => congrArg spin (p j hj)) f
  have snd := split (fun j => spin ((x+z) j)) (fun j => if j∈D then -g j else g j)
    (fun j hj => by simp [zero j hj,p j hj]) (fun j hj => by simp [D,spin_add,f j hj])
  rw [fst,snd]; exact loss i

/-- On an affine slice, the same threshold cell meets both endpoints of every
direction that vanishes on a bounded number of coordinates. -/
theorem slice_differences {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {r : ℕ} (Q : (J → F) →ₗ[F] V) (anchor : J → F)
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (y : Fin r → Bool),
      t.card ≤ 2*r*(2^(Module.finrank F V)*r*(2*r+2*Module.finrank F V+2))^2 ∧
      ∀ z : J → F, Q z=0 → (∀ j∈t, z j=0) →
        ∃ x : J → F, Q x=Q anchor ∧ Q (x+z)=Q anchor ∧
          readings A b (fun j => spin (x j))=y ∧ readings A b (fun j => spin ((x+z) j))=y := by
  classical
  let s := Module.finrank F V
  let c := 2*r+2*s+1
  let G := univ.filter (fun x : J → Bool => Q (cube x)=Q anchor)
  obtain ⟨t,a,card,ha,mg⟩ := dense_margins r c s G (slice_size Q anchor) A b
  let x₀ := cube a
  have feasible : Q x₀=Q anchor := (mem_filter.mp ha).2
  have same (j : J) : spin (x₀ j)=signBit (a j) := by
    change spin (decode (a j))=signBit (a j)
    cases a j <;> norm_num [decode,spin,signBit]
  let B (i : Fin r) := b i+∑ j∈t, A i j*spin (x₀ j)
  let U := univ\t
  choose M nonneg cap attained using fun i => row_cap U (A i)
  have bound (i j) (hj : j∉t) : |A i j|≤M i := cap i j (by simp [U,hj])
  have margin (i : Fin r) : ((2*r:ℕ)+(2*s:ℕ)+1:ℝ)*M i ≤ |B i| := by
    rcases attained i with h|⟨j,mem,h⟩
    · rw [h,mul_zero]; exact abs_nonneg _
    · have e := mg i j (mem_sdiff.mp mem).2
      dsimp only [B]
      simp only [same]
      dsimp only [c] at e
      push_cast at e ⊢
      rw [←h]
      exact e
  refine ⟨t,fun i => decide (0≤B i),?_,?_⟩
  · simpa [c,s,Nat.add_assoc] using card
  intro z hz zero
  obtain ⟨p,pin,round⟩ := rounded_pair A t x₀ z zero M nonneg bound
  obtain ⟨T,v,dis,ts,supp,h₁,h₂⟩ := correct_pair Q t x₀ p z pin hz
  let R (i : Fin r) (x : J → F) := b i+∑ j,A i j*spin (x j)
  have noise (i : Fin r) (x : J → F) : |R i (x+v)-R i x|≤(2*s:ℕ)*M i := by
    have sp (u : F) : |spin u|≤1 := by by_cases h : u=0 <;> simp [spin,h]
    have e := correction_error T (A i) (fun j => spin (x j)) (fun j => spin ((x+v) j)) (M i)
      (fun j hj => bound i j (fun ht => Finset.disjoint_left.mp dis ht hj))
      (fun j => sp _) (fun j => sp _) (fun j hj => by simp [supp j hj])
    dsimp only [R]
    rw [add_sub_add_left_eq_sub]
    refine e.trans (mul_le_mul_of_nonneg_right ?_ (nonneg i))
    exact_mod_cast Nat.mul_le_mul_left 2 ts
  have side (x : J → F) (rounded : ∀ i, |R i x-B i|≤(2*r:ℕ)*M i) :
      readings A b (fun j => spin ((x+v) j)) = fun i => decide (0≤B i) := by
    funext i
    apply decide_eq_decide.mpr
    exact stable_after_repair (nonneg i) (rounded i) (noise i x) (margin i)
  have first := side p (fun i => by simpa [R,B] using (round i).1)
  have second := side (p+z) (fun i => by simpa [R,B] using (round i).2)
  exact ⟨p+v,h₁.trans feasible,h₂.trans feasible,first,by simpa only [add_right_comm p z v] using second⟩

/-- Allow a common collection of affine parities with arbitrary dependencies.
The codimension bound depends on the number of threshold rows and the number
of linear relations among the parities. -/
theorem parity_threshold_subspace {n N r : ℕ} {C : Type*}
    (E : Green52Complements.Cube n →ₗ[F] Green52Complements.Cube N)
    (h : Green52Complements.Cube N) (A : Fin r → Fin N → ℝ) (b : Fin r → ℝ)
    (colour : (Fin r → Bool) → C) :
    let s := Module.finrank F ((Green52Complements.Cube N) ⧸ E.range)
    ∃ (i : C) (W : Submodule F (Green52Complements.Cube n)),
      n ≤ Module.finrank F W + 2*r*(2^s*r*(2*r+2*s+2))^2 ∧
      (W : Set _) ⊆ {x | colour (readings A b (fun j => spin ((E x+h) j)))=i} +
        {x | colour (readings A b (fun j => spin ((E x+h) j)))=i} := by
  classical
  let Q := E.range.mkQ
  obtain ⟨t,y,size,cover⟩ := slice_differences Q h A b
  let P : Green52Complements.Cube N →ₗ[F] (t → F) := LinearMap.pi (fun i => LinearMap.proj i.val)
  let L := P.comp E
  refine ⟨colour y,L.ker,?_,?_⟩
  · have eq := L.finrank_range_add_finrank_ker
    have bound := L.range.finrank_le
    have dom : Module.finrank F (Green52Complements.Cube n)=n := by simp [Green52Complements.Cube]
    have ran : Module.finrank F (t → F)=t.card := by simp
    rw [dom] at eq
    rw [ran] at bound
    omega
  · intro z hz
    have zero (j : Fin N) (hj : j∈t) : E z j=0 :=
      congrFun (LinearMap.mem_ker.mp hz) (⟨j,hj⟩ : t)
    have dir : Q (E z)=0 := (Submodule.Quotient.mk_eq_zero E.range).mpr ⟨z,rfl⟩
    obtain ⟨x,feasible,_,first,second⟩ := cover (E z) dir zero
    have mem : x-h∈E.range := (Submodule.Quotient.mk_eq_zero E.range).mp
      (show Q (x-h)=0 by rw [map_sub,feasible,sub_self])
    obtain ⟨u,hu⟩ := mem
    have xu : E u+h=x := by rw [hu,sub_add_cancel]
    have xz : E (u+z)+h=x+E z := by rw [map_add,add_right_comm,xu]
    refine ⟨u,?_,u+z,?_,?_⟩
    · simp only [Set.mem_ofPred_eq,xu,first]
    · simp only [Set.mem_ofPred_eq,xz,second]
    · funext j
      exact (by decide : ∀ a b : F,a+(a+b)=b) (u j) (z j)

open Green52Complements in
/-- The Green 53 conclusion when the row count and number of parity relations
are bounded in terms of the number of colours. -/
theorem parity_partition_green53 (rows relations : ℕ → ℕ) :
    ∃ c : ℕ → ℕ, ∀ (n k : ℕ) (as : Fin k → Set (Cube n)),
      (⋃ i, as i) = Set.univ → Pairwise (fun i j => Disjoint (as i) (as j)) →
      (∃ (N : ℕ) (E : Cube n →ₗ[F] Cube N) (h : Cube N)
          (A : Fin (rows k) → Fin N → ℝ) (b : Fin (rows k) → ℝ)
          (colour : (Fin (rows k) → Bool) → Fin k),
        Module.finrank F (Cube N ⧸ E.range) ≤ relations k ∧
        ∀ i, as i={x | colour (readings A b (fun j => spin ((E x+h) j)))=i}) →
      ∃ i, Flat n (c k) (as i) := by
  refine ⟨fun k => 2*rows k*(2^(relations k)*rows k*(2*rows k+2*relations k+2))^2,?_⟩
  rintro n k as _ _ ⟨N,E,h,A,b,colour,rank,classes⟩
  obtain ⟨i,W,dim,sub⟩ := parity_threshold_subspace E h A b colour
  refine ⟨i,W.toAffineSubspace,?_,?_⟩
  · rw [classes]; exact sub
  · rw [Submodule.toAffineSubspace_direction]
    refine dim.trans ?_
    dsimp only
    gcongr
    norm_num

end Green53ParityThreshold

#print axioms Green53ParityThreshold.sparse_correction
#print axioms Green53ParityThreshold.correct_pair
#print axioms Green53ParityThreshold.slice_size

#print axioms Green53ParityThreshold.correction_error
#print axioms Green53ParityThreshold.slice_differences
#print axioms Green53ParityThreshold.parity_threshold_subspace
#print axioms Green53ParityThreshold.parity_partition_green53
