import Green53ParityOscillation

/-! # Simultaneous threshold margins from independent coordinate blocks -/
open Finset Green53ParityThreshold Green53Threshold
open scoped Classical Pointwise
namespace Green53ParityOscillation

/-- One forbidden choice per coordinate line cannot cover an n-dimensional grid
when each side has more than n points. -/
theorem avoid_grid {I T : Type*} [Fintype I] [Fintype T] (big : Fintype.card I<Fintype.card T)
    (bad : I → (I → T) → Prop)
    (unique : ∀ i x y, bad i x → bad i y → (∀ j,j≠i → x j=y j) → x=y) :
    ∃ x,∀ i,¬bad i x := by
  classical
  let B i := univ.filter (bad i)
  have cap (i : I) : Fintype.card T*(B i).card≤Fintype.card (I → T) := by
    let put (z : T × B i) := Function.update z.2.val i z.1
    have inj : Function.Injective put := by
      rintro ⟨v,x⟩ ⟨w,y⟩ eq
      have vw := congrFun eq i
      have xy : x.val=y.val := unique i x.val y.val (mem_filter.mp x.property).2
        (mem_filter.mp y.property).2 (fun j hj => by
          simpa only [put,Function.update_of_ne hj] using congrFun eq j)
      exact Prod.ext (by simpa only [put,Function.update_self] using vw) (Subtype.ext xy)
    simpa only [Fintype.card_prod,Fintype.card_coe] using Fintype.card_le_of_injective put inj
  have bound : Fintype.card T*(univ.biUnion B).card≤Fintype.card I*Fintype.card (I → T) := calc
    _ ≤ Fintype.card T*∑ i,(B i).card := Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ i,Fintype.card T*(B i).card := mul_sum _ _ _
    _ ≤ ∑ _i : I,Fintype.card (I → T) := sum_le_sum (fun i _ => cap i)
    _ = _ := by simp
  have pos : 0<Fintype.card (I → T) := by rw [Fintype.card_fun]; exact pow_pos (by omega) _
  have strict : (univ.biUnion B).card<(univ : Finset (I → T)).card := by
    rw [card_univ]
    by_contra! contra
    have e := (Nat.mul_le_mul_left (Fintype.card T) contra).trans bound
    exact (Nat.mul_lt_mul_of_pos_right big pos).not_ge e
  obtain ⟨x,hx⟩ := exists_mem_notMem_of_card_lt_card strict
  exact ⟨x,fun i h => hx.2 (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,h⟩⟩)⟩
private theorem select_blocks {J : Type*} [Fintype J] (d : ℕ) :
    ∀ n (A : Fin n → J → ℝ) (S : Finset J), n*d≤S.card →
    ∃ t : Fin n → Finset J, (∀ i,t i⊆S ∧ (t i).card=d) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      ∀ i j,j∈t i → ∀ l∈S,(∀ p,l∉t p) → A i l≤A i j := by
  classical
  intro n
  induction n with
  | zero => intro A S h; exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | succ n ih =>
    intro A S h
    obtain ⟨u,us,uc,order⟩ := largest (A 0) S d
    have cnt : u.card=d := uc.trans (min_eq_left (by rw [Nat.succ_mul] at h; omega))
    have rem : n*d≤(S\u).card := by rw [card_sdiff_of_subset us,cnt,Nat.succ_mul] at *; omega
    obtain ⟨v,vs,vp,vo⟩ := ih (fun i => A i.succ) (S\u) rem
    let t : Fin (n+1) → Finset J := Fin.cases u v
    refine ⟨t,Fin.cases ⟨us,cnt⟩ (fun i => ⟨(vs i).1.trans sdiff_subset,(vs i).2⟩),?_,?_⟩
    · have dis (i : Fin n) : Disjoint u (v i) := Finset.disjoint_left.mpr
        (fun j hj hp => (mem_sdiff.mp ((vs i).1 hp)).2 hj)
      intro i k
      refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) k
      · intro h'; exact (h' rfl).elim
      · intro _; exact dis b
      · intro _; exact (dis a).symm
      · intro ne; exact vp (fun eq => ne (congrArg Fin.succ eq))
    · intro i
      refine Fin.cases ?_ (fun p => ?_) i
      · intro j hj l hl out
        exact order j hj l hl (out 0)
      · intro j hj l hl out
        exact vo p j hj l (mem_sdiff.mpr ⟨hl,out 0⟩) (fun a => out a.succ)

private def stair {r : ℕ} (hi lo : Fin r → ℝ) (k : Fin (r+1)) : ℝ :=
  ∑ l,if l.val<k.val then hi l else lo l

private theorem stair_gap {r : ℕ} (hi lo : Fin r → ℝ) {m : ℝ} (nn : 0 ≤ m)
    (gap : ∀ l, 2*m<hi l-lo l) {u v : Fin (r+1)} (lt : u<v) :
    2*m<stair hi lo v-stair hi lo u := by
  classical
  let l : Fin r := ⟨u.val,by have := v.isLt; change u.val<v.val at lt; omega⟩
  let diff (j : Fin r) := (if j.val<v.val then hi j else lo j)-(if j.val<u.val then hi j else lo j)
  have pos (j : Fin r) : 0≤diff j := by
    by_cases a : j.val<u.val
    · simp [diff,a,a.trans lt]
    · by_cases b : j.val<v.val
      · simp only [diff,if_pos b,if_neg a]; linarith [gap j]
      · simp [diff,a,b]
  have eq : diff l=hi l-lo l := by simp [diff,l,show u.val<v.val from lt]
  calc
    _ < diff l := eq.symm ▸ gap l
    _ ≤ ∑ j,diff j := single_le_sum (fun j _ => pos j) (mem_univ l)
    _ = _ := by simp only [stair,diff,sum_sub_distrib]

private theorem grid_margins {r : ℕ} (m b : Fin r → ℝ)
    (score : Fin r → Fin r → Fin (r+1) → ℝ)
    (gap : ∀ i,0 < m i → ∀ u v, u<v → 2*m i < score i i v-score i i u) :
    ∃ z : Fin r → Fin (r+1), ∀ i, m i ≤ |b i + ∑ j,score i j (z j)| := by
  classical
  let bad (i : Fin r) (z : Fin r → Fin (r+1)) := |b i+∑ j,score i j (z j)| < m i
  obtain ⟨z,safe⟩ := avoid_grid (I:=Fin r) (T:=Fin (r+1)) (by simp) bad (by
    intro i x y bx by' outside
    have ordered (x y : Fin r → Fin (r+1)) (bx : bad i x) (by' : bad i y)
        (off : ∀ j,j≠i → x j=y j) (hi : x i<y i) : False := by
      have ex : ∑ j∈univ.erase i,score i j (x j)=∑ j∈univ.erase i,score i j (y j) :=
        sum_congr rfl (fun j hj => by rw [off _ (mem_erase.mp hj).1])
      change |b i+∑ j,score i j (x j)| < m i at bx
      change |b i+∑ j,score i j (y j)| < m i at by'
      have mi := (abs_nonneg _).trans_lt bx
      rw [←sum_erase_add _ _ (mem_univ i)] at bx by'
      rw [ex] at bx
      rcases abs_lt.mp bx with ⟨xl,xr⟩
      rcases abs_lt.mp by' with ⟨yl,yr⟩
      linarith [gap i mi _ _ hi]
    funext j
    by_cases eq : j=i
    · subst j
      exact le_antisymm (le_of_not_gt (ordered y x by' bx (fun j hj => (outside _ hj).symm)))
        (le_of_not_gt (ordered x y bx by' outside))
    · exact outside j eq)
  exact ⟨z,fun i => le_of_not_gt (safe i)⟩

private theorem join_patches {I J V : Type*} [Fintype I] [Fintype J] [AddCommGroup V] [Module F V]
    (Q : (J → F) →ₗ[F] V) (anchor : J → F) (B : I → Finset J)
    (dis : Pairwise (fun i k => Disjoint (B i) (B k))) (p : I → J → F)
    (pq : ∀ i,Q (p i)=Q anchor) (out : ∀ i j,j∉B i → p i j=anchor j) :
    ∃ x : J → F,Q x=Q anchor ∧ ∀ i j,j∈B i → x j=p i j := by
  classical
  let x := anchor+(∑ i,(p i-anchor))
  refine ⟨x,?_,?_⟩
  · simp only [x,map_add,map_sum,map_sub,pq,sub_self,sum_const_zero,add_zero]
  · intro i j hj
    have only : (∑ k,(p k j-anchor j))=p i j-anchor j := Finset.sum_eq_single (f:=fun k => p k j-anchor j) i
      (fun k _ ne => by
        have no : j∉B k := fun h => Finset.disjoint_left.mp (dis ne) h hj
        rw [out k j no,sub_self])
      (fun h => (h (mem_univ _)).elim)
    simp only [x,Pi.add_apply,Finset.sum_apply,Pi.sub_apply,only]; abel

/-- Select simultaneously feasible coordinates using a number of pinned bits
linear in the check rank and the target margin. -/
theorem grid_slice_margins {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : (J → F) →ₗ[F] V) (anchor : J → F) (r c : ℕ)
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (x : J → F), t.card ≤ r^2*(2*Module.finrank F V+c+1) ∧
      Q x=Q anchor ∧ ∀ i j,j∉t → (c:ℝ)*|A i j|≤|b i+∑ l∈t,A i l*spin (x l)| := by
  classical
  let s := Module.finrank F V
  let d := 2*s+c+1
  let I := Fin r × Fin r
  let e := Fintype.equivFin I
  have size : Fintype.card I=r^2 := by simp [I,pow_two]
  by_cases enough : Fintype.card I*d≤Fintype.card J
  · obtain ⟨u,us,dis,order⟩ := select_blocks d (Fintype.card I)
      (fun v j => |A (e.symm v).1 j|) univ (by simpa using enough)
    let B (i : I) := u (e i)
    let t := univ.biUnion B
    have disjoint : Pairwise (fun i k => Disjoint (B i) (B k)) := fun _ _ neq =>
      dis (e.injective.ne neq)
    have len i : (B i).card=d := (us (e i)).2
    have tc : t.card≤r^2*d := calc
      _ ≤ ∑ i,(B i).card := card_biUnion_le
      _ = _ := by simp only [len,sum_const,card_univ,nsmul_eq_mul,size,Nat.cast_id]
    choose M nn cap attain using fun i => row_cap (univ\t) (A i)
    have large (p : I) (j : J) (hj : j∈B p) : M p.1≤|A p.1 j| := by
      rcases attain p.1 with z|⟨k,hk,eq⟩
      · rw [z]; exact abs_nonneg _
      have none (v) : k∉u v := fun h => (mem_sdiff.mp hk).2 (mem_biUnion.mpr
        ⟨e.symm v,mem_univ _,by simpa only [B,Equiv.apply_symm_apply] using h⟩)
      have le := order (e p) j hj k (mem_univ _) none
      simpa only [Equiv.symm_apply_apply,eq] using le
    let score (i : Fin r) (p : I) (z : J → F) := ∑ j∈B p,A i j*spin (z j)
    have ends (p : I) : ∃ x y : J → F,Q x=Q anchor ∧ Q y=Q anchor ∧
        (∀ j,j∉B p → x j=anchor j ∧ y j=anchor j) ∧
        2*((c:ℝ)+1)*M p.1 ≤ score p.1 p x-score p.1 p y := by
      obtain ⟨T,sub,small,osc⟩ := slice_oscillation Q (B p)
      obtain ⟨x,y,xq,yq,fix,diff⟩ := osc anchor (A p.1)
      have count : c+1≤(B p\T).card := by
        rw [card_sdiff_of_subset sub,len]; dsimp [d,s]; omega
      have mass : ((c:ℝ)+1)*M p.1≤∑ j∈B p\T,|A p.1 j| := calc
        _ ≤ ((B p\T).card:ℝ)*M p.1 := mul_le_mul_of_nonneg_right (by exact_mod_cast count) (nn _)
        _ = ∑ _j∈B p\T,M p.1 := by simp
        _ ≤ _ := sum_le_sum (fun j hj => large p j (mem_sdiff.mp hj).1)
      exact ⟨x,y,xq,yq,fix,by dsimp only [score]; linarith⟩
    choose hi lo hq lq outside jump using ends
    let row (i j : Fin r) (k : Fin (r+1)) := stair
      (fun l => score i (j,l) (hi (j,l))) (fun l => score i (j,l) (lo (j,l))) k
    obtain ⟨z,safe⟩ := grid_margins (fun i => (c:ℝ)*M i) b row (by
      intro i pos u v uv
      have mi : 0 < M i := by by_contra! h; linarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α:=ℝ) c) h]
      apply stair_gap _ _ pos.le _ uv
      intro l
      have e := jump (i,l)
      change 2*((c:ℝ)+1)*M i≤_ at e
      linarith)
    let pick (p : I) := if p.2.val<(z p.1).val then hi p else lo p
    obtain ⟨x,xq,agree⟩ := join_patches Q anchor B disjoint pick (fun p => by
      dsimp only [pick]; split <;> solve | exact hq _ | exact lq _)
      (fun p j hj => by dsimp only [pick]; split <;> solve | exact (outside _ _ hj).1 | exact (outside _ _ hj).2)
    refine ⟨t,x,tc,xq,?_⟩
    intro i j hj
    have same : (∑ j∈t,A i j*spin (x j))=∑ k,row i k (z k) := calc
      _ = ∑ p : I,∑ j∈B p,A i j*spin (x j) := sum_biUnion (fun a _ b _ ne => disjoint ne)
      _ = ∑ p : I,score i p (pick p) := sum_congr rfl (fun p _ => sum_congr rfl
        (fun j hj => by rw [agree p j hj]))
      _ = ∑ k,row i k (z k) := by
        rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro k hk
        apply sum_congr rfl; intro l hl
        dsimp only [pick]
        split <;> rfl
    rw [same]
    exact (mul_le_mul_of_nonneg_left (cap i j (mem_sdiff.mpr ⟨mem_univ _,hj⟩))
      (Nat.cast_nonneg c)).trans (safe i)
  · refine ⟨univ,anchor,?_,rfl,by simp⟩
    rw [card_univ]; rw [size] at enough
    exact (not_le.mp enough).le

open Green52Complements in
/-- The codimension is linear in the number of relations for each row count,
and cubic in the row count when the number of relations is fixed. -/
theorem linear_relation_subspace {n N r : ℕ} {C : Type*}
    (E : Cube n →ₗ[F] Cube N) (h : Cube N) (A : Fin r → Fin N → ℝ) (b : Fin r → ℝ)
    (colour : (Fin r → Bool) → C) :
    let s := Module.finrank F (Cube N ⧸ E.range)
    ∃ (i : C) (W : Submodule F (Cube n)),
      n ≤ Module.finrank F W + r^2*(4*s+2*r+2) ∧
      (W : Set _) ⊆ {x | colour (readings A b (fun j => spin ((E x+h) j)))=i} +
        {x | colour (readings A b (fun j => spin ((E x+h) j)))=i} := by
  let s := Module.finrank F (Cube N ⧸ E.range)
  obtain ⟨t,x,card,hx,mg⟩ := grid_slice_margins E.range.mkQ h r (2*r+2*s+1) A b
  obtain ⟨y,cover⟩ := slice_of_margin E.range.mkQ h A b t x hx mg
  obtain ⟨i,W,dim,sub⟩ := subspace_of_coordinates E h A b colour t y cover
  refine ⟨i,W,dim.trans (Nat.add_le_add_left (card.trans_eq ?_) _),sub⟩
  dsimp only [s]; ring

open Green52Complements in
/-- Transfer the linear relation estimate to the partition formulation of Green 53. -/
theorem linear_relation_partition (r s n k : ℕ) (as : Fin k → Set (Cube n))
    (_cover : (⋃ i, as i)=Set.univ) (_disjoint : Pairwise (fun i j => Disjoint (as i) (as j)))
    (tests : ∃ (N : ℕ) (E : Cube n →ₗ[F] Cube N) (h : Cube N)
      (A : Fin r → Fin N → ℝ) (b : Fin r → ℝ) (colour : (Fin r → Bool) → Fin k),
      Module.finrank F (Cube N ⧸ E.range) ≤ s ∧
      ∀ i, as i={x | colour (readings A b (fun j => spin ((E x+h) j)))=i}) :
    ∃ i, Flat n (r^2*(4*s+2*r+2)) (as i) := by
  obtain ⟨N,E,h,A,b,colour,rank,classes⟩ := tests
  obtain ⟨i,W,dim,sub⟩ := linear_relation_subspace E h A b colour
  refine ⟨i,W.toAffineSubspace,?_,?_⟩
  · rw [classes]; exact sub
  · rw [Submodule.toAffineSubspace_direction]; exact dim.trans (by gcongr)

end Green53ParityOscillation
#print axioms Green53ParityOscillation.avoid_grid

#print axioms Green53ParityOscillation.grid_slice_margins
#print axioms Green53ParityOscillation.linear_relation_subspace
#print axioms Green53ParityOscillation.linear_relation_partition
