import Green51Hyperplane

/-! # Sharpness of the hyperplane threshold by Hamming balls and cylinders -/

open Finset Green53ParityThreshold Green53FoldedCube
open scoped Classical Pointwise
namespace Green51Hyperplane

private theorem bit_cases (u : F) : u=0 ∨ u=1 := by
  fin_cases u <;> first | exact Or.inl rfl | exact Or.inr rfl

private def supportEquiv (d : ℕ) : (Fin d → F) ≃ Finset (Fin d) where
  toFun x := univ.filter (fun j => x j≠0)
  invFun S j := if j∈S then 1 else 0
  left_inv x := by
    funext j
    rcases bit_cases (x j) with h|h <;> simp [h]
  right_inv S := by ext j; simp

/-- Split a binary vector into its active support and its remaining coordinates. -/
def splitSupport (d r : ℕ) :
    (Fin (d+r) → F) ≃ Finset (Fin d) × (Fin r → F) :=
  (Fin.appendEquiv d r).symm.trans ((supportEquiv d).prodCongr (Equiv.refl _))

/-- A radius `k − 1` Hamming ball on `2 * k` active coordinates with `r` free coordinates. -/
def ball (k r : ℕ) : Finset (Fin (2*k+r) → F) :=
  (((univ : Finset (Finset (Fin (2*k)))).filter (fun S => S.card<k)) ×ˢ
    (univ : Finset (Fin r → F))).map (splitSupport (2*k) r).symm.toEmbedding

/-- Membership only depends on the weight of the active coordinates. -/
theorem ball_mem {k r : ℕ} {a : Fin (2*k+r) → F} :
    a∈ball k r ↔ ((splitSupport (2*k) r a).1.card<k) := by
  simp [ball,Finset.mem_map_equiv]

private theorem ball_count (k r : ℕ) :
    2*(ball k r).card+2^r*(2*k).choose k=2^(2*k+r) := by
  have cnt := strict_layers_card (J:=Fin (2*k)) k (Fintype.card_fin _)
  simp only [ball,card_map,card_product,card_univ,Fintype.card_fun,Fintype.card_fin,F,ZMod.card]
  rw [pow_add]
  nlinarith only [congrArg (fun t => t*2^r) cnt]

private theorem prefix_mem {d r : ℕ} (x : Fin (d+r) → F) (j : Fin d) :
    j∈(splitSupport d r x).1 ↔ x (Fin.castAdd r j)≠0 := by
  simp [splitSupport,supportEquiv]

open scoped symmDiff in
/-- Addition on the active coordinates takes symmetric difference of their supports. -/
theorem support_add {d r : ℕ} (x y : Fin (d + r) → F) :
    (splitSupport d r (x + y)).1 = (splitSupport d r x).1 ∆ (splitSupport d r y).1 := by
  ext i
  simp only [mem_symmDiff, prefix_mem, Pi.add_apply]
  rcases bit_cases (x (Fin.castAdd r i)) with hx | hx <;>
    rcases bit_cases (y (Fin.castAdd r i)) with hy | hy <;> simp [hx, hy, ZModModule.add_self]

/-- The zero vector has empty active support. -/
theorem active_zero (d r : ℕ) : (splitSupport d r (0 : Fin (d + r) → F)).1 = ∅ := by
  ext i
  simp [prefix_mem]

/-- The double occupies every active weight through `2 * k − 2` for `k ≥ 1`. -/
theorem ball_sum_iff {k r : ℕ} (z : Fin (2*k+r) → F) :
    z∈ball k r+ball k r ↔ (splitSupport (2*k) r z).1.card+2≤2*k := by
  classical
  constructor
  · rintro h
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp h
    let U := (splitSupport (2*k) r a).1
    let V := (splitSupport (2*k) r b).1
    have sub : (splitSupport (2*k) r (a+b)).1⊆U∪V := by
      intro j hj
      by_contra no
      have zero : a (Fin.castAdd r j)=0 ∧ b (Fin.castAdd r j)=0 := by
        simpa [U,V,prefix_mem] using no
      exact (prefix_mem (a+b) j).mp hj (by simp [zero])
    have hu : U.card<k := ball_mem.mp ha
    have hv : V.card<k := ball_mem.mp hb
    have bound := (card_le_card sub).trans (card_union_le U V)
    omega
  · intro h
    let S := (splitSupport (2*k) r z).1
    obtain ⟨T,sub,size⟩ := exists_subset_card_eq (min_le_right (k-1) S.card)
    let a := (splitSupport (2*k) r).symm (T,0)
    have active : (splitSupport (2*k) r a).1=T := by simp [a]
    have diff : (splitSupport (2*k) r (z+a)).1=S\T := by
      ext j
      have t : a (Fin.castAdd r j)=(if j∈T then 1 else 0) := by simp [a,splitSupport,supportEquiv]
      rw [prefix_mem,mem_sdiff]
      change _ ↔ j∈(splitSupport (2*k) r z).1 ∧ _
      rw [prefix_mem]
      by_cases hj : j∈T
      · have nz := (prefix_mem z j).mp (sub hj)
        have one := (bit_cases _).resolve_left nz
        simp [t,hj,one,ZModModule.add_self]
      · simp [t,hj]
    change S.card+2≤2*k at h
    exact mem_add.mpr ⟨a,ball_mem.mpr (by rw [active]; omega),z+a,
      ball_mem.mpr (by rw [diff,card_sdiff_of_subset sub]; omega),
      by rw [add_left_comm,ZModModule.add_self,add_zero]⟩

private theorem missing_count (k r : ℕ) :
    (ball k r+ball k r)ᶜ.card=2^r*(2*k+1) := by
  classical
  let U : Finset (Fin (2*k)) := univ
  let small := U.powersetCard 0 ∪ U.powersetCard 1
  let far := univ.filter (fun S : Finset (Fin (2*k)) => Sᶜ.card≤1)
  have small_mem (S : Finset (Fin (2*k))) : S∈small ↔ S.card≤1 := by
    simp only [small,U,mem_union,mem_powersetCard,subset_univ,true_and]; omega
  have same : far.card=small.card := by
    apply card_bij (fun S _ => Sᶜ)
    · intro S h; exact (small_mem _).mpr (mem_filter.mp h).2
    · intro S _ T _ eq; simpa using congrArg (fun v : Finset (Fin (2*k)) => vᶜ) eq
    · intro S h
      exact ⟨Sᶜ,by simpa [far] using (small_mem S).mp h,by simp⟩
  have dis : Disjoint (U.powersetCard 0) (U.powersetCard 1) := by
    rw [disjoint_left]; intro S h0 h1
    exact Nat.zero_ne_one ((mem_powersetCard.mp h0).2.symm.trans (mem_powersetCard.mp h1).2)
  have size : small.card=2*k+1 := by
    dsimp only [small]
    rw [card_union_of_disjoint dis,card_powersetCard,card_powersetCard]
    simp [U,Nat.add_comm]
  have eq : (ball k r+ball k r)ᶜ =
      (far ×ˢ (univ : Finset (Fin r → F))).map (splitSupport (2*k) r).symm.toEmbedding := by
    ext z
    simp only [mem_compl,ball_sum_iff,mem_map_equiv,Equiv.symm_symm,mem_product,
      far,mem_filter,mem_univ,true_and,and_true,card_compl,Fintype.card_fin]
    omega
  rw [eq,card_map,card_product,same,size]
  simp [F,Nat.mul_comm]

/-- The top two weight layers meet every affine hyperplane. This uses only the
active coordinates, so the same obstruction holds for a cylinder. -/
private theorem ball_avoids {k r : ℕ} (z : Fin (2*k+r) → F)
    (unique : ∀ i j, z i=0 → z j=0 → i=j) :
    z∉ball k r+ball k r := by
  let S := (splitSupport (2*k) r z).1
  have zero (j : Fin (2*k)) (hj : j∈Sᶜ) : z (Fin.castAdd r j)=0 := by
    simpa [S,prefix_mem] using hj
  have few : Sᶜ.card≤1 := card_le_one.mpr (fun i hi j hj =>
    Fin.castAdd_injective _ _ (unique _ _ (zero i hi) (zero j hj)))
  rw [card_compl,Fintype.card_fin] at few
  intro hz
  have large : S.card+2≤2*k := (ball_sum_iff z).mp hz
  omega

private theorem shell_hits {n : ℕ} {S : AffineSubspace F (Fin n → F)} (a : Fin n → F) (ha : a∈S)
    (dim : n≤Module.finrank F S.direction+1) (y : Fin n → F) :
    y∈S ∨ ∃ i,y+Pi.single i 1∈S := by
  classical
  by_cases hy : y∈S
  · exact Or.inl hy
  right
  have dir (z : Fin n → F) : z-a∈S.direction ↔ z∈S :=
    AffineSubspace.vsub_right_mem_direction_iff_mem ha z
  have out := mt (dir y).mp hy
  obtain ⟨f,nz,ann⟩ := Submodule.exists_dual_map_eq_bot_of_notMem out inferInstance
  have sub : S.direction ≤ f.ker := by
    intro x hx
    have h : f x∈S.direction.map f := ⟨x,hx,rfl⟩
    rwa [ann] at h
  have dimf : Module.finrank F f.ker<n := by
    simpa using Submodule.finrank_lt (s:=f.ker) (fun eq =>
      nz ((LinearMap.ker_eq_top.mp eq) ▸ (rfl : (0 : (Fin n → F) →ₗ[F] F) (y-a)=0)))
  have eq := Submodule.eq_of_le_of_finrank_le sub (by omega)
  obtain ⟨i,ne⟩ : ∃ i,f (Pi.single i (1:F))≠0 := by
    by_contra! none
    apply nz
    have point (j : Fin n) : f (Pi.single j ((y-a) j))=0 := by
      rcases bit_cases ((y-a) j) with h|h <;> simp [h,none]
    rw [←univ_sum_single (y-a),map_sum]; exact sum_eq_zero (fun j _ => point j)
  refine ⟨i,(dir _).mp ?_⟩
  rw [eq,LinearMap.mem_ker]
  have h : y+Pi.single i (1:F)-a=(y-a)+Pi.single i 1 := by abel
  have bit (x : F) (hn : x≠0) : x=1 := (bit_cases x).resolve_left hn
  rw [h,map_add,bit _ nz,bit _ ne]; rfl

private theorem cylinder_no_flat (k r : ℕ) :
    ∀ S : AffineSubspace F (Fin (2*k+r) → F), (∃ x,x∈S) →
      (∀ x∈S,x∈ball k r+ball k r) → Module.finrank F S.direction+1<2*k+r := by
  rintro S ⟨a,ha⟩ sub
  by_contra! hd
  rcases shell_hits a ha hd (fun _ => 1) with h|⟨i,h⟩
  · exact ball_avoids _ (fun j _ hz _ => (one_ne_zero hz).elim) (sub _ h)
  · apply ball_avoids _ _ (sub _ h)
    intro j l hj hl
    have at_i (t : Fin (2*k+r)) (ht : ((fun _ : Fin (2*k+r) => (1:F))+Pi.single i 1 : Fin (2*k+r) → F) t=0) : t=i := by
      by_contra ne; simp [Pi.single_eq_of_ne ne] at ht
    exact (at_i j hj).trans (at_i l hl).symm

/-- The size, missing directions and hyperplane obstruction for the specified cylinder. -/
theorem hamming_ball_data (k r : ℕ) :
    2 * (ball k r).card + 2 ^ r * (2 * k).choose k = 2 ^ (2 * k + r) ∧
    (ball k r + ball k r)ᶜ.card = 2 ^ r * (2 * k + 1) ∧
    ∀ S : AffineSubspace F (Fin (2 * k + r) → F), (∃ x, x ∈ S) →
      (∀ x ∈ S, x ∈ ball k r + ball k r) → Module.finrank F S.direction + 1 < 2 * k + r :=
  ⟨ball_count k r, missing_count k r, cylinder_no_flat k r⟩

/-- The Hamming cylinder at the threshold has exactly the top two active weight
layers missing, with a free choice in every remaining coordinate. -/
theorem hamming_cylinder (k r : ℕ) :
    ∃ A : Finset (Fin (2*k+r) → F),
      2*A.card+2^r*(2*k).choose k=2^(2*k+r) ∧
      (A+A)ᶜ.card=2^r*(2*k+1) ∧
      ∀ S : AffineSubspace F (Fin (2*k+r) → F), (∃ x,x∈S) →
        (∀ x∈S,x∈A+A) → Module.finrank F S.direction+1<2*k+r :=
  ⟨ball k r, hamming_ball_data k r⟩

/-- At the exact threshold there is a cylinder over a Hamming ball whose
double contains no nonempty affine subspace of codimension at most one. -/
theorem extremal_example (n : ℕ) :
    ∃ A : Finset (Fin n → F),
      2*A.card+2^(n%2)*(2*(n/2)).choose (n/2)=2^n ∧
      ∀ S : AffineSubspace F (Fin n → F), (∃ x,x∈S) →
        (∀ x∈S,x∈A+A) → Module.finrank F S.direction+1<n := by
  generalize hk : n/2=k
  generalize hr : n%2=r
  have eq : n=2*k+r := by omega
  rw [eq]; exact ⟨ball k r,ball_count k r,cylinder_no_flat k r⟩


/-- If the third of three covering sets is smaller than a middle layer, one
of the first two doubles contains a linear subspace of codimension at most one. -/
theorem small_third_class {n : ℕ} (A B C : Finset (Fin n → F))
    (cover : A∪B∪C=univ) (small : C.card<2^(n%2)*(2*(n/2)).choose (n/2)) :
    ∃ l : (Fin n → F) →ₗ[F] F,
      (∀ x∈l.ker,x∈A+A) ∨ (∀ x∈l.ker,x∈B+B) := by
  have cnt := card_union_le (A∪B) C
  simp only [cover,card_univ,Fintype.card_fun,Fintype.card_fin,F,ZMod.card] at cnt
  have union := card_union_le A B
  by_cases large : 2^n<2*A.card+2^(n%2)*(2*(n/2)).choose (n/2)
  · obtain ⟨l,h⟩ := hyperplane_above A large
    exact ⟨l,Or.inl (fun _ hx => h hx)⟩
  · obtain ⟨l,h⟩ := hyperplane_above B (by omega)
    exact ⟨l,Or.inr (fun _ hx => h hx)⟩

/-- At equality two disjoint translates with identical doubles can leave a
remainder of exactly the stated size and miss every affine hyperplane. -/
theorem third_class_boundary (n : ℕ) :
    ∃ A B C : Finset (Fin n → F), Disjoint A B ∧ Disjoint (A∪B) C ∧ A∪B∪C=univ ∧
      C.card=2^(n%2)*(2*(n/2)).choose (n/2) ∧ A+A=B+B ∧
      ∀ S : AffineSubspace F (Fin n → F), (∃ x,x∈S) → (∀ x∈S,x∈A+A) →
        Module.finrank F S.direction+1<n := by
  classical
  obtain ⟨A,size,avoid⟩ := extremal_example n
  obtain ⟨z,hz⟩ : ∃ z,z∉A+A := by
    by_contra! full
    have bad := avoid ⊤ ⟨0,by simp⟩ (fun x _ => full x)
    rw [AffineSubspace.direction_top] at bad
    simp at bad
  let B := A.map (Equiv.addLeft z).toEmbedding
  have shift {b : Fin n → F} : b∈B ↔ ∃ a∈A,z+a=b := Finset.mem_map
  have dis : Disjoint A B := by
    rw [disjoint_left]
    intro b hb hs
    obtain ⟨a,ha,rfl⟩ := shift.mp hs
    apply hz
    have eq : z+a+a=z := by rw [add_assoc,ZModModule.add_self,add_zero]
    exact eq ▸ add_mem_add hb ha
  have double : A+A=B+B := by
    ext x; constructor
    · intro hx
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
      exact mem_add.mpr ⟨z+a,shift.mpr ⟨a,ha,rfl⟩,z+b,shift.mpr ⟨b,hb,rfl⟩,by
        rw [add_add_add_comm,ZModModule.add_self,zero_add]⟩
    · intro hx
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
      obtain ⟨c,hc,rfl⟩ := shift.mp ha
      obtain ⟨e,he,rfl⟩ := shift.mp hb
      rw [add_add_add_comm,ZModModule.add_self,zero_add]; exact add_mem_add hc he
  refine ⟨A,B,(A∪B)ᶜ,dis,disjoint_compl_right,sup_compl_eq_top,?_,double,avoid⟩
  rw [card_compl,card_union_of_disjoint dis]
  simp only [B,card_map,Fintype.card_fun,Fintype.card_fin,F,ZMod.card]
  omega

end Green51Hyperplane
#print axioms Green51Hyperplane.ball_mem
#print axioms Green51Hyperplane.support_add
#print axioms Green51Hyperplane.active_zero
#print axioms Green51Hyperplane.ball_sum_iff
#print axioms Green51Hyperplane.hamming_ball_data
#print axioms Green51Hyperplane.hamming_cylinder
#print axioms Green51Hyperplane.extremal_example
#print axioms Green51Hyperplane.small_third_class
#print axioms Green51Hyperplane.third_class_boundary
