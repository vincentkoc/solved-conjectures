import Green53ParityThresholds

/-! # Intersecting parity-preserving sign changes -/

open Finset Green53ParityThreshold Green53Threshold
open scoped Classical

namespace Green53ParityBlocks

/-- Each sufficiently large block has two parity-preserving flips. The common
support consists of one coordinate, which can carry a single large weight. -/
theorem crossing_flips {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : (J → F) →ₗ[F] V) (B : Finset J)
    (large : 2*Module.finrank F V < B.card) :
    ∃ (j : J) (u v : J → F), j∈B ∧ Q u=0 ∧ Q v=0 ∧
      (∀ k, k∉B → u k=0 ∧ v k=0) ∧
      ∀ k, (u k≠0 ∧ v k≠0) ↔ k=j := by
  classical
  obtain ⟨p,ps,pc,cover₁⟩ := sparse_correction Q B
  obtain ⟨q,qs,qc,cover₂⟩ := sparse_correction Q (B\p)
  have small := (card_union_le (s:=p) (t:=q)).trans (Nat.add_le_add pc qc)
  have card : (p∪q).card < B.card := by omega
  obtain ⟨j,hj⟩ := exists_mem_notMem_of_card_lt_card card
  rcases notMem_union.mp hj.2 with ⟨jp,jq⟩
  let e : J → F := Pi.single j 1
  have supp (k : J) (different : k≠j) : e k=0 := by simp [e,different]
  obtain ⟨v₁,s₁,eq₁⟩ := cover₁ e (fun k h => supp k (fun eq => h (eq ▸ hj.1)))
  obtain ⟨v₂,s₂,eq₂⟩ := cover₂ e (fun k h => supp k (fun eq => h (eq ▸ mem_sdiff.mpr ⟨hj.1,jp⟩)))
  refine ⟨j,e-v₁,e-v₂,hj.1,by rw [map_sub,eq₁,sub_self],by rw [map_sub,eq₂,sub_self],?_,?_⟩
  · intro k hk
    have ek := supp k (fun eq => hk (eq ▸ hj.1))
    have kp : k∉p := fun hp => hk (ps hp)
    have kq : k∉q := fun hq => hk (mem_sdiff.mp (qs hq)).1
    simp [ek,s₁ _ kp,s₂ _ kq]
  · intro k
    by_cases h : k=j
    · subst k; simp [e,s₁ _ jp,s₂ _ jq]
    · have dis : k∉p ∨ k∉q := by
        by_cases hp : k∈p
        · exact Or.inr (fun hq => (mem_sdiff.mp (qs hq)).2 hp)
        · exact Or.inl hp
      rcases dis with hp|hq
      · simp [h,supp k h,s₁ k hp]
      · simp [h,supp k h,s₂ k hq]

/-- Pairwise disjoint coordinate blocks of a specified size inside a finite set. -/
private theorem fixed_blocks {J : Type*} [DecidableEq J] (S : Finset J) (m k : ℕ)
    (size : m*k ≤ S.card) :
    ∃ b : Fin m → Finset J, (∀ i, b i ⊆ S ∧ (b i).card=k) ∧
      Pairwise (fun i j => Disjoint (b i) (b j)) := by
  classical
  have le : Fintype.card (Fin m × Fin k) ≤ Fintype.card S := by simpa using size
  obtain ⟨e⟩ := (Function.Embedding.nonempty_of_card_le le)
  let f (i : Fin m) : Fin k ↪ J :=
    ⟨fun j => (e (i,j)).val, fun _ _ h => congrArg Prod.snd (e.injective (Subtype.ext h))⟩
  let b i := univ.map (f i)
  refine ⟨b,fun i => ⟨?_,by simp [b]⟩,?_⟩
  · intro j hj
    obtain ⟨v,_,rfl⟩ := mem_map.mp hj
    exact (e (i,v)).property
  · intro i j ij
    apply Finset.disjoint_left.mpr
    intro a ai aj
    obtain ⟨u,_,rfl⟩ := mem_map.mp ai
    obtain ⟨v,_,eq⟩ := mem_map.mp aj
    exact ij (congrArg Prod.fst (e.injective (Subtype.ext eq))).symm

/-- Two kernel displacements per block, meeting only at the pivot. -/
structure CrossingFamily (I J : Type*) where
  block : I → Finset J
  separate : Pairwise (fun i j => Disjoint (block i) (block j))
  pivot : I → J
  pivot_mem : ∀ i, pivot i∈block i
  left : I → J → F
  right : I → J → F
  outside : ∀ i j, j∉block i → left i j=0 ∧ right i j=0
  crossing : ∀ i j, (left i j≠0 ∧ right i j≠0) ↔ j=pivot i

/-- In any collection of m(2s+1) heavy coordinates, construct m pairs of
crossing kernel displacements, with one heavy pivot in each block. -/
theorem heavy_crossings {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : (J → F) →ₗ[F] V) (S : Finset J) (m : ℕ)
    (size : m*(2*Module.finrank F V+1) ≤ S.card) :
    ∃ D : CrossingFamily (Fin m) J, ∀ i, D.pivot i∈S ∧ Q (D.left i)=0 ∧ Q (D.right i)=0 := by
  classical
  obtain ⟨b,bs,sep⟩ := fixed_blocks S m _ size
  have large i : 2*Module.finrank F V < (b i).card := by rw [(bs i).2]; omega
  choose j u v mem lu lv outside cross using fun i => crossing_flips Q (b i) (large i)
  exact ⟨⟨b,sep,j,mem,u,v,outside,cross⟩,fun i => ⟨(bs i).1 (mem i),lu i,lv i⟩⟩

variable {I J : Type*} [Fintype I]

/-- The vector added by independently toggling a family of binary displacements. -/
def moves (d : I → J → F) (bits : I → Bool) : J → F :=
  ∑ i,decode (bits i) • d i

theorem moves_kernel {V : Type*} [AddCommGroup V] [Module F V] (Q : (J → F) →ₗ[F] V)
    (d : I → J → F) (ker : ∀ i,Q (d i)=0) (bits : I → Bool) : Q (moves d bits)=0 := by
  simp [moves,map_sum,map_smul,ker]

private theorem moves_on (D : CrossingFamily I J) (d : I → J → F)
    (out : ∀ i j, j∉D.block i → d i j=0) (bits : I → Bool) {i : I} {j : J} (mem : j∈D.block i) :
    moves d bits j=decode (bits i)*d i j := by
  classical
  simp only [moves,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sum_eq_single i
  · intro k _ ne
    have absent : j∉D.block k := fun h => Finset.disjoint_left.mp (D.separate ne) h mem
    simp [out k j absent]
  · simp

private theorem spin_dec (x : F) (b : Bool) :
    spin (x+decode b)=spin x*signBit b := by
  cases b <;> simp [decode,spin_add,signBit]

/-- The effect of the two flips on a weighted row. There is one mixed
coefficient per block, with magnitude equal to the pivot's weight. -/
theorem crossing_row [Fintype J] (D : CrossingFamily I J) (x : J → F) (a : J → ℝ) (b : ℝ) :
    ∃ (offset : (I → Bool) → ℝ) (B C : I → ℝ),
      (∀ i, |C i|=|a (D.pivot i)|) ∧ ∀ l r : I → Bool,
        b+∑ j,a j*spin ((x+moves D.left l+moves D.right r) j) =
          offset l+∑ i,(B i+C i*signBit (l i))*signBit (r i) := by
  classical
  let R i := (D.block i).filter (fun j => D.right i j≠0)
  let S := univ.biUnion R
  let y l := x+moves D.left l
  let B i := ∑ j∈(R i).erase (D.pivot i),a j*spin (x j)
  let C i := a (D.pivot i)*spin (x (D.pivot i))
  let offset l := b+∑ j∈univ\S,a j*spin (y l j)
  have nz {v : F} (h : v≠0) : v=1 := (by decide : ∀ v : ZMod 2,v≠0 → v=1) v h
  have Rj i : D.pivot i∈R i := mem_filter.mpr ⟨D.pivot_mem i,((D.crossing i _).mpr rfl).2⟩
  have left i j (hj : j∈D.block i) l := moves_on D D.left (fun i j no => (D.outside i j no).1) l hj
  have right i j (hj : j∈D.block i) r := moves_on D D.right (fun i j no => (D.outside i j no).2) r hj
  have mass i l : (∑ j∈R i,a j*spin (y l j))=B i+C i*signBit (l i) := by
    rw [← sum_erase_add (R i) (fun j => a j*spin (y l j)) (Rj i)]
    congr 1
    · apply sum_congr rfl
      intro j hj
      obtain ⟨ne,hr⟩ := mem_erase.mp hj
      have zero : D.left i j=0 := by
        by_contra h
        exact ne ((D.crossing i j).mp ⟨h,(mem_filter.mp hr).2⟩)
      simp [y,left i j (mem_filter.mp hr).1 l,zero]
    · have unit := nz (((D.crossing i _).mpr rfl).1)
      simp [C,y,left i _ (D.pivot_mem i) l,unit,spin_dec,mul_assoc]
  refine ⟨offset,B,C,fun i => ?_,fun l r => ?_⟩
  · have hs : |spin (x (D.pivot i))|=1 := by by_cases h : x (D.pivot i)=0 <;> simp [spin,h]
    simp [C,abs_mul,hs]
  · let f (j : J) := a j*spin ((y l+moves D.right r) j)
    have outside (j : J) (hj : j∉S) : moves D.right r j=0 := by
      have z (i : I) : D.right i j=0 := by
        by_contra h
        have mem : j∈D.block i := by by_contra notMem; exact h (D.outside i j notMem).2
        exact hj (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem,h⟩⟩)
      simp [moves,Finset.sum_apply,z]
    have rest : (∑ j∈univ\S,f j)=∑ j∈univ\S,a j*spin (y l j) := by
      apply sum_congr rfl; intro j hj; simp [f,outside j (mem_sdiff.mp hj).2]
    have dis : ∀ i∈(univ : Finset I),∀ k∈univ,i≠k → Disjoint (R i) (R k) := by
      intro i hi k hk ne
      exact (D.separate ne).mono (filter_subset _ _) (filter_subset _ _)
    have part (i : I) : (∑ j∈R i,f j)=(B i+C i*signBit (l i))*signBit (r i) := by
      rw [←mass,sum_mul]
      apply sum_congr rfl
      intro j hj
      obtain ⟨mem,n⟩ := mem_filter.mp hj
      simp [f,right i j mem r,nz n,spin_dec,mul_assoc]
    change b+∑ j,f j=_
    have sumS : (∑ j∈S,f j)=∑ i,(B i+C i*signBit (l i))*signBit (r i) := by
      rw [show S=univ.biUnion R from rfl,sum_biUnion dis]
      exact sum_congr rfl (fun i _ => part i)
    have split := sum_sdiff (s₁:=S) (s₂:=univ) (f:=f) (subset_univ _)
    dsimp only [offset]
    rw [←split,rest,sumS,add_assoc]


/-- With only 2s heavy coordinates, s independent parity checks can cancel a
row of unit weights identically on the check kernel. -/
theorem paired_obstruction (s : ℕ) :
    ∃ (Q : ((Fin s × Bool) → F) →ₗ[F] (Fin s → F)) (a : Fin s × Bool → ℝ),
      Function.Surjective Q ∧ (∀ j,|a j|=1) ∧
      ∀ x : (Fin s × Bool) → F, Q x=0 → (∑ j,a j*spin (x j))=0 := by
  classical
  let Q : ((Fin s × Bool) → F) →ₗ[F] (Fin s → F) :=
    LinearMap.pi (fun i : Fin s => (LinearMap.proj (i,true) : ((Fin s × Bool) → F) →ₗ[F] F)-LinearMap.proj (i,false))
  let a (j : Fin s × Bool) : ℝ := signBit j.2
  refine ⟨Q,a,?_,?_,?_⟩
  · intro v
    refine ⟨fun j => if j.2 then v j.1 else 0,?_⟩
    ext i
    simp [Q]
  · rintro ⟨i,b⟩; cases b <;> norm_num [a,signBit]
  · intro x hx
    have same i : x (i,true)=x (i,false) := by
      have eq := congrFun hx i
      simpa [Q,sub_eq_zero] using eq
    rw [Fintype.sum_prod_type]
    simp [a,signBit,same]

end Green53ParityBlocks
#print axioms Green53ParityBlocks.crossing_flips

#print axioms Green53ParityBlocks.heavy_crossings

#print axioms Green53ParityBlocks.crossing_row
#print axioms Green53ParityBlocks.paired_obstruction
