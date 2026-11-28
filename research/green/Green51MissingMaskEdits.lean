import Green51DirectionDeletion

/-! # Editing a binary set to prescribe missing directions -/

namespace Green51MissingMasks
open Finset Green53ParityThreshold
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

theorem prescribe (H X J : Finset G) (outside : J ⊆ (H+H)ᶜ)
    (small : ∀ B ⊆ H, (H \ B).card ≤ X.card * J.card → B+B = H+H)
    (within : X+X ⊆ H+H)
    (cover : ∀ z ∈ (H+H)ᶜ, ∃ x ∈ X, x+z ∈ H)
    (unique : ∀ x ∈ X, ∀ z ∈ (H+H)ᶜ, ∀ y ∈ X, ∀ w ∈ (H+H)ᶜ, x+z = y+w → z=w) :
    ∃ A : Finset G, (A+A)ᶜ = J ∧ H.card ≤ A.card + X.card * J.card ∧
      (H \ A).card ≤ X.card * J.card ∧ (A \ H).card ≤ X.card := by
  classical
  let B := H \ (X+J)
  let A := B ∪ X
  have bh : B ⊆ H := sdiff_subset
  have removed : H \ B ⊆ X+J := by
    intro u hu
    obtain ⟨inH, outB⟩ := mem_sdiff.mp hu
    by_contra no
    exact outB (mem_sdiff.mpr ⟨inH, no⟩)
  have limit := (card_le_card removed).trans card_add_le
  have intact := small B bh limit
  have spare := card_sdiff_add_card_eq_card bh
  have subA : B ⊆ A := subset_union_left
  have back (x z : G) : x + (x+z) = z := by rw [←add_assoc, ZModModule.add_self, zero_add]
  have forbidden {b x : G} (hb : b ∈ B) (hx : x ∈ X) (j : x+b ∈ J) : False :=
    (mem_sdiff.mp hb).2 (mem_add.mpr ⟨x,hx,x+b,j,back x b⟩)
  have cut : H \ A ⊆ H \ B := by
    intro x hx
    obtain ⟨h,n⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨h,fun b => n (subA b)⟩
  have fresh : A \ H ⊆ X := by
    intro x hx
    obtain ⟨h,n⟩ := mem_sdiff.mp hx
    exact (mem_union.mp h).resolve_left (fun b => n (bh b))
  refine ⟨A, ?_, by have := card_le_card subA; omega, (card_le_card cut).trans limit, card_le_card fresh⟩
  ext z
  constructor
  · intro absent
    have absentSum := mem_compl.mp absent
    have newDir : z ∈ (H+H)ᶜ := by
      apply mem_compl.mpr
      intro old
      rw [←intact] at old
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.mp old
      exact absentSum (mem_add.mpr ⟨u,subA hu,v,subA hv,rfl⟩)
    obtain ⟨x,hx,h⟩ := cover z newDir
    by_contra no
    have partner : x+z ∈ B := by
      apply mem_sdiff.mpr
      refine ⟨h, ?_⟩
      intro mem
      obtain ⟨y,hy,w,hw,eq⟩ := mem_add.mp mem
      exact no ((unique x hx z newDir y hy w (outside hw) eq.symm).symm ▸ hw)
    exact absentSum (mem_add.mpr ⟨x,mem_union_right _ hx,x+z,subA partner,back x z⟩)
  · intro hz
    apply mem_compl.mpr
    intro hzA
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.mp hzA
    rcases mem_union.mp hu with hu | hu <;> rcases mem_union.mp hv with hv | hv
    · exact (mem_compl.mp (outside hz)) (mem_add.mpr ⟨u,bh hu,v,bh hv,rfl⟩)
    · exact forbidden hu hv (add_comm u v ▸ hz)
    · exact forbidden hv hu hz
    · exact (mem_compl.mp (outside hz)) (within (mem_add.mpr ⟨u,hu,v,hv,rfl⟩))

end Green51MissingMasks
#print axioms Green51MissingMasks.prescribe

namespace Green51MissingMasks
open Finset Green53ParityThreshold Green51Hyperplane
open scoped Classical Pointwise

/-- Delete at most one kernel point per forbidden direction, then add a point in the opposite coset.
This is the one-point construction of Alon and Zamir, *Sumsets in the Hypercube*, Theorem 7. -/
theorem realize_affine {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
    (D : Finset G) (f : G →ₗ[F] F) (t : G) (one : f t = 1)
    (level : ∀ x ∈ D, f x = 1) (thin : 4*D.card < Fintype.card G) :
    ∃ A : Finset G, (A+A)ᶜ = D ∧ Fintype.card G ≤ 2*(A.card+D.card) := by
  classical
  let K := (LinearMap.ker f : Set G).toFinset
  have mk (x : G) : x ∈ K ↔ f x = 0 := by simp [K]
  have bits (a : F) : a = 0 ∨ a = 1 := by fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
  have off {x : G} (hx : x ∉ K) : f x = 1 := (bits _).resolve_left (fun h => hx ((mk x).mpr h))
  have inside {x : G} (hx : x ∉ K) : t+x ∈ K := by
    apply (mk _).mpr
    rw [map_add,one,off hx,ZModModule.add_self]
  have mirror : K.map (Equiv.addLeft t).toEmbedding = Kᶜ := by
    ext x
    constructor
    · rintro hx
      obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
      apply mem_compl.mpr
      intro bad
      have h := (mk _).mp bad
      change f (t+y) = 0 at h
      rw [map_add,one,(mk _).mp hy,add_zero] at h
      exact one_ne_zero h
    · intro hx
      exact mem_map.mpr ⟨t+x,inside (mem_compl.mp hx),by change t+(t+x)=x; rw [←add_assoc,ZModModule.add_self,zero_add]⟩
  have half : K.card + K.card = Fintype.card G := by
    have h := card_compl_add_card K
    rwa [←mirror,card_map] at h
  have full : K+K=K := by
    ext x
    constructor
    · rintro hx
      obtain ⟨y,hy,z,hz,rfl⟩ := mem_add.mp hx
      exact (mk _).mpr (by rw [map_add,(mk _).mp hy,(mk _).mp hz,add_zero])
    · intro hx
      exact mem_add.mpr ⟨0,(mk _).mpr (map_zero _),x,hx,zero_add _⟩
  have forbidden : D ⊆ (K+K)ᶜ := by
    rw [full]
    exact fun x hx => mem_compl.mpr fun bad => one_ne_zero ((level x hx).symm.trans ((mk _).mp bad))
  have cheap (B : Finset G) (sub : B ⊆ K) (loss : (K \ B).card ≤ ({t} : Finset G).card * D.card) :
      B+B=K+K := by
    apply Finset.Subset.antisymm (Finset.add_subset_add sub sub)
    intro z hz
    rw [full] at hz
    by_contra absent
    have cost := Green51DeletionRadius.direction_cost (A := K) (B := B) z absent
    have mates : Green51DeletionRadius.mates K z = K := by
      unfold Green51DeletionRadius.mates
      exact filter_eq_self.mpr fun x hx => (mk _).mpr (by rw [map_add,(mk _).mp hx,(mk _).mp hz,add_zero])
    rw [mates] at cost
    simp only [card_singleton,one_mul] at loss
    omega
  obtain ⟨A,eq,sz,_,_⟩ := prescribe K {t} D forbidden cheap
    (by rw [Finset.singleton_add_singleton,ZModModule.add_self,full]; exact singleton_subset_iff.mpr ((mk _).mpr (map_zero _)))
    (by intro z hz; rw [full] at hz; exact ⟨t,mem_singleton_self _,inside (mem_compl.mp hz)⟩)
    (by intro x hx z _ y hy w _ eq; obtain rfl := mem_singleton.mp hx; obtain rfl := mem_singleton.mp hy; exact add_left_cancel eq)
  simp only [card_singleton,one_mul] at sz
  exact ⟨A,eq,by omega⟩

end Green51MissingMasks
#print axioms Green51MissingMasks.realize_affine
