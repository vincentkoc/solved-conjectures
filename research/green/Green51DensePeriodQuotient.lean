import Green51DenseTranslationCount

/-! # Dense sumsets pulled back along a binary linear quotient -/

namespace Green51PeriodQuotients
open Finset Green53ParityThreshold
open scoped Classical Pointwise
variable {G H : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
  [AddCommGroup H] [Module F H] [Fintype H] [DecidableEq H]

def pull (f : G →ₗ[F] H) (B : Finset H) : Finset G := univ.filter fun x => f x∈B

omit [DecidableEq G] [Fintype H] in
@[simp] theorem mem_pull (f : G →ₗ[F] H) (B : Finset H) (x : G) :
    x∈pull f B ↔ f x∈B := by simp [pull]

omit [DecidableEq G] [Fintype H] in
theorem image_pull (f : G →ₗ[F] H) (onto : Function.Surjective f) (B : Finset H) :
    (pull f B).image f=B := by
  classical
  ext y
  constructor
  · rintro hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact (mem_pull _ _ _).mp hx
  · intro hy
    obtain ⟨x,rfl⟩ := onto y
    exact mem_image.mpr ⟨_,(mem_pull _ _ _).mpr hy,rfl⟩

omit [DecidableEq G] in
theorem card_pull (f : G →ₗ[F] H) (onto : Function.Surjective f) (B : Finset H) :
    (pull f B).card=(f.ker : Set G).toFinset.card*B.card := by
  classical
  obtain ⟨j,hj⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr onto)
  have sec (y) : f (j y)=y := LinearMap.congr_fun hj y
  rw [←Finset.card_product]
  symm
  apply card_bij (fun z _ => z.1+j z.2)
  · intro z hz
    obtain ⟨hx,hy⟩ := mem_product.mp hz
    simpa only [mem_pull,map_add,LinearMap.mem_ker.mp (Set.mem_toFinset.mp hx),sec,zero_add] using hy
  · intro a ha b hb eq
    have aa := mem_product.mp ha
    have bb := mem_product.mp hb
    have second := congrArg f eq
    rw [map_add,map_add,LinearMap.mem_ker.mp (Set.mem_toFinset.mp aa.1),LinearMap.mem_ker.mp (Set.mem_toFinset.mp bb.1),sec,sec,zero_add,zero_add] at second
    exact Prod.ext (add_right_cancel (show a.1+j b.2=b.1+j b.2 by simpa only [second] using eq)) second
  · intro y hy
    refine ⟨(y-j (f y),f y),mem_product.mpr ⟨Set.mem_toFinset.mpr (LinearMap.mem_ker.mpr ?_),(mem_pull _ _ _).mp hy⟩,sub_add_cancel _ _⟩
    rw [map_sub,sec,sub_self]

theorem pull_compl (f : G →ₗ[F] H) (S : Finset H) : (pull f S)ᶜ=pull f Sᶜ := by
  ext x
  simp only [mem_compl,mem_pull]

omit [Fintype H] in
theorem pull_double (f : G →ₗ[F] H) (onto : Function.Surjective f) (A : Finset H) :
    pull f (A+A)=pull f A+pull f A := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨a,ha,b,hb,eq⟩ := mem_add.mp ((mem_pull _ _ _).mp hx)
    obtain ⟨y,rfl⟩ := onto a
    refine mem_add.mpr ⟨y,(mem_pull _ _ _).mpr ha,x-y,(mem_pull _ _ _).mpr ?_,by abel⟩
    rwa [map_sub,←eq,add_sub_cancel_left]
  · intro hx
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
    exact (mem_pull _ _ _).mpr (by rw [map_add]; exact add_mem_add ((mem_pull _ _ _).mp ha) ((mem_pull _ _ _).mp hb))

theorem dens_pull (f : G →ₗ[F] H) (onto : Function.Surjective f) (A : Finset H) :
    (pull f A).dens=A.dens := by
  classical
  have hu : pull f univ=univ := by ext x; simp
  have full := card_pull f onto univ
  rw [hu,card_univ,card_univ] at full
  have p : 0 < (f.ker : Set G).toFinset.card := card_pos.mpr ⟨0,Set.mem_toFinset.mpr f.ker.zero_mem⟩
  unfold Finset.dens
  rw [card_pull f onto,full]
  push_cast
  field_simp

/-- The maximum attainable input density is preserved when the output is a complete inverse image. -/
theorem dense_double_pull_iff (f : G →ₗ[F] H) (onto : Function.Surjective f) (S : Finset H) (α : ℝ) :
    (∃ A : Finset G, A+A=pull f S ∧ α < (A.dens : ℝ)) ↔
      ∃ B : Finset H, B+B=S ∧ α < (B.dens : ℝ) := by
  classical
  constructor
  · rintro ⟨A,eq,high⟩
    have sub : A ⊆ pull f (A.image f) := fun x hx => (mem_pull _ _ _).mpr (mem_image_of_mem _ hx)
    have sz := Finset.dens_mono sub
    rw [dens_pull f onto] at sz
    refine ⟨A.image f,?_,high.trans_le (by exact_mod_cast sz)⟩
    rw [←image_pull f onto S,←eq]
    ext y
    constructor
    · intro h
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp h
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hb
      exact mem_image.mpr ⟨x+z,add_mem_add hx hz,map_add _ _ _⟩
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_image.mp h
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
      rw [map_add]
      exact add_mem_add (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
  · rintro ⟨B,rfl,h⟩
    exact ⟨pull f B,(pull_double f onto B).symm,by rwa [dens_pull f onto]⟩

end Green51PeriodQuotients
#print axioms Green51PeriodQuotients.mem_pull
#print axioms Green51PeriodQuotients.image_pull
#print axioms Green51PeriodQuotients.card_pull
#print axioms Green51PeriodQuotients.pull_compl
#print axioms Green51PeriodQuotients.pull_double
#print axioms Green51PeriodQuotients.dens_pull
#print axioms Green51PeriodQuotients.dense_double_pull_iff
