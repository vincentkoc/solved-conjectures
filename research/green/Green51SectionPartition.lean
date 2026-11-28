import Green51FrameSections

/-! # Partition of near-extremal nonaffine direction sets -/

namespace Green51GirthFrame
open Finset Green53ParityThreshold
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

noncomputable def circuitFrames (G : Type*) [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
    (g : ℕ) : Finset (Finset G) :=
  univ.filter fun U => ∃ C, ShortestOddCircuit U C ∧ C.card=g ∧ ∃ P : Submodule F G,
    IsCompl P (Submodule.span F (C : Set G)) ∧ U=(P : Set G).toFinset+C

noncomputable def nonaffineSubsets (U : Finset G) (k : ℕ) : Finset (Finset G) :=
  (U.powersetCard k).filter (fun D => ¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x=1)

private theorem frame_data {U : Finset G} {g : ℕ} (h : U ∈ circuitFrames G g) :
    U.card = g*2^(Module.finrank F G+1-g) ∧
    ∀ R ⊆ U, Odd R.card → (∑ x ∈ R, x) = 0 → g ≤ R.card := by
  obtain ⟨C,m,len,P,comp,eq⟩ := (mem_filter.mp h).2
  exact ⟨by simpa only [←eq,len] using (container_size_girth m P comp).2,
    fun R sub par zero => len ▸ m.2.2.2 R sub par zero⟩

/-- In the near-extremal band, the nonaffine missing sets have disjoint greatest frames. -/
theorem frame_partition (g k : ℕ) (large : 5 ≤ g) (odd : Odd g)
    (near : min (5*g+12) (4*g+20)*2^(Module.finrank F G+1-g) < 8*k) :
    let family := ((univ : Finset G).powersetCard k).filter (fun D =>
      (¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x=1) ∧
      ∀ R ⊆ D, Odd R.card → (∑ x ∈ R, x) = 0 → g ≤ R.card)
    family = (circuitFrames G g).biUnion (fun U => nonaffineSubsets U k) ∧
    ((circuitFrames G g : Finset (Finset G)) : Set (Finset G)).PairwiseDisjoint
      (fun U => nonaffineSubsets U k) := by
  classical
  have unique (D : Finset G) (sz : D.card=k) (no : ¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x=1)
      (short : ∀ R ⊆ D, Odd R.card → (∑ x ∈ R, x) = 0 → g ≤ R.card) :
      ∃ U ∈ circuitFrames G g, D ⊆ U ∧ ∀ W ∈ circuitFrames G g, D ⊆ W → W = U := by
    obtain ⟨C,m,len,P,comp,gr,num⟩ := greatest_girth_extension D g large odd short no (by simpa only [sz] using near)
    have mU := (container_size_girth m P comp).1
    refine ⟨_,mem_filter.mpr ⟨mem_univ _,C,mU,len,P,comp,rfl⟩,gr.1.1,?_⟩
    intro W hW sub
    obtain ⟨cnt,small⟩ := frame_data hW
    exact Finset.eq_of_subset_of_card_le (gr.2 ⟨sub,small⟩) (num.trans cnt.symm).le
  constructor
  · ext D
    constructor
    · intro h
      obtain ⟨bound,no,short⟩ := mem_filter.mp h
      have sz := (mem_powersetCard.mp bound).2
      obtain ⟨U,hU,sub,_⟩ := unique D sz no short
      exact mem_biUnion.mpr ⟨U,hU,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sub,sz⟩,no⟩⟩
    · intro h
      obtain ⟨U,hU,subs⟩ := mem_biUnion.mp h
      obtain ⟨bound,no⟩ := mem_filter.mp subs
      obtain ⟨sub,sz⟩ := mem_powersetCard.mp bound
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨Finset.subset_univ _,sz⟩,no,
        fun R hR par zero => (frame_data hU).2 R (hR.trans sub) par zero⟩
  · intro U hU W hW distinct
    apply Finset.disjoint_left.mpr
    intro D hDU hDW
    obtain ⟨bound,no⟩ := mem_filter.mp hDU
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp bound
    have short := fun R (hR : R ⊆ D) => (frame_data hU).2 R (hR.trans sub)
    obtain ⟨V,_,_,eq⟩ := unique D sz no short
    exact distinct ((eq U hU sub).trans (eq W hW (mem_powersetCard.mp (mem_filter.mp hDW).1).1).symm)

end Green51GirthFrame
#print axioms Green51GirthFrame.frame_partition

namespace Green51GirthFrame
open Finset Green53ParityThreshold
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

theorem count_global_sections (g k : ℕ) (large : 5 ≤ g) (odd : Odd g)
    (near : min (5*g+12) (4*g+20)*2^(Module.finrank F G+1-g) < 8*k) :
    ((((univ : Finset G).powersetCard k).filter (fun D =>
      (¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x=1) ∧
      ∀ R ⊆ D, Odd R.card → (∑ x ∈ R, x) = 0 → g ≤ R.card)).card : ℤ) =
      (circuitFrames G g).card * ∑ j ∈ range (g+1), ((g.choose j : ℕ) : ℤ) *
        ((-1 : ℤ)^j * (((g-j)*2^(Module.finrank F G+1-g)).choose k : ℕ)) := by
  classical
  let l := 2^(Module.finrank F G+1-g)
  let w := ∑ j ∈ range (g+1), ((g.choose j : ℕ) : ℤ) * ((-1 : ℤ)^j * (((g-j)*l).choose k : ℕ))
  have majority : g*l < 2*k := by
    have a := Nat.mul_le_mul_right l (show 4*g ≤ min (5*g+12) (4*g+20) by omega)
    change min (5*g+12) (4*g+20)*l < 8*k at near
    rw [Nat.mul_assoc] at a
    omega
  have uniform (U : Finset G) (hu : U ∈ circuitFrames G g) : ((nonaffineSubsets U k).card : ℤ)=w := by
    obtain ⟨C,m,len,P,comp,eq⟩ := (mem_filter.mp hu).2
    have num := (container_size_girth m P comp).2
    have rk := circuit_rank m
    have rr := Submodule.finrank_add_eq_of_isCompl comp
    have lev : Module.finrank F P = Module.finrank F G+1-g := by omega
    have order : (P : Set G).toFinset.card = l := by
      rw [Set.toFinset_card]
      change Fintype.card P = l
      rw [Module.card_eq_pow_finrank (K := F),lev]
      rfl
    have dense : ((P : Set G).toFinset+C).card < 2*k := by rw [num,len]; exact majority
    have result := count_nonaffine_in_frame m P comp k dense
    rw [len,order] at result
    unfold nonaffineSubsets
    rw [eq]
    exact result
  obtain ⟨collect,dis⟩ := frame_partition (G := G) g k large odd near
  rw [collect,card_biUnion dis,Nat.cast_sum]
  change _ = _ * w
  rw [sum_congr rfl uniform,sum_const,nsmul_eq_mul]
end Green51GirthFrame
#print axioms Green51GirthFrame.count_global_sections
