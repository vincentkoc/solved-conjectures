import Erdos722IntrinsicLatinAffinity
import Erdos722SparseCoordinateDetection
import Erdos722SignedSteinerObstruction

/-! # Leaving a nonlinear transversal through each nonroot point -/

namespace Erdos722.AffineStar
open Finset QuadCompletion FourPoint QuadSwitch LatinFillings
open scoped Classical
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The flag count on an arbitrary finite point type, transported to the pinned predicate. -/
theorem sqs_flags {H : Finset (Finset I)} (h : H.IsBlockDesign 3 4) (A : Finset I) (size : A.card≤3) :
    (4-A.card).choose (3-A.card)*(H.filter (A⊆·)).card=(Fintype.card I-A.card).choose (3-A.card) := by
  let e := Fintype.equivFin I
  let G := H.image (Finset.map e.toEmbedding)
  have same : G.filter (A.map e.toEmbedding ⊆ ·)=(H.filter (A⊆·)).image (Finset.map e.toEmbedding) := by
    ext B
    constructor
    · intro hb
      obtain ⟨hb,inside⟩ := mem_filter.mp hb
      obtain ⟨C,hC,rfl⟩ := mem_image.mp hb
      exact mem_image.mpr ⟨C,mem_filter.mpr ⟨hC,map_subset_map.mp inside⟩,rfl⟩
    · intro hb
      obtain ⟨C,hC,rfl⟩ := mem_image.mp hb
      obtain ⟨hC,inside⟩ := mem_filter.mp hC
      exact mem_filter.mpr ⟨mem_image_of_mem _ hC,map_subset_map.mpr inside⟩
  have count := IntegralDesign.flag_count (PointedProduct.relabel_design e h) (A.map e.toEmbedding)
    (by simpa using size)
  change _*(G.filter _).card=_ at count
  simpa only [same,card_image_of_injective _ (Finset.map_injective e.toEmbedding),card_map] using count

def pencil (Q : Rule I) (o : I) := Q.blocks.filter (o∈·)

theorem pencil_card (Q : Rule I) (o : I) :
    3*(pencil Q o).card=(Fintype.card I-1).choose 2 := by
  simpa [pencil] using sqs_flags Q.isBlockDesign {o} (by simp)

theorem joint_pencil (Q : Rule I) {i o : I} (ne : i≠o) :
    2*(Q.blocks.filter ({i,o}⊆·)).card=Fintype.card I-2 := by
  have size : ({i,o}:Finset I).card=2 := card_pair ne
  simpa only [size,Nat.reduceSub,Nat.choose_one_right] using sqs_flags Q.isBlockDesign {i,o} (by omega)

/-- The blocks through i outside the root pencil outnumber any 2n forbidden blocks when n≥64. -/
theorem marker_exists (Q : Rule I) {o i : I} (ne : i≠o) (large : 64≤Fintype.card I)
    (K : Finset (Finset I)) (small : K.card≤2*Fintype.card I) :
    ∃ B∈Q.blocks, i∈B ∧ o∉B ∧ B∉K := by
  by_contra! bad
  have sub : pencil Q i ⊆ Q.blocks.filter ({i,o}⊆·) ∪ K := by
    intro B hb
    obtain ⟨block,inside⟩ := mem_filter.mp hb
    by_cases root : o∈B
    · exact mem_union_left _ (mem_filter.mpr ⟨block,insert_subset inside (singleton_subset_iff.mpr root)⟩)
    · exact mem_union_right _ (bad B block inside root)
  have le := (card_le_card sub).trans (card_union_le ..)
  have joint := joint_pencil Q ne
  have star := pencil_card Q i
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le large
  have twice := Nat.choose_succ_right_eq (Fintype.card I-1) 1
  simp only [Nat.reduceAdd,Nat.choose_one_right,← star] at twice
  rw [hm] at joint small twice
  rw [show 64+m-1=63+m by omega,show 63+m-1=62+m by omega] at twice
  rw [show 64+m-2=62+m by omega] at joint
  nlinarith

attribute [local instance] cubeOrder cubeDec

/-- At most 2n whole weighted-block equations distinguish all 4^n fibre translations. -/
theorem sparse_gradient (d : ℕ) (hd : 6≤d) :
    ∃ K : Finset (Finset (Base d)), K⊆(cubeRule (d+2)).blocks ∧ K.card≤2*2^(d+2) ∧
      ∀ t : Base d → Fibre, (∀ B : (cubeRule (d+2)).blocks, B.val∈K →
        weightedGradient (cubeRule (d+2)) (colours d hd) t B=0) → t=0 := by
  let Q := cubeRule (d+2)
  let D := weightedGradient Q (colours d hd)
  let ev (B : Q.blocks) : (Base d → Fibre) →+ Fibre :=
    { toFun := fun t => D t B
      map_zero' := congrFun (map_zero D) B
      map_add' := fun a b => congrFun (map_add D a b) B }
  obtain ⟨S,small,det⟩ := SparseDetection.detecting_coordinates ev (by
    intro t eq
    apply cycle_gradient_injective (d+2) (by omega)
    rw [map_zero]
    exact funext eq)
  have sz : Nat.card (Base d → Fibre)=2^(2*2^(d+2)) := by
    rw [pow_mul]
    simp [Base,Fibre,Cube,Nat.card_eq_fintype_card]
  rw [sz] at small
  refine ⟨S.image Subtype.val,?_,?_,fun t tests => det t (fun B h => tests B (mem_image_of_mem _ h))⟩
  · intro B hb
    obtain ⟨b,_,rfl⟩ := mem_image.mp hb
    exact b.prop
  · rw [card_image_of_injective _ Subtype.val_injective]
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp small

#print axioms sqs_flags
#print axioms pencil
#print axioms pencil_card
#print axioms joint_pencil
#print axioms marker_exists
#print axioms sparse_gradient
end
end Erdos722.AffineStar
