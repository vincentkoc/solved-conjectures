import Green51SparseDimensions
import Mathlib.LinearAlgebra.Matrix.Rank
/-! # Quadratic relations on binary point sets -/

open Finset Green50Downsets
open scoped Classical Pointwise Matrix
namespace Green51QuadraticFlats
local notation "F" => ZMod 2
abbrev Coordinates (n : ℕ) := Option (Fin n)
def homogeneous {n:ℕ} (x : Cube n) : Coordinates n → F := fun i => i.elim 1 x
def quad {n:ℕ} (x : Cube n) : Matrix (Coordinates n) (Coordinates n) F :=
  fun i j => homogeneous x i * homogeneous x j

private theorem homogeneous_inj {n:ℕ} : Function.Injective (@homogeneous n) := by
  intro x y eq
  exact funext fun i => congrFun eq (some i)

theorem quad_inj {n:ℕ} : Function.Injective (@quad n) := by
  intro x y eq
  funext i
  have h := congrFun (congrFun eq none) (some i)
  simpa [quad,homogeneous] using h

private def columnMatrix {n:ℕ} (T : Finset (Cube n)) : Matrix (Coordinates n) T F :=
  fun i x => homogeneous x.val i

private theorem span_bound {n:ℕ} (T : Finset (Cube n)) (sum : ∑ x∈T,quad x=0) :
    2*Module.finrank F (Submodule.span F (Set.range (columnMatrix T).col))≤T.card := by
  let M := columnMatrix T
  have gram : M*Mᵀ=0 := by
    ext i j
    have h := congrFun (congrFun sum i) j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply,M,columnMatrix,Matrix.zero_apply]
    rw [Finset.sum_coe_sort T (fun x => homogeneous x i * homogeneous x j)]
    simpa only [Matrix.sum_apply,Matrix.zero_apply,quad] using h
  have r := Matrix.rank_add_rank_le_card_of_mul_eq_zero gram
  rw [Matrix.rank_transpose,Matrix.rank_eq_finrank_span_cols,Fintype.card_coe] at r
  simpa only [two_mul] using r

private abbrev hull {n:ℕ} (T : Finset (Cube n)) :=
  Submodule.span F (Set.range (columnMatrix T).col)
private def cloud {n:ℕ} (T : Finset (Cube n)) := T.image homogeneous
private theorem cloud_size {n:ℕ} (T : Finset (Cube n)) : (cloud T).card=T.card :=
  card_image_of_injective _ homogeneous_inj
private theorem cloud_in {n:ℕ} (T : Finset (Cube n)) {v} (hv:v∈cloud T) : v∈hull T := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
  exact Submodule.subset_span ⟨⟨x,hx⟩,rfl⟩
private theorem leading {n:ℕ} {T : Finset (Cube n)} {v} (hv:v∈cloud T) : v none=1 := by
  obtain ⟨x,_,rfl⟩ := mem_image.mp hv
  rfl
private def doubled {n:ℕ} (T:Finset (Cube n)) (x:Cube n) :=
  cloud T ∪ (cloud T).image (fun y => homogeneous x+y)
private theorem doubled_card {n:ℕ} (T:Finset (Cube n)) (x:Cube n) :
    (doubled T x).card=2*T.card := by
  have dis : Disjoint (cloud T) ((cloud T).image (fun y => homogeneous x+y)) := by
    apply disjoint_left.mpr
    intro v hv h
    obtain ⟨y,hy,eq⟩ := mem_image.mp h
    have e := congrFun eq none
    change 1+y none=v none at e
    rw [leading hy,leading hv] at e
    exact (by decide : ¬((1:F)+1=1)) e
  rw [doubled,card_union_of_disjoint dis,card_image_of_injective _ (fun _ _ h => add_left_cancel h),cloud_size,two_mul]

private theorem doubled_sub {n:ℕ} (T:Finset (Cube n)) {x:Cube n} (hx:x∈T) :
    doubled T x ⊆ (hull T).carrier.toFinset := by
  intro y hy
  rw [Set.mem_toFinset]
  rcases mem_union.mp hy with h|h
  · exact cloud_in _ h
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact (hull T).add_mem (cloud_in T (mem_image_of_mem homogeneous hx)) (cloud_in T ha)

private theorem hull_size {n:ℕ} (T:Finset (Cube n)) :
    (hull T).carrier.toFinset.card=2^(Module.finrank F (hull T)) := by
  rw [Set.toFinset_card]
  change Fintype.card (hull T)=_
  rw [Module.card_eq_pow_finrank (K:=F),ZMod.card]

theorem relation_size {n:ℕ} (T:Finset (Cube n)) (hne : T.Nonempty)
    (sum : ∑ x∈T,quad x=0) : 2*T.card≤2^(T.card/2) := by
  obtain ⟨x,hx⟩ := hne
  have bound := card_le_card (doubled_sub T hx)
  rw [doubled_card,hull_size] at bound
  have rank := span_bound T sum
  exact bound.trans (Nat.pow_le_pow_right (by decide) (by unfold hull; omega))

/-- Eight distinct labels with vanishing quadratic moments form an affine three-space. -/
theorem eight_closed {n:ℕ} (T : Finset (Cube n)) (size : T.card=8)
    (sum : ∑ x∈T,quad x=0) {a b c : Cube n} (ha:a∈T) (hb:b∈T) (hc:c∈T) :
    a+b+c∈T := by
  have rank := span_bound T sum
  rw [size] at rank
  have bound : Module.finrank F (hull T)≤4 := by unfold hull;omega
  have full : doubled T a=(hull T).carrier.toFinset := by
    apply eq_of_subset_of_card_le (doubled_sub T ha)
    rw [doubled_card,hull_size,size]
    exact Nat.pow_le_pow_right (by decide) bound
  let y := homogeneous a+homogeneous b+homogeneous c
  have yin : y∈(hull T).carrier := (hull T).add_mem
    ((hull T).add_mem (cloud_in T (mem_image_of_mem _ ha)) (cloud_in T (mem_image_of_mem _ hb)))
    (cloud_in T (mem_image_of_mem _ hc))
  have row : y none=1 := by change (1:F)+1+1=1;decide
  rcases mem_union.mp (show y∈doubled T a from full.symm ▸ Set.mem_toFinset.mpr yin) with hy|hy
  · obtain ⟨v,hv,eq⟩ := mem_image.mp hy
    have same : v=a+b+c := by
      funext i
      exact congrFun eq (some i)
    exact same ▸ hv
  · obtain ⟨v,hv,eq⟩ := mem_image.mp hy
    have e := congrFun eq none
    change 1+v none=y none at e
    rw [leading hv,row] at e
    exact False.elim ((by decide : ¬((1:F)+1=1)) e)

def graph (n:ℕ) : Finset (Matrix (Coordinates n) (Coordinates n) F) := univ.image quad

theorem avoids_linear (n:ℕ) :
    ¬∃ W : Submodule F (Matrix (Coordinates n) (Coordinates n) F),
      Module.finrank F W=3 ∧ ∀ w∈W,w∈graph n+graph n := by
  rintro ⟨W,dim,inside⟩
  have free (T : Finset (Matrix (Coordinates n) (Coordinates n) F)) (sub:T⊆graph n)
      (size:T.card=4 ∨ T.card=6) (zero:∑ t∈T,t=0) : False := by
    let B := univ.filter (fun x:Cube n => quad x∈T)
    have eq : B.image quad=T := by
      ext y
      constructor
      · intro h;obtain ⟨x,hx,rfl⟩ := mem_image.mp h;exact (mem_filter.mp hx).2
      · intro hy
        obtain ⟨x,_,rfl⟩ := mem_image.mp (sub hy)
        exact mem_image_of_mem quad (mem_filter.mpr ⟨mem_univ _,hy⟩)
    have card : B.card=T.card := (card_image_of_injective B quad_inj).symm.trans (congrArg Finset.card eq)
    have total : ∑ x∈B,quad x=0 := by
      rw [←eq,sum_image quad_inj.injOn] at zero;exact zero
    have pos : B.Nonempty := card_pos.mp (by omega)
    have bound := relation_size B pos total
    rcases size with h|h <;> rw [card,h] at bound <;> norm_num at bound
  have rank := Green51SparseDimensions.rank_without_relation (graph n) free W inside
  omega

end Green51QuadraticFlats

#print axioms Green51QuadraticFlats.quad_inj
#print axioms Green51QuadraticFlats.relation_size
#print axioms Green51QuadraticFlats.eight_closed
#print axioms Green51QuadraticFlats.avoids_linear
