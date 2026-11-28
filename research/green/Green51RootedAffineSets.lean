import Green51GreatestExtension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Rooted binary subsets and level-one affine hyperplanes -/
namespace Green51AffineEnumeration
open Finset Green53ParityThreshold
open scoped Classical
variable {G : Type*} [AddCommGroup G] [Module F G]

def translates (a : G) : G ≃ G where
  toFun x := x+a
  invFun x := x+a
  left_inv x := by change x+a+a=x; rw [add_assoc,ZModModule.add_self,add_zero]
  right_inv x := by change x+a+a=x; rw [add_assoc,ZModModule.add_self,add_zero]

def shifted (D : Finset G) (a : G) := D.map (translates a).toEmbedding

@[simp] theorem mem_shifted (x a : G) (D : Finset G) : x ∈ shifted D a ↔ x+a ∈ D := by
  exact mem_map_equiv

@[simp] theorem shifted_twice (D : Finset G) (a : G) : shifted (shifted D a) a=D := by
  ext x; simp [add_assoc,ZModModule.add_self]

def separated (D : Finset G) : Prop := ∃ f : G →ₗ[F] F, ∀ y ∈ D, f y=1

/-- A rooted set translates into a level-one hyperplane exactly off its span. -/
theorem separated_shifted_iff (D : Finset G) (zero : 0 ∈ D) (a : G) :
    separated (shifted D a) ↔ a ∉ Submodule.span F (D : Set G) := by
  classical
  let W := Submodule.span F (D : Set G)
  constructor
  · rintro ⟨f,ones⟩ ha
    have atA : f a=1 := ones _ ((mem_shifted _ _ _).mpr ((ZModModule.add_self a) ▸ zero))
    have ker : W ≤ f.ker := Submodule.span_le.mpr fun x hx => by
      have e := ones (x+a) ((mem_shifted _ _ _).mpr (by rwa [add_assoc,ZModModule.add_self,add_zero]))
      rw [map_add,atA] at e
      exact LinearMap.mem_ker.mpr (add_right_cancel (b := (1:F)) (by simpa only [zero_add] using e))
    exact one_ne_zero (atA.symm.trans (LinearMap.mem_ker.mp (ker ha)))
  · intro ha
    have ne : W.mkQ a ≠ 0 := fun eq => ha ((Submodule.Quotient.mk_eq_zero W).mp eq)
    obtain ⟨f,one⟩ := Module.Projective.exists_dual_eq_one F ne
    refine ⟨f.comp W.mkQ,fun x hx => ?_⟩
    have inside : x+a ∈ W := Submodule.subset_span ((mem_shifted _ _ _).mp hx)
    have eq : W.mkQ x + W.mkQ a = 0 := by rw [←map_add,Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero W).mpr inside
    have same : W.mkQ x = W.mkQ a := by
      calc
        _ = W.mkQ x + W.mkQ a + W.mkQ a := by rw [add_assoc,ZModModule.add_self,add_zero]
        _ = _ := by rw [eq,zero_add]
    change f (W.mkQ x) = 1
    rw [same,one]
end Green51AffineEnumeration
#print axioms Green51AffineEnumeration.separated_shifted_iff

namespace Green51AffineEnumeration
open Finset Green53ParityThreshold
open scoped Classical
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]

/-- Mark one element and translate it to zero, retaining the translate as a free parameter. -/
theorem root_count (k : ℕ) (pred : Finset G → Prop) [DecidablePred pred] :
    let K := (univ : Finset G).powersetCard k
    k*(K.filter pred).card =
      ∑ E ∈ K.filter (fun E => 0 ∈ E), (univ.filter (fun a => pred (shifted E a))).card := by
  classical
  let K := (univ : Finset G).powersetCard k
  let A (a : G) := K.filter fun D => a ∈ D ∧ pred D
  let B (a : G) := K.filter fun E => 0 ∈ E ∧ pred (shifted E a)
  have keep (D : Finset G) (a : G) : shifted D a ∈ K ↔ D ∈ K := by simp [K,shifted]
  have swap (a : G) : (A a).card=(B a).card := by
    apply card_bij (fun D _ => shifted D a)
    · intro D h
      obtain ⟨sz,mem,val⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨(keep _ _).mpr sz,by simpa using mem,by simpa using val⟩
    · intro D _ E _ he
      simpa using congrArg (fun J => shifted J a) he
    · intro E h
      obtain ⟨sz,mem,val⟩ := mem_filter.mp h
      exact ⟨shifted E a,mem_filter.mpr ⟨(keep _ _).mpr sz,
        (mem_shifted _ _ _).mpr (by rwa [ZModModule.add_self]),val⟩,shifted_twice E a⟩
  have inner (D : Finset G) : (∑ a : G, if a ∈ D ∧ pred D then 1 else 0) =
      (if pred D then D.card else 0) := by
    by_cases h : pred D <;> simp [h]
  calc
    _ = ∑ D ∈ K.filter pred, D.card := by
      rw [sum_congr rfl (g := fun _ => k) fun D h => (mem_powersetCard.mp (mem_filter.mp h).1).2]
      simp [mul_comm]
    _ = ∑ D ∈ K, ∑ a : G, if a ∈ D ∧ pred D then 1 else 0 := by
      rw [sum_filter]; apply sum_congr rfl; intro D _; exact (inner D).symm
    _ = ∑ a : G, (A a).card := by
      rw [sum_comm]; apply sum_congr rfl; intro a _; simp [A]
    _ = ∑ a : G, (B a).card := sum_congr rfl fun a _ => swap a
    _ = ∑ E ∈ K, ∑ a : G, if 0 ∈ E ∧ pred (shifted E a) then 1 else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro a _; simp [B]
    _ = _ := by
      rw [sum_filter]; apply sum_congr rfl; intro E _; by_cases h : 0 ∈ E <;> simp [h]
end Green51AffineEnumeration
#print axioms Green51AffineEnumeration.root_count

namespace Green51AffineEnumeration
open Finset Green53ParityThreshold
open scoped Classical
variable (G : Type*) [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

noncomputable def affineCount (k : ℕ) : ℕ :=
  (((univ : Finset G).powersetCard k).filter separated).card

noncomputable def rootedSets (k : ℕ) : Finset (Finset G) :=
  ((univ : Finset G).powersetCard k).filter (fun E => 0 ∈ E)

omit [DecidableEq G] in
private theorem killed (E : Finset G) (hz : 0 ∈ E) :
    univ.filter (fun a => ¬separated (shifted E a)) = ((Submodule.span F (E : Set G)) : Set G).toFinset := by
  classical
  ext a; simp [separated_shifted_iff E hz]

/-- The counts on both sides of the affine criterion are sums over sets rooted at zero. -/
theorem affine_rooted_sums (k : ℕ) :
    k*affineCount G k =
      ∑ E ∈ rootedSets G k, (Fintype.card G - ((Submodule.span F (E : Set G)) : Set G).toFinset.card) ∧
    k*((Fintype.card G).choose k-affineCount G k) =
      ∑ E ∈ rootedSets G k, ((Submodule.span F (E : Set G)) : Set G).toFinset.card := by
  classical
  let K := (univ : Finset G).powersetCard k
  constructor
  · refine (root_count k (separated (G := G))).trans ?_
    apply sum_congr rfl
    intro E hE
    have hz := (mem_filter.mp hE).2
    have eq : univ.filter (fun a => separated (shifted E a)) = (((Submodule.span F (E : Set G)) : Set G).toFinset)ᶜ := by
      ext a; simp [separated_shifted_iff E hz]
    rw [eq,card_compl]
  · have total : (K.filter separated).card+(K.filter (fun D => ¬separated D)).card=(Fintype.card G).choose k := by
      rw [card_filter_add_card_filter_not,card_powersetCard,card_univ]
    have small : (Fintype.card G).choose k-affineCount G k = (K.filter (fun D => ¬separated D)).card := by
      change _ - (K.filter separated).card = _
      omega
    rw [small]
    refine (root_count k (fun D : Finset G => ¬separated D)).trans ?_
    apply sum_congr rfl; intro E hE; rw [killed G E (mem_filter.mp hE).2]
end Green51AffineEnumeration
#print axioms Green51AffineEnumeration.affine_rooted_sums

namespace Green51AffineEnumeration
open Finset Green53ParityThreshold
open scoped Classical
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
  [Fintype (Module.Dual F G)]

/-- Weighting the nonzero annihilators of a rooted set by its span counts the off-span points. -/
theorem annihilator_weight (E : Finset G) :
    let W := Submodule.span F (E : Set G)
    (univ.filter (fun f : Module.Dual F G => f ≠ 0 ∧ ∀ x ∈ E, f x=0)).card *
      (W : Set G).toFinset.card = Fintype.card G-(W : Set G).toFinset.card := by
  classical
  let W := Submodule.span F (E : Set G)
  let T := (W.dualAnnihilator : Set (Module.Dual F G)).toFinset
  let S := (W : Set G).toFinset
  have zero : (0 : Module.Dual F G) ∈ T := Set.mem_toFinset.mpr W.dualAnnihilator.zero_mem
  have eq : univ.filter (fun f : Module.Dual F G => f ≠ 0 ∧ ∀ x ∈ E, f x=0) = T.erase 0 := by
    ext f
    simp only [mem_filter,mem_univ,true_and,mem_erase]
    apply and_congr_right
    intro _
    rw [show (f ∈ T) ↔ f ∈ W.dualAnnihilator from Set.mem_toFinset, Submodule.mem_dualAnnihilator]
    exact (Submodule.span_le (p := f.ker)).symm
  have product : T.card*S.card = Fintype.card G := by
    change (W.dualAnnihilator : Set (Module.Dual F G)).toFinset.card * (W : Set G).toFinset.card = _
    rw [Set.toFinset_card,Set.toFinset_card]
    change Fintype.card W.dualAnnihilator * Fintype.card W = Fintype.card G
    rw [Module.card_eq_pow_finrank (K := F) (V := W.dualAnnihilator),Module.card_eq_pow_finrank (K := F) (V := W),
      Module.card_eq_pow_finrank (K := F) (V := G),←pow_add,add_comm (Module.finrank F W.dualAnnihilator),Subspace.finrank_add_finrank_dualAnnihilator_eq]
  dsimp only
  rw [eq]
  change (T.erase 0).card * S.card = Fintype.card G-S.card
  have split : (T.erase 0).card+1=T.card := card_erase_add_one zero
  rw [←split,add_mul,one_mul] at product
  omega
end Green51AffineEnumeration
#print axioms Green51AffineEnumeration.annihilator_weight

namespace Green51AffineEnumeration
open Finset Green53ParityThreshold
open scoped Classical
variable {H G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
  [AddCommGroup H] [Module F H] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
private theorem span_image_card (j : H →ₗ[F] G) (inj : Function.Injective j) (E : Finset H) :
    ((Submodule.span F ((E.image j : Finset G) : Set G)) : Set G).toFinset.card =
      ((Submodule.span F (E : Set H)) : Set H).toFinset.card := by
  classical
  rw [coe_image,←LinearMap.map_span]
  let W := Submodule.span F (E : Set H)
  have img : ((W.map j) : Set G).toFinset = (W : Set H).toFinset.image j := by
    ext x
    simp only [Set.mem_toFinset, SetLike.mem_coe, mem_image,Submodule.mem_map]
  exact img ▸ card_image_of_injective _ inj

/-- Rooted subsets inside a linear image have the span-cardinality sum of the source. -/
theorem rooted_image_sum (j : H →ₗ[F] G) (inj : Function.Injective j) (k : ℕ) :
    (∑ E ∈ (rootedSets G k).filter (fun E => ∀ x ∈ E, x ∈ j.range),
      ((Submodule.span F (E : Set G)) : Set G).toFinset.card) =
    ∑ D ∈ rootedSets H k, ((Submodule.span F (D : Set H)) : Set H).toFinset.card := by
  classical
  symm
  apply sum_bij (fun D _ => D.image j)
  · intro D hD
    obtain ⟨num,hz⟩ := mem_filter.mp hD
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,?_⟩,?_⟩,?_⟩
    · rw [card_image_of_injective _ inj]; exact (mem_powersetCard.mp num).2
    · exact mem_image.mpr ⟨0,hz,map_zero _⟩
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      exact ⟨y,rfl⟩
  · intro D _ E _ eq
    ext x
    have atX := Finset.ext_iff.mp eq (j x)
    simpa [mem_image,inj.eq_iff] using atX
  · intro E hE
    obtain ⟨root,inside⟩ := mem_filter.mp hE
    obtain ⟨num,hz⟩ := mem_filter.mp root
    let D := (univ : Finset H).filter (fun h => j h ∈ E)
    have same : D.image j=E := by
      ext x; constructor
      · rintro hx
        obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
        exact (mem_filter.mp hv).2
      · intro hx
        obtain ⟨v,rfl⟩ := inside x hx
        exact mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,hx⟩,rfl⟩
    refine ⟨D,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,?_⟩,?_⟩,same⟩
    · rw [←card_image_of_injective D inj,same]; exact (mem_powersetCard.mp num).2
    · exact mem_filter.mpr ⟨mem_univ _,by simpa using hz⟩
  · intro D _; exact (span_image_card j inj D).symm
end Green51AffineEnumeration
#print axioms Green51AffineEnumeration.rooted_image_sum

#print axioms Green51AffineEnumeration.mem_shifted
#print axioms Green51AffineEnumeration.shifted_twice
