import Green51AffineFrameRows

/-! # Restricting an affine equivalence to the fibres of a layered set -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical
variable {P Q V W : Type*} [AddCommGroup P] [Module F P] [AddCommGroup Q] [Module F Q]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- A linear equivalence preserving horizontal fibres induces linear equivalences on their
common direction and on the quotient. -/
theorem split_coordinates (e : (P×V) ≃ₗ[F] (Q×W))
    (horizontal : ∀ z : P×V, z.2=0 ↔ (e z).2=0) (b : Q×W) :
    ∃ u : P ≃ₗ[F] Q, ∃ v : V ≃ₗ[F] W, ∃ offset : V → Q, ∀ p i,
      e (p,i)+b=(u p+offset i,v i+b.2) := by
  let U := (LinearMap.fst F Q W).comp (e.toLinearMap.comp (LinearMap.inl F P V))
  let Vq := (LinearMap.snd F Q W).comp (e.toLinearMap.comp (LinearMap.inr F P V))
  have horiz (p : P) : e (p,0)=(U p,0) := Prod.ext rfl ((horizontal (p,0)).mp rfl)
  have expand (p : P) (i : V) : e (p,i)=(U p+(e (0,i)).1,Vq i) := by
    have add : (p,i)=(p,0)+(0,i) := by simp
    rw [add,map_add,horiz];exact Prod.ext rfl (zero_add _)
  have iu : Function.Injective U := by
    intro x y eq
    have same := (horiz x).trans ((congrArg (fun a : Q => (a,(0:W))) eq).trans (horiz y).symm)
    exact congrArg Prod.fst (e.injective same)
  have su : Function.Surjective U := by
    intro q
    obtain ⟨⟨p,i⟩,eq⟩ := e.surjective (q,0)
    have zero := (horizontal (p,i)).mpr (congrArg Prod.snd eq)
    change i=0 at zero
    subst i
    exact ⟨p,congrArg Prod.fst eq⟩
  have iv : Function.Injective Vq := by
    intro i j eq
    apply sub_eq_zero.mp
    apply (horizontal (0,i-j)).mpr
    change Vq (i-j)=0
    rw [map_sub,eq,sub_self]
  have sv : Function.Surjective Vq := by
    intro w
    obtain ⟨⟨p,i⟩,eq⟩ := e.surjective (0,w)
    rw [expand] at eq
    exact ⟨i,congrArg Prod.snd eq⟩
  refine ⟨LinearEquiv.ofBijective U ⟨iu,su⟩,LinearEquiv.ofBijective Vq ⟨iv,sv⟩,
    fun i => (e (0,i)).1+b.1,fun p i => ?_⟩
  rw [expand]
  exact Prod.ext (add_assoc ..) rfl

variable [DecidableEq P] [DecidableEq Q] [DecidableEq V] [DecidableEq W]

/-- Nonempty rows determine the quotient permutation. Each row is transformed by the same
linear identification of its fibres, followed by its own translation. -/
theorem rows_of_affine_map (C : Finset V) (B : Finset W) (row : V→Finset P) (target : W→Finset Q)
    (occupied : ∀ i∈C,(row i).Nonempty) (occupied' : ∀ j∈B,(target j).Nonempty)
    (e : (P×V) ≃ₗ[F] (Q×W)) (b : Q×W)
    (horizontal : ∀ z : P×V, z.2=0 ↔ (e z).2=0)
    (img : (layers C row).image (fun z => e z+b)=layers B target) :
    ∃ σ : ↥C ≃ ↥B, ∃ u : P ≃ₗ[F] Q, ∀ i : C, ∃ a : Q,
      (row i.val).image (fun p => u p+a)=target (σ i).val := by
  classical
  obtain ⟨u,v,off,act⟩ := split_coordinates e horizontal b
  let q := v.toEquiv.trans (Equiv.addRight b.2)
  have law (p : P) (i : V) : (i∈C ∧ p∈row i) ↔ (q i∈B ∧ u p+off i∈target (q i)) := by
    rw [←mem_layers,←mem_layers,←img]
    change _ ↔ (u p+off i,v i+b.2)∈_
    rw [←act,mem_image]
    constructor
    · intro h;exact ⟨_,h,rfl⟩
    · rintro ⟨z,hz,eq⟩;exact e.injective (add_right_cancel eq) ▸ hz
  have index (i : V) : i∈C ↔ q i∈B := by
    constructor
    · intro hi
      obtain ⟨p,hp⟩ := occupied i hi
      exact ((law p i).mp ⟨hi,hp⟩).1
    · intro hj
      obtain ⟨x,hx⟩ := occupied' (q i) hj
      exact ((law (u.symm (x-off i)) i).mpr ⟨hj,by simpa using hx⟩).1
  let σ : ↥C ≃ ↥B := q.subtypeEquiv (fun i => index i)
  refine ⟨σ,u,fun i => ⟨off i.val,?_⟩⟩
  ext x
  change x∈(row i.val).image _ ↔ x∈target (q i.val)
  constructor
  · rintro hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    exact ((law p i.val).mp ⟨i.property,hp⟩).2
  · intro hx
    let p := u.symm (x-off i.val)
    have eq : u p+off i.val=x := by simp [p]
    have hp := ((law p i.val).mpr ⟨(index _).mp i.property,eq ▸ hx⟩).2
    exact mem_image.mpr ⟨p,hp,eq⟩

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.split_coordinates
#print axioms Green51FrameIsomorphisms.rows_of_affine_map
