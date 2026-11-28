import Green51UniversalDefectNumber

/-! # Encoding stable classes using labelled rows and a binary relation space -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

theorem labelled_kernel_bound (h : ℕ) :
    universalDefectNumber h ≤ h^h * Nat.card (Submodule F (Fin h →₀ F)) := by
  classical
  let H := 𝔽₂ (h-1)
  let Q := Quotient (wordSetoid (Fin h) H h)
  let A (q : Q) : Fin h → Finset H := q.out.val
  have total (q : Q) : ∑ i,(A q i).card=h := q.out.property
  let labels (q : Q) : Fin h ≃ ((i : Fin h) × ↥(A q i)) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_sigma,total])
  let row (q : Q) (i : Fin h) := (labels q i).1
  let point (q : Q) (i : Fin h) : H := (labels q i).2.val
  let code (q : Q) : (Fin h → Fin h) × Submodule F (Fin h →₀ F) :=
    (row q,LinearMap.ker (Finsupp.linearCombination F (point q)))
  have occurrence (q : Q) (j : Fin h) (x : H) :
      x∈A q j ↔ ∃ i,row q i=j ∧ point q i=x := by
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := (labels q).surjective ⟨j,⟨x,hx⟩⟩
      exact ⟨i,congrArg Sigma.fst hi,congrArg (fun z => z.2.val) hi⟩
    · rintro ⟨i,rfl,rfl⟩
      exact (labels q i).2.property
  have inj : Function.Injective code := by
    intro p q eq
    have sameRow : row p=row q := congrArg Prod.fst eq
    obtain ⟨u,hu⟩ := (tuple_ker_iff (point p) (point q)).mp (congrArg Prod.snd eq)
    have matchRows : WordMatch (A p) (A q) := by
      refine ⟨Equiv.refl _,u,fun _ => 0,fun j => ?_⟩
      ext y
      change y ∈ (A p j).map _ ↔ y ∈ A q j
      constructor
      · intro hy
        obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
        obtain ⟨i,hi,rfl⟩ := (occurrence p j x).mp hx
        exact (occurrence q j _).mpr ⟨i,sameRow ▸ hi,by simpa using (hu i).symm⟩
      · intro hy
        obtain ⟨i,hi,rfl⟩ := (occurrence q j y).mp hy
        exact Finset.mem_map.mpr ⟨point p i,(occurrence p j _).mpr ⟨i,sameRow ▸ hi,rfl⟩,
          by simpa using hu i⟩
    have e : Quotient.mk (wordSetoid (Fin h) H h) p.out = Quotient.mk _ q.out := Quotient.sound matchRows
    simpa using e
  have bound := Nat.card_le_card_of_injective code inj
  rw [Nat.card_prod] at bound
  simpa [universalDefectNumber,Q,H,Nat.card_fun] using bound

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.labelled_kernel_bound
