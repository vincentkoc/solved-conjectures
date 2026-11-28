import Erdos722IntrinsicDoubleFibres
import Erdos722UnlabelledBlockFamilies

/-! # Point permutations preserving the intrinsic pairs of a quadruple double -/

namespace Erdos722.QuadSwitch
open Finset Function Equiv
noncomputable section

/-- A permutation of the base together with a separate switch in each fibre. -/
def fibrePerm {V W : Type*} (σ : V ≃ W) (f : V → Bool) : (V × Bool) ≃ (W × Bool) where
  toFun x := (σ x.1,x.2 ^^ f x.1)
  invFun y := (σ.symm y.1,y.2 ^^ f (σ.symm y.1))
  left_inv := by rintro ⟨x,b⟩; simp
  right_inv := by rintro ⟨y,b⟩; simp

theorem fibrePerm_eq_iff {V W : Type*} {σ τ : V ≃ W} {f g : V → Bool} :
    fibrePerm σ f=fibrePerm τ g ↔ σ=τ ∧ f=g := by
  constructor
  · intro he
    have point (x : V) := congrArg (fun e : V × Bool ≃ W × Bool => e (x,false)) he
    refine ⟨Equiv.ext fun x => congrArg Prod.fst (point x),funext fun x => ?_⟩
    simpa [fibrePerm] using congrArg Prod.snd (point x)
  · rintro ⟨rfl,rfl⟩
    rfl

theorem decompose_fibrePerm {V W : Type*} (e : V × Bool ≃ W × Bool)
    (fibres : ∀ x y, (e x).1=(e y).1 ↔ x.1=y.1) :
    ∃ (σ : V ≃ W) (f : V → Bool), e=fibrePerm σ f := by
  let s (x : V) := (e (x,false)).1
  have first (x : V × Bool) : (e x).1=s x.1 := (fibres x (x.1,false)).mpr rfl
  have bij : Bijective s := by
    constructor
    · exact fun x y h => (fibres (x,false) (y,false)).mp h
    · intro y
      obtain ⟨x,hx⟩ := e.surjective (y,false)
      exact ⟨x.1,(first x).symm.trans (congrArg Prod.fst hx)⟩
  let σ := Equiv.ofBijective s bij
  let f (x : V) := (e (x,false)).2
  refine ⟨σ,f,Equiv.ext ?_⟩
  rintro ⟨x,b⟩
  refine Prod.ext ?_ ?_
  · exact first _
  cases b with
  | false => simp [fibrePerm,f]
  | true =>
    have ne : (e (x,true)).2≠(e (x,false)).2 := by
      intro he
      have eq := e.injective (Prod.ext (first (x,true)) he)
      exact (by decide : true≠false) (congrArg Prod.snd eq)
    change (e (x,true)).2=(true ^^ (e (x,false)).2)
    cases h₁ : (e (x,true)).2 <;> cases h₂ : (e (x,false)).2 <;> simp_all

theorem separates_relabel {V W : Type*} (e : V ≃ W) (D : Finset (Finset V)) :
    Separates (e.finsetCongr.finsetCongr D) ↔ Separates D := by
  constructor
  · intro h x y eq
    exact e.injective (h _ _ ((sameChecks_relabel e D x y).mp eq))
  · intro h x y eq
    obtain ⟨a,rfl⟩ := e.surjective x
    obtain ⟨b,rfl⟩ := e.surjective y
    exact congrArg e (h a b ((sameChecks_relabel e D a b).mpr eq))

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {H : Finset (Finset V)}

/-- The coboundary class is recognized by the unlabelled incidence structure. -/
theorem isomorphic_coboundary (hH : H.IsBlockDesign 3 4) (sep : Separates H) {s t : H → Bool}
    (iso : Isomorphic (doubling hH s) (doubling hH t)) : Coboundary s ↔ Coboundary t := by
  obtain ⟨e,he⟩ := iso
  rw [← separating_iff hH sep s,← separating_iff hH sep t,← he]
  exact (separates_relabel ..).symm

/-- Every unrestricted isomorphism out of a non-coboundary double descends to
a permutation of the base. The base permutation and the switch in each fibre are determined by the point map. -/
theorem intrinsic_isomorphism (hH : H.IsBlockDesign 3 4) (sep : Separates H) {s t : H → Bool}
    (ng : ¬Coboundary s) (e : Perm (V × Bool)) (he : e.finsetCongr.finsetCongr (doubling hH s)=doubling hH t) :
    ∃ (σ : Perm V) (f : V → Bool), e=fibrePerm σ f := by
  have nt : ¬Coboundary t := fun h => ng ((isomorphic_coboundary hH sep ⟨e,he⟩).mpr h)
  apply decompose_fibrePerm
  intro x y
  rw [← intrinsic_fibres hH sep t nt,← he,← sameChecks_relabel, intrinsic_fibres hH sep s ng]

#print axioms fibrePerm
#print axioms fibrePerm_eq_iff
#print axioms decompose_fibrePerm
#print axioms separates_relabel
#print axioms isomorphic_coboundary
#print axioms intrinsic_isomorphism
end
end Erdos722.QuadSwitch
