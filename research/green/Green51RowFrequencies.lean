import Green51FourFibreTypes
import Mathlib.Logic.Equiv.Sum

/-! # Histograms of the six occupied row types of a binary plane -/

namespace Green51FrameIsomorphisms
open Finset
open scoped Classical

/-- Number of indices with a specified value. -/
def frequency {I K : Type*} [Fintype I] [DecidableEq K] (f : I→K) (k : K) : ℕ :=
  Fintype.card {i // f i=k}

/-- Two labelled families differ by a permutation precisely when every value occurs equally often. -/
theorem match_iff_frequency {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq K]
    (f : I→K) (g : J→K) :
    (∃ e : I≃J, ∀ i, f i=g (e i)) ↔ ∀ k,frequency f k=frequency g k := by
  classical
  constructor
  · rintro ⟨e,h⟩ k
    exact Fintype.card_congr (e.subtypeEquiv (fun i => by simp only [h i]))
  · intro h
    let E (k : K) : {i // f i=k} ≃ {j // g j=k} := Fintype.equivOfCardEq (h k)
    let e := (Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight E).trans (Equiv.sigmaFiberEquiv g))
    exact ⟨e,fun i => ((E (f i) ⟨i,rfl⟩).property).symm⟩

abbrev Direction := {z : Four // z≠0}
abbrev RowKind := Fin 3 ⊕ Direction

private theorem pair_sum_ne : ∀ S : Finset Four, S.card=2 → (∑ x∈S,x)≠0 := by decide +kernel

/-- The left summand records sizes one, three and four, in order. The right records a pair's direction. -/
def kind (S : Finset Four) : RowKind :=
  if h : S.card=2 then Sum.inr ⟨∑ x∈S,x,pair_sum_ne S h⟩
  else Sum.inl (if S.card=3 then 1 else if S.card=4 then 2 else 0)

private theorem nonpair_code : ∀ S T : Finset Four, S.Nonempty → T.Nonempty →
    S.card≠2 → T.card≠2 →
    ((if S.card=3 then 1 else if S.card=4 then 2 else 0 : Fin 3)=
      (if T.card=3 then 1 else if T.card=4 then 2 else 0 : Fin 3) ↔ S.card=T.card) := by decide +kernel

def actDirection (u : Four ≃ₗ[ZMod 2] Four) : Direction ≃ Direction :=
  u.toEquiv.subtypeEquiv (fun x => by simp)

theorem lift_direction (e : Direction ≃ Direction) :
    ∃ u : Four ≃ₗ[ZMod 2] Four, actDirection u=e := by
  classical
  let f := Equiv.Perm.subtypeCongr e (Equiv.refl {x : Four // ¬x≠0})
  have fixed : f 0=0 := by simp [f, Equiv.Perm.subtypeCongr]
  refine ⟨linearize f fixed,?_⟩
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change f x.val=(e x).val
  simp [f, Equiv.Perm.subtypeCongr,x.property]

theorem kind_match (u : Four ≃ₗ[ZMod 2] Four) (S T : Finset Four) (a : S.Nonempty) (b : T.Nonempty) :
    (Equiv.sumCongr (Equiv.refl (Fin 3)) (actDirection u)) (kind S)=kind T ↔
      S.card=T.card ∧ (S.card=2 → u (∑ x∈S,x)=∑ y∈T,y) := by
  classical
  by_cases s : S.card=2 <;> by_cases t : T.card=2
  · simp [kind,s,t,actDirection,Subtype.ext_iff]
  · simp [kind,s,t,Ne.symm t]
  · simp [kind,s,t]
  · simpa [kind,s,t] using (nonpair_code S T a b s t)

theorem match_relabel_iff {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq K]
    (f : I→K) (g : J→K) (e : Equiv.Perm K) :
    (∃ σ : I≃J, ∀ i, e (f i)=g (σ i)) ↔ ∀ k,frequency f k=frequency g (e k) := by
  classical
  have changeKey (k : K) : frequency (fun j => e.symm (g j)) k=frequency g (e k) := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun j => e.symm_apply_eq)
  simp_rw [← changeKey]
  rw [← match_iff_frequency]
  exact exists_congr fun σ => forall_congr' fun i => e.eq_symm_apply.symm

/-- The three counts for row sizes one, three and four stay labelled. Among two-point
rows precisely the multiset of the three direction counts survives a change of coordinates. -/
theorem signature_iff {I J : Type*} [Fintype I] [Fintype J]
    (S : I→Finset Four) (T : J→Finset Four) (a : ∀ i,(S i).Nonempty) (b : ∀ j,(T j).Nonempty) :
    (∃ (σ : I ≃ J) (u : Four ≃ₗ[ZMod 2] Four), ∀ i,
      (S i).card=(T (σ i)).card ∧
      ((S i).card=2 → u (∑ x∈S i,x)=∑ y∈T (σ i),y)) ↔
    (∀ k : Fin 3, frequency (kind ∘ S) (.inl k)=frequency (kind ∘ T) (.inl k)) ∧
    ∀ n : ℕ, frequency (fun d : Direction => frequency (kind ∘ S) (.inr d)) n =
      frequency (fun d : Direction => frequency (kind ∘ T) (.inr d)) n := by
  classical
  let f := kind ∘ S
  let g := kind ∘ T
  let left (d : Direction) := frequency f (.inr d)
  let right (d : Direction) := frequency g (.inr d)
  constructor
  · rintro ⟨σ,u,h⟩
    let e := Equiv.sumCongr (Equiv.refl (Fin 3)) (actDirection u)
    have counts := (match_relabel_iff f g e).mp ⟨σ,fun i => (kind_match u _ _ (a _) (b _)).mpr (h i)⟩
    exact ⟨fun k => counts (.inl k),(match_iff_frequency left right).mp
      ⟨actDirection u,fun d => counts (.inr d)⟩⟩
  · rintro ⟨h,k⟩
    obtain ⟨v,hv⟩ := (match_iff_frequency left right).mpr k
    obtain ⟨u,hu⟩ := lift_direction v
    let e := Equiv.sumCongr (Equiv.refl (Fin 3)) (actDirection u)
    have equal (x : RowKind) : frequency f x=frequency g (e x) := by
      cases x with
      | inl z => exact h z
      | inr d =>
        change left d = right (actDirection u d)
        rw [hu]
        exact hv d
    obtain ⟨σ,acts⟩ := (match_relabel_iff f g e).mpr equal
    exact ⟨σ,u,fun i => (kind_match u _ _ (a _) (b _)).mp (acts i)⟩

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.match_iff_frequency
#print axioms Green51FrameIsomorphisms.kind_match

#print axioms Green51FrameIsomorphisms.signature_iff
