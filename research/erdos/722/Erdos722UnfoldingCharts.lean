import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Unfolding an indexed pair design

A zero-sum vector is determined by all but one coordinate. Two affine
charts with slopes agreeing in just one coordinate can thus be matched
at two prescribed values once their offsets agree in that coordinate.
-/

namespace Erdos722.PairUnfolding
open Finset
variable {D K : Type*} [Fintype D] [DecidableEq D] [Field K]

def Plane (D K : Type*) [Fintype D] [AddCommMonoid K] := {f : D → K // ∑ e, f e = 0}

private theorem plane_extend (e : D) (f : D → K) :
    ∃! y : Plane D K, ∀ j, j≠e → y.val j=f j := by
  classical
  let z := Function.update f e (-(∑ j∈univ.erase e, f j))
  have hz (j : D) (hj : j≠e) : z j=f j := Function.update_of_ne hj ..
  have hs : (∑ j∈univ.erase e, z j) = ∑ j∈univ.erase e, f j :=
    sum_congr rfl fun j hj => hz j (mem_erase.mp hj).1
  have hsum : ∑ j, z j=0 := by
    rw [← sum_erase_add _ _ (mem_univ e),hs]
    simp [z]
  refine ⟨⟨z,hsum⟩,hz,?_⟩
  intro w hw
  apply Subtype.ext
  funext j
  by_cases hje : j=e
  · subst j
    have hw' : (∑ t∈univ.erase e, w.val t)=∑ t∈univ.erase e, f t :=
      sum_congr rfl fun t ht => hw t (mem_erase.mp ht).1
    have h := w.property
    rw [← sum_erase_add _ _ (mem_univ e),hw'] at h
    change w.val e=z e
    simp only [z,Function.update_self]
    exact eq_neg_of_add_eq_zero_right h
  · exact (hw j hje).trans (hz j hje).symm

def chart (s t : D → K) (z : Plane D K × (D → K)) : D → K :=
  fun e => z.2 e+s e*z.1.val e+t e

/-- The missing slope difference leaves one scalar compatibility equation.
The zero-sum condition then supplies the missing parameter. -/
theorem charts_through (e : D) (s₁ s₂ t₁ t₂ X Y : D → K) (he : s₁ e=s₂ e)
    (hne : ∀ j, j≠e → s₁ j≠s₂ j) (hdelta : Y e-X e=t₂ e-t₁ e) :
    ∃! z : Plane D K × (D → K), chart s₁ t₁ z=X ∧ chart s₂ t₂ z=Y := by
  let v (j : D) := ((Y j-X j)-(t₂ j-t₁ j))/(s₂ j-s₁ j)
  obtain ⟨y,hy,hu⟩ := plane_extend e v
  let u (j : D) := X j-s₁ j*y.val j-t₁ j
  have h₁ : chart s₁ t₁ (y,u)=X := by funext j; dsimp [chart,u]; ring
  have delta (j : D) : (s₂ j-s₁ j)*y.val j=(Y j-X j)-(t₂ j-t₁ j) := by
    by_cases hje : j=e
    · subst j; rw [he,hdelta]; ring
    · rw [hy j hje]; dsimp [v]; field_simp [sub_ne_zero.mpr (Ne.symm (hne j hje))]
  refine ⟨(y,u),⟨h₁,?_⟩,?_⟩
  · funext j
    dsimp [chart,u]
    linear_combination delta j
  · rintro ⟨w,a⟩ ⟨hw,ha⟩
    have hw₁ (j) := congrFun hw j
    have hw₂ (j) := congrFun ha j
    change ∀ j, a j+s₁ j*w.val j+t₁ j=X j at hw₁
    change ∀ j, a j+s₂ j*w.val j+t₂ j=Y j at hw₂
    have hwy : w=y := hu w (by
      intro j hj
      apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm (hne j hj)))).mpr
      linear_combination hw₂ j - hw₁ j)
    subst w
    congr 1
    funext j
    dsimp [u]
    linear_combination hw₁ j

#print axioms charts_through

abbrev Coord (v : ℕ) := {e : Fin v × Fin v // e.1 < e.2}


/-- The coordinates are the unordered pairs of original points. -/
theorem coord_card (v : ℕ) : Fintype.card (Coord v)=v.choose 2 := by
  classical
  let pairs := (univ : Finset (Fin v)).powersetCard 2
  let send (e : Coord v) : pairs :=
    ⟨{e.val.1,e.val.2},mem_powersetCard.mpr ⟨subset_univ _,by simp [e.property.ne]⟩⟩
  have hf : Function.Bijective send := by
    constructor
    · intro e f h
      have h' : ({e.val.1,e.val.2} : Set (Fin v))={f.val.1,f.val.2} := by
        simpa [send] using congrArg (fun t : pairs => (t.val : Set (Fin v))) h
      rcases Set.pair_eq_pair_iff.mp h' with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
      · exact Subtype.ext (Prod.ext h₁ h₂)
      · have he := e.property
        have hf := f.property
        order
    · intro e
      obtain ⟨i,j,hij,he⟩ := card_eq_two.mp (mem_powersetCard.mp e.property).2
      rcases lt_or_gt_of_ne hij with h|h
      · exact ⟨⟨(i,j),h⟩,Subtype.ext he.symm⟩
      · exact ⟨⟨(j,i),h⟩,Subtype.ext ((pair_comm j i).trans he.symm)⟩
  exact (Fintype.card_congr (Equiv.ofBijective send hf)).trans (by simp [pairs])

def slope {v : ℕ} (f : Fin v → K) (i : Fin v) (e : Coord v) :=
  if i=e.val.1 ∨ i=e.val.2 then 0 else f i

def offset {v : ℕ} {β : Type*} (serial : Coord v → β → K) (b : β) (i : Fin v) (e : Coord v) :=
  if i=e.val.2 then serial e b else 0

private theorem slopes_ne {v : ℕ} (f : Fin v → K) (hf : Function.Injective f)
    (hn : ∀ i, f i≠0) {i j : Fin v} (hij : i<j) {e : Coord v} (he : e≠⟨(i,j),hij⟩) :
    slope f i e≠slope f j e := by
  by_cases hi : i=e.val.1 ∨ i=e.val.2
  · by_cases hj : j=e.val.1 ∨ j=e.val.2
    · exfalso
      apply he
      have h := e.property
      apply Subtype.ext
      apply Prod.ext <;> rcases hi with hi|hi <;> rcases hj with hj|hj <;> order
    · simpa [slope,hi,hj] using (hn j).symm
  · by_cases hj : j=e.val.1 ∨ j=e.val.2
    · simpa [slope,hi,hj] using hn i
    · simpa [slope,hi,hj] using fun h => hij.ne (hf h)

abbrev Params (v : ℕ) (K : Type*) [Field K] := Plane (Coord v) K × (Coord v → K)

/-- The index of a repeated block selects its unique copy. The two chart
conditions then determine the unique translation of that copy. -/
theorem repeat_through {v : ℕ} {β : Type*} (f : Fin v → K) (hf : Function.Injective f)
    (hn : ∀ i, f i≠0) (base : β → Finset (Fin v)) (serial : Coord v → β → K)
    (hs : ∀ e d, ∃! b, e.val.1∈base b ∧ e.val.2∈base b ∧ serial e b=d)
    {i j : Fin v} (hij : i<j) (X Y : Coord v → K) :
    ∃! z : β × Params v K, i∈base z.1 ∧ j∈base z.1 ∧
      chart (slope f i) (offset serial z.1 i) z.2=X ∧
      chart (slope f j) (offset serial z.1 j) z.2=Y := by
  let e : Coord v := ⟨(i,j),hij⟩
  obtain ⟨b,⟨hi,hj,hb⟩,hu⟩ := hs e (Y e-X e)
  have he : slope f i e=slope f j e := by simp [e,slope]
  have hd : Y e-X e=offset serial b j e-offset serial b i e := by
    simpa [offset,e,hij.ne] using hb.symm
  obtain ⟨z,hz,hz'⟩ := charts_through e (slope f i) (slope f j) (offset serial b i)
    (offset serial b j) X Y he (fun _ h => slopes_ne f hf hn hij h) hd
  refine ⟨(b,z),⟨hi,hj,hz⟩,?_⟩
  rintro ⟨b',z'⟩ ⟨hi',hj',hX,hY⟩
  have hX' := congrFun hX e
  have hY' := congrFun hY e
  change chart (slope f i) (offset serial b' i) z' e=X e at hX'
  change chart (slope f j) (offset serial b' j) z' e=Y e at hY'
  have htag : serial e b'=Y e-X e := by
    simp [chart,slope,offset,e,hij.ne] at hX' hY'
    dsimp only [e]
    linear_combination hY'-hX'
  have eqb : b'=b := hu b' ⟨hi',hj',htag⟩
  subst b'
  exact congrArg (Prod.mk b) (hz' z' ⟨hX,hY⟩)

#print axioms coord_card
#print axioms repeat_through
end Erdos722.PairUnfolding
