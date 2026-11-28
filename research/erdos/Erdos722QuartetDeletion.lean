import Erdos722QuartetCovers

/-!
# Deletion and inflation of uniform pair designs

The blocks through the deleted point partition the remaining vertices into
groups. All other blocks form a group-divisible design with one block through
every pair from different groups. The group labels can be prescribed.
-/

namespace Erdos722.Quartet
open Finset

variable {V I : Type*} {s : ℕ → Prop}

private noncomputable def residual (C : Cover (Option V) (AllPairs _) s)
    (grp : V → I) (B : I → Finset (Option V))
    (member : ∀ i, B i ∈ C.blocks) (root : ∀ i, none ∈ B i)
    (onLine : ∀ x i, grp x = i ↔ some x ∈ B i)
    (exhaust : ∀ T ∈ C.blocks, none ∈ T → ∃ i, B i = T) :
    Cover V (fun x y => grp x ≠ grp y) s where
  blocks := {A | A.map Function.Embedding.some ∈ C.blocks}
  size := by intro A hA; simpa using C.size _ hA
  sound := by
    intro A hA x hx y hy hxy he
    have ha : some x ∈ A.map Function.Embedding.some := by simpa using hx
    have hb : some y ∈ A.map Function.Embedding.some := by simpa using hy
    have hline := C.through (some x) (some y) (Option.some_injective _ |>.ne hxy) trivial
    have eq := hline.unique ⟨hA,ha,hb⟩
      ⟨member (grp y),(onLine x _).mp he,(onLine y _).mp rfl⟩
    have : none ∈ A.map Function.Embedding.some := eq ▸ root _
    simp at this
  through := by
    classical
    intro x y hxy hg
    obtain ⟨T,⟨hT,hx,hy⟩,hu⟩ := C.through (some x) (some y) (Option.some_injective _ |>.ne hxy) trivial
    have h0 : none ∉ T := by
      intro hr
      obtain ⟨i,rfl⟩ := exhaust T hT hr
      exact hg (((onLine x i).mpr hx).trans ((onLine y i).mpr hy).symm)
    have hmap : T.eraseNone.map Function.Embedding.some = T := by simp [h0]
    refine ⟨T.eraseNone,⟨(show T.eraseNone.map Function.Embedding.some ∈ C.blocks from hmap.symm ▸ hT),mem_eraseNone.mpr hx,mem_eraseNone.mpr hy⟩,?_⟩
    rintro A ⟨hA,ha,hb⟩
    have he := hu (A.map Function.Embedding.some) ⟨hA,by simpa using ha,by simpa using hb⟩
    simpa using congrArg (fun S : Finset (Option V) => S.eraseNone) he

/-- The blocks through a point of a uniform pair design give prescribed groups
of size `w` after deleting that point. -/
theorem delete_uniform_point {J : Type*} [Fintype J] {n w : ℕ} (hw : 0 < w) (hJ : Fintype.card J = n)
    (h : Has (· = w+1) (w*n+1)) :
    Nonempty (Cover (J × Fin w) (fun x y => x.1 ≠ y.1) (· = w+1)) := by
  classical
  let X := Fin (w*n)
  let C := h.realize (V := Option X) (by simp [X])
  let G := {B : Finset (Option X) // B ∈ C.blocks ∧ none ∈ B}
  have chooseLine (x : X) := C.through none (some x) (by simp) trivial
  let grp : X → G := fun x =>
    ⟨(chooseLine x).exists.choose,(chooseLine x).exists.choose_spec.1,
      (chooseLine x).exists.choose_spec.2.1⟩
  have onLine (x : X) (i : G) : grp x = i ↔ some x ∈ i.val := by
    constructor
    · rintro rfl
      exact (chooseLine x).exists.choose_spec.2.2
    · intro hx
      exact Subtype.ext ((chooseLine x).unique (chooseLine x).exists.choose_spec
        ⟨i.property.1,i.property.2,hx⟩)
  let D := residual C grp Subtype.val (fun i => i.property.1) (fun i => i.property.2) onLine
    (fun T hT h0 => ⟨⟨T,hT,h0⟩,rfl⟩)
  let fiber (i : G) : {x // grp x = i} ≃ Fin w :=
    (Equiv.subtypeEquivRight (fun x => (onLine x i).trans mem_eraseNone.symm)).trans
      (i.val.eraseNone.equivFinOfCardEq (by rw [card_eraseNone_of_mem i.property.2,C.size _ i.property.1]; omega))
  let coord : X ≃ G × Fin w := (Equiv.sigmaFiberEquiv grp).symm.trans (Equiv.sigmaEquivProdOfEquiv fiber)
  have hcard := Fintype.card_congr coord
  simp [X] at hcard
  let label : G ≃ J := Fintype.equivOfCardEq (by
    rw [hJ]
    apply Nat.eq_of_mul_eq_mul_right hw
    simpa [Nat.mul_comm] using hcard.symm)
  let e := coord.trans (Equiv.prodCongr label (Equiv.refl (Fin w)))
  have first (x : X) : (e x).1 = label (grp x) := rfl
  refine ⟨(D.map e.toEmbedding).change ?_ (fun _ => id)⟩
  intro x y _
  constructor
  · rintro ⟨a,b,rfl,rfl,hg⟩
    exact label.injective.ne hg
  · intro hxy
    refine ⟨e.symm x,e.symm y,e.apply_symm_apply _,e.apply_symm_apply _,?_⟩
    intro hg
    apply hxy
    rw [← e.apply_symm_apply x, ← e.apply_symm_apply y,first,first,hg]

/-- An arbitrary quartet design on `3n+1` points supplies a group-divisible
design on any prescribed `n` labels with three vertices per group. -/
theorem delete_point {J : Type*} [Fintype J] {n : ℕ} (hJ : Fintype.card J = n)
    (h : Has (· = 4) (3*n+1)) :
    Nonempty (Cover (J × Fin 3) (fun x y => x.1 ≠ y.1) (· = 4)) :=
  delete_uniform_point (by decide) hJ h

/-- Inflate a pairwise balanced design using uniform point-deleted ingredients. -/
theorem inflate_uniform {V : Type*} [Fintype V] {w : ℕ} (hw : 0 < w)
    (C : Cover V (AllPairs _) s) (seed : ∀ n, s n → Has (· = w+1) (w*n+1)) :
    Has (· = w+1) (w*Fintype.card V+1) := by
  classical
  let I := {B : Finset V // B ∈ C.blocks}
  let P := fun (B : I) (x y : V × Fin w) => x.1 ∈ B.val ∧ y.1 ∈ B.val ∧ x.1 ≠ y.1
  have localCover (B : I) : Nonempty (Cover (V × Fin w) (P B) (· = w+1)) := by
    let G := (delete_uniform_point hw (Fintype.card_coe B.val) (seed _ (C.size _ B.property))).some
    let e := (Function.Embedding.subtype (· ∈ B.val)).prodMap (Function.Embedding.refl (Fin w))
    refine ⟨(G.map e).change ?_ (fun _ => id)⟩
    intro x y _
    constructor
    · rintro ⟨⟨⟨x,hx⟩,u⟩,⟨⟨y,hy⟩,v⟩,rfl,rfl,hxy⟩
      exact ⟨hx,hy,fun h => hxy (Subtype.ext h)⟩
    · rintro ⟨hx,hy,hxy⟩
      exact ⟨(⟨x.1,hx⟩,x.2),(⟨y.1,hy⟩,y.2),rfl,rfl,fun he => hxy (congrArg Subtype.val he)⟩
  let between : Cover (V × Fin w) (fun x y => x.1 ≠ y.1) (· = w+1) :=
    Cover.assemble (P := P) (fun B => (localCover B).some) (fun _ _ _ _ h => h.2.2) (by
      intro x y _ hxy
      obtain ⟨B,⟨hB,hx,hy⟩,hu⟩ := C.through x.1 y.1 hxy trivial
      exact ⟨⟨B,hB⟩,⟨hx,hy,hxy⟩,fun T hT => Subtype.ext (hu _ ⟨T.property,hT.1,hT.2.1⟩)⟩)
  apply (Cover.adjoin Prod.fst between _).has (by simp [Nat.mul_comm])
  intro x
  let e : Fin w ≃ {y : V × Fin w // y.1 = x} :=
    ⟨fun j => ⟨(x,j),rfl⟩,fun y => y.val.2,fun _ => rfl,by rintro ⟨⟨_,j⟩,rfl⟩; rfl⟩
  exact (Has.single (s := (· = w+1)) rfl).realize (by simp [← Fintype.card_congr e])

#print axioms delete_uniform_point
#print axioms inflate_uniform
#print axioms delete_point

end Erdos722.Quartet
