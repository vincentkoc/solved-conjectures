import Erdos722QuadrupleTripling

/-!
# Gluing a quadruple system over a two-point stem

Each point other than the distinguished base point is replaced by a column.
The two new stem points lie over that distinguished point. A triple in at
least three distinct projected points selects its base block, and a triple
inside one column together with the stem uses their common subdesign.
-/

namespace Erdos722.StemInflation
open Finset

abbrev Lift (I C : Type*) := Fin 2 ⊕ (I × C)

variable {I C : Type*} [DecidableEq I]

def proj : Lift I C → Option I
  | .inl _ => none
  | .inr (i,_) => some i

def column (i : I) : Fin 2 ⊕ C ↪ Lift I C :=
  (Function.Embedding.refl (Fin 2)).sumMap ⟨fun c => (i,c), fun _ _ he => congrArg Prod.snd he⟩

def expand {J : Type*} (j : J ↪ I) : Lift J C ↪ Lift I C :=
  (Function.Embedding.refl (Fin 2)).sumMap (j.prodMap (Function.Embedding.refl C))

private def key (T : Finset (Lift I C)) : Finset (Option I) :=
  let P := T.image proj
  if P.card = 3 then P else insert none P

private theorem image_sub_key (T : Finset (Lift I C)) : T.image proj ⊆ key T := by
  simp only [key]
  split <;> simp_all

private theorem key_card {T : Finset (Lift I C)} (ht : T.card = 3) : (key T).card ≤ 3 := by
  have h := card_image_le (s := T) (f := proj)
  simp only [key]
  split
  · omega
  · have := card_insert_le none (T.image proj)
    omega

private theorem key_small {T : Finset (Lift I C)} (ht : T.card = 3) (hs : (key T).card < 3) :
    ∃ i, key T = {none,some i} := by
  classical
  have hn : none ∈ key T := by
    by_cases h : (T.image proj).card = 3
    · simp [key,h] at hs
    · simp [key,h]
  obtain ⟨i,c,hic⟩ : ∃ i c, Sum.inr (i,c) ∈ T := by
    by_contra! h
    have hsub : T ⊆ (univ : Finset (Fin 2)).image Sum.inl := by
      rintro (p | ⟨i,c⟩) hx
      · exact mem_image.mpr ⟨p,mem_univ _,rfl⟩
      · exact (h i c hx).elim
    have hl := (card_le_card hsub).trans card_image_le
    simp [ht] at hl
  have hi : some i ∈ key T := image_sub_key T (mem_image_of_mem proj hic)
  refine ⟨i,Eq.symm ?_⟩
  apply eq_of_subset_of_card_le (insert_subset hn (singleton_subset_iff.mpr hi))
  simpa using (show (key T).card ≤ 2 by omega)

private theorem column_range {T : Finset (Lift I C)} {i : I} (he : key T = {none,some i})
    {x : Lift I C} (hx : x ∈ T) : ∃ y, column i y = x := by
  have hp := he ▸ image_sub_key T (mem_image_of_mem proj hx)
  cases x with
  | inl p => exact ⟨.inl p,rfl⟩
  | inr z =>
    obtain ⟨j,c⟩ := z
    have hj : j=i := by simpa [proj] using hp
    subst j
    exact ⟨.inr c,rfl⟩

private theorem mapped_complete {X : Type*} [DecidableEq X] {Y : Type*} [Fintype Y] [DecidableEq Y]
    {G : Finset (Finset Y)} (hG : G.IsBlockDesign 3 4) (e : Y ↪ X)
    {T : Finset X} (ht : T.card = 3) (he : ∀ x ∈ T, ∃ y, e y = x) :
    ∃! C, C ∈ G.image (Finset.map e) ∧ T ⊆ C := by
  classical
  have htu : T ⊆ univ.image e := by
    intro x hx
    obtain ⟨y,hy⟩ := he x hx
    exact mem_image.mpr ⟨y,mem_univ _,hy⟩
  obtain ⟨U,_,hU⟩ := subset_image_iff.mp htu
  have heq : U.map e = T := (map_eq_image _ _).trans hU
  have h3 : U.card = 3 := by rw [← heq, card_map] at ht; exact ht
  obtain ⟨D,⟨hD,huD⟩,un⟩ := hG.2 U h3
  refine ⟨D.map e, ⟨mem_image_of_mem _ hD, heq ▸ map_subset_map.mpr huD⟩, ?_⟩
  rintro C ⟨hm,hTC⟩
  obtain ⟨E,hE,rfl⟩ := mem_image.mp hm
  rw [← heq] at hTC
  rw [un _ ⟨hE,map_subset_map.mp hTC⟩]

theorem relabel {A D : Type*} [Fintype A] [DecidableEq D]
    {G : Finset (Finset A)} (hG : G.IsBlockDesign 3 4) (e : A ≃ D) :
    (G.image (Finset.map e.toEmbedding)).IsBlockDesign 3 4 := by
  classical
  refine ⟨?_, fun T ht ↦ mapped_complete hG e.toEmbedding ht (fun x _ ↦ e.surjective x)⟩
  intro C hc
  obtain ⟨U,hu,rfl⟩ := mem_image.mp hc
  simpa using hG.1 U hu


variable {K : Type*} [Fintype I] [Fintype K] [DecidableEq K] [AddCommGroup K]

private def color : Lift I K → K
  | .inl _ => 0
  | .inr z => z.2

private def transversal (B : Finset (Option I)) : Finset (Finset (Lift I K)) :=
  univ.filter fun C ↦ C.card = 4 ∧ C.image proj = B ∧ ∑ x ∈ C, color x = 0

private theorem mem_transversal {B : Finset (Option I)} {C : Finset (Lift I K)} :
    C ∈ transversal B ↔ C.card = 4 ∧ C.image proj = B ∧ ∑ x ∈ C, color x = 0 := by
  simp [transversal]

private theorem transversal_key {B : Finset (Option I)} (hb : B.card = 4)
    {C : Finset (Lift I K)} (hc : C ∈ transversal B) {T : Finset (Lift I K)}
    (htc : T ⊆ C) (ht : T.card = 3) : key T ⊆ B := by
  obtain ⟨hc4,hi,_⟩ := mem_transversal.mp hc
  have hinj : Set.InjOn proj (C : Set (Lift I K)) := injOn_of_card_image_eq (hi ▸ hb.trans hc4.symm)
  have hd := (card_image_of_injOn (hinj.mono htc)).trans ht
  simpa [key, hd, hi] using (image_subset_image (f := proj) htc)

private theorem transversal_complete {B : Finset (Option I)} (hn : none ∉ B) (hb : B.card = 4)
    {T : Finset (Lift I K)} (ht : T.card = 3) (hs : key T ⊆ B) :
    ∃! C, C ∈ transversal B ∧ T ⊆ C := by
  classical
  let P := T.image proj
  have hP : P.card = 3 := by
    by_contra h
    exact hn (hs (by simp [key, P] at h ⊢; simp [h]))
  have hPB := (image_sub_key T).trans hs
  obtain ⟨u,hu,he⟩ := exists_eq_insert_iff.mpr
    (show P ⊆ B ∧ P.card + 1 = B.card by exact ⟨hPB, by omega⟩)
  cases u with
  | none => exact (hn (he ▸ mem_insert_self _ _)).elim
  | some i =>
    let a : K := -(∑ x ∈ T, color x)
    let w : Lift I K := .inr (i, a)
    have hwπ : proj w = some i := rfl
    have hw : w ∉ T := fun h ↦ hu (hwπ ▸ mem_image_of_mem proj h)
    have good : insert w T ∈ transversal B := by
      refine mem_transversal.mpr ⟨by rw [card_insert_of_notMem hw, ht], ?_, ?_⟩
      · rw [image_insert, hwπ]; exact he
      · rw [sum_insert hw]; exact neg_add_cancel _
    refine ⟨insert w T, ⟨good, subset_insert _ _⟩, ?_⟩
    rintro C ⟨hc,hTC⟩
    obtain ⟨hc4,hproj,hzero⟩ := mem_transversal.mp hc
    obtain ⟨v,hv,rfl⟩ := exists_eq_insert_iff.mpr ⟨hTC, by rw [ht,hc4]⟩
    have hvp : proj v = some i := by
      rw [image_insert, ← he] at hproj
      have hm : some i ∈ insert (proj v) P := hproj ▸ mem_insert_self _ _
      exact ((mem_insert.mp hm).resolve_right hu).symm
    have hvc : color v = a := by
      rw [sum_insert hv] at hzero
      exact eq_neg_of_add_eq_zero_left hzero
    have hvw : v = w := by
      cases v with
      | inl u => contradiction
      | inr z => exact congrArg Sum.inr (Prod.ext (Option.some.inj hvp) hvc)
    rw [hvw]



omit [DecidableEq I] [Fintype I] [Fintype K] [DecidableEq K] [AddCommGroup K] in
private theorem expand_range (j : Fin 3 ↪ I) {B : Finset (Option I)} (hb : none ∈ B)
    (hj : ∀ i, some i ∈ B ↔ ∃ a, j a = i) (x : Lift I K) :
    proj x ∈ B ↔ ∃ y, expand j y = x := by
  cases x with
  | inl h => exact ⟨fun _ => ⟨.inl h,rfl⟩,fun _ => hb⟩
  | inr v =>
    obtain ⟨i,c⟩ := v
    constructor
    · intro hi
      obtain ⟨a,ha⟩ := (hj i).mp hi
      exact ⟨.inr (a,c),by subst i; rfl⟩
    · rintro ⟨h | ⟨a,d⟩,he⟩
      · contradiction
      · exact (hj i).mpr ⟨a, congrArg Prod.fst (Sum.inr.inj he)⟩

private def Good (F : Finset (Finset (Fin 2 ⊕ K))) (B : Finset (Option I))
    (P : Finset (Finset (Lift I K))) : Prop :=
  (∀ D ∈ P, D.card = 4) ∧
  (∀ D ∈ P, ∀ T ⊆ D, T.card = 3 → key T ⊆ B) ∧
  (∀ T, T.card = 3 → key T ⊆ B → ∃! D, D ∈ P ∧ T ⊆ D) ∧
  (none ∈ B → ∀ i, some i ∈ B → ∀ D ∈ F, D.map (column i) ∈ P)

private theorem piece_exists {F : Finset (Finset (Fin 2 ⊕ K))}
    {G : Finset (Finset (Lift (Fin 3) K))} (hG : G.IsBlockDesign 3 4)
    (hcol : ∀ a : Fin 3, ∀ D ∈ F, D.map (column a) ∈ G)
    (B : Finset (Option I)) (h4 : B.card = 4) : ∃ P, Good F B P := by
  classical
  by_cases hn : none ∈ B
  · have hcard : Fintype.card (Fin 3) = Fintype.card B.eraseNone := by
      rw [Fintype.card_fin,Fintype.card_coe,card_eraseNone_of_mem hn,h4]
    let e : Fin 3 ≃ B.eraseNone := Fintype.equivOfCardEq hcard
    let j := e.toEmbedding.trans (Function.Embedding.subtype _)
    have hj (i : I) : some i ∈ B ↔ ∃ a, j a = i := by
      constructor
      · intro h
        let b : B.eraseNone := ⟨i,mem_eraseNone.mpr h⟩
        exact ⟨e.symm b,congrArg Subtype.val (e.apply_symm_apply b)⟩
      · rintro ⟨a,rfl⟩
        exact mem_eraseNone.mp (e a).property
    let f := expand (C := K) j
    refine ⟨G.image (Finset.map f), ?_, ?_, ?_, ?_⟩
    · intro D hd
      obtain ⟨U,hu,rfl⟩ := mem_image.mp hd
      simpa using hG.1 U hu
    · intro D hd T hTD _
      obtain ⟨U,_,rfl⟩ := mem_image.mp hd
      have hproj : T.image proj ⊆ B := by
        intro v hv
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
        obtain ⟨y,_,hy⟩ := mem_map.mp (hTD hx)
        exact (expand_range j hn hj x).mpr ⟨y,hy⟩
      simp only [key]
      split
      · exact hproj
      · exact insert_subset hn hproj
    · intro T ht hTB
      apply mapped_complete hG f ht
      intro x hx
      exact (expand_range j hn hj x).mp (hTB (image_sub_key T (mem_image_of_mem proj hx)))
    · intro _ i hi D hD
      obtain ⟨a,rfl⟩ := (hj i).mp hi
      refine mem_image.mpr ⟨D.map (column a),hcol a D hD,?_⟩
      rw [map_map]
      congr 1
      ext (p | c) <;> rfl
  · exact ⟨transversal B,fun _ h => (mem_transversal.mp h).1,
      fun _ hc _ hTC ht => transversal_key h4 hc hTC ht,
      fun _ ht hs => transversal_complete hn h4 ht hs,fun h => (hn h).elim⟩

/-- Three mutually compatible column subdesigns on a local template produce
a global quadruple system with two common stem points. -/
theorem exists_pointed {F : Finset (Finset (Fin 2 ⊕ K))} (hF : F.IsBlockDesign 3 4)
    {G : Finset (Finset (Lift (Fin 3) K))} (hG : G.IsBlockDesign 3 4)
    (hcol : ∀ a : Fin 3, ∀ D ∈ F, D.map (column a) ∈ G)
    {H : Finset (Finset (Option I))} (hH : H.IsBlockDesign 3 4)
    (hn : 3 ≤ Fintype.card (Option I)) : ∃ P : Finset (Finset (Lift I K)), P.IsBlockDesign 3 4 := by
  classical
  let P (B : Finset (Option I)) : Finset (Finset (Lift I K)) :=
    if h : B.card = 4 then (piece_exists hG hcol B h).choose else ∅
  have hP (B) (hB : B ∈ H) : Good F B (P B) := by
    have h := hH.1 B hB
    simpa only [P,dif_pos h] using (piece_exists hG hcol B h).choose_spec
  have shared (T : Finset (Lift I K)) (ht : T.card = 3) (hs : (key T).card < 3) :
      ∃ D, T ⊆ D ∧ ∀ B ∈ H, key T ⊆ B → D ∈ P B := by
    obtain ⟨i,hi⟩ := key_small ht hs
    obtain ⟨D,⟨hD,hTD⟩,_⟩ := mapped_complete hF (column i) ht (fun x hx => column_range hi hx)
    obtain ⟨U,hU,rfl⟩ := mem_image.mp hD
    refine ⟨_,hTD,fun B hB hTB => ?_⟩
    rw [hi] at hTB
    exact (hP B hB).2.2.2 (hTB (by simp)) i (hTB (by simp)) U hU
  let small (T : Finset (Lift I K)) : Finset (Lift I K) :=
    if h : T.card = 3 ∧ (key T).card < 3 then (shared T h.1 h.2).choose else ∅
  refine ⟨_,Tripling.glue hH hn P key small (fun _ ht => key_card ht)
    (fun B hB => (hP B hB).1) (fun B hB => (hP B hB).2.1)
    (fun B hB => (hP B hB).2.2.1) ?_⟩
  intro B hB T ht hs hTB
  simp only [small,dif_pos (And.intro ht hs)]
  exact ⟨(shared T ht hs).choose_spec.2 B hB hTB,(shared T ht hs).choose_spec.1⟩

#print axioms exists_pointed

end Erdos722.StemInflation
