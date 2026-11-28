import Erdos722HarmonicQuadruples
import Erdos722BinaryQuadruples

/-!
# Tripling a Steiner quadruple system

Hanani's construction replaces each point except a distinguished point by three
copies. The local systems overlap on whole four-point columns.
-/

namespace Erdos722.Tripling

open Finset Polynomial

variable {V X : Type*} [DecidableEq X] [Fintype V]

/-- Glue local quadruple systems indexed by the blocks of a base design.
A triple whose support has size three determines the base block. A smaller
support must have the same prescribed completion in every incident piece. -/
theorem glue {H : Finset (Finset V)} (hH : H.IsBlockDesign 3 4) (hn : 3 ≤ Fintype.card V)
    (pieces : Finset V → Finset (Finset X)) (support : Finset X → Finset V)
    (small : Finset X → Finset X)
    (hcard : ∀ T : Finset X, T.card = 3 → (support T).card ≤ 3)
    (hunif : ∀ B ∈ H, ∀ C ∈ pieces B, C.card = 4)
    (hsub : ∀ B ∈ H, ∀ C ∈ pieces B, ∀ T ⊆ C, T.card = 3 → support T ⊆ B)
    (hlocal : ∀ B ∈ H, ∀ T : Finset X, T.card = 3 → support T ⊆ B →
      ∃! C, C ∈ pieces B ∧ T ⊆ C)
    (hsmall : ∀ B ∈ H, ∀ T : Finset X, T.card = 3 → (support T).card < 3 →
      support T ⊆ B → small T ∈ pieces B ∧ T ⊆ small T) :
    (H.biUnion pieces).IsBlockDesign 3 4 := by
  classical
  refine ⟨?_, ?_⟩
  · intro C hC
    obtain ⟨B,hB,hBC⟩ := mem_biUnion.mp hC
    exact hunif B hB C hBC
  intro T hT
  have hs := hcard T hT
  obtain ⟨U,hTU,_,hU⟩ := exists_subsuperset_card_eq (subset_univ (support T)) hs (by simpa using hn)
  obtain ⟨B,⟨hB,hUB⟩,_⟩ := hH.2 U hU
  have hTB := hTU.trans hUB
  obtain ⟨C,hC,uC⟩ := hlocal B hB T hT hTB
  refine ⟨C, ⟨mem_biUnion.mpr ⟨B,hB,hC.1⟩,hC.2⟩, ?_⟩
  rintro D ⟨hD,hTD⟩
  obtain ⟨A,hA,hAD⟩ := mem_biUnion.mp hD
  have hTA := hsub A hA D hAD T hTD hT
  rcases lt_or_eq_of_le hs with hlt | heq
  · have hsmallA := hsmall A hA T hT hlt hTA
    have hsmallB := hsmall B hB T hT hlt hTB
    exact ((hlocal A hA T hT hTA).unique ⟨hAD,hTD⟩ hsmallA).trans (uC _ hsmallB)
  · have he : A = B := (hH.2 (support T) heq).unique ⟨hA,hTA⟩ ⟨hB,hTB⟩
    exact uC _ ⟨he ▸ hAD,hTD⟩


private abbrev Color := ZMod 3
private abbrev Lift (I : Type*) := Option (I × Color)

private def column {I : Type*} [DecidableEq I] (i : I) : Finset (Lift I) :=
  {none, some (i, 0), some (i, 1), some (i, 2)}

private theorem coeff_three {K : Type*} [Field K] (a b c : K) :
    ((Polynomial.C a + Polynomial.X) * (Polynomial.C b + Polynomial.X) *
      (Polynomial.C c + Polynomial.X)).coeff 2 = a + b + c := by
  open Polynomial in
    rw [show (C a + X) * (C b + X) * (C c + X) = C (a*b*c) +
      C (a*b + a*c + b*c) * X ^ 1 + C (a+b+c) * X ^ 2 + X ^ 3 by
        simp only [map_add, map_mul, pow_one]; ring]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C]
    norm_num

/-- The ten-point harmonic design can be labelled by three columns of three
points, with each column and infinity forming a block. -/
theorem ten_point_template :
    ∃ H : Finset (Finset (Option (ZMod 3 × ZMod 3))), H.IsBlockDesign 3 4 ∧
      ∀ a : ZMod 3, {none, some (a, 0), some (a, 1), some (a, 2)} ∈ H := by
  classical
  let K := GaloisField 3 2
  let e : (Color × Color) ≃ₗ[Color] K := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_prod, Module.finrank_self, GaloisField.finrank 3 (by decide : 2 ≠ 0)])
  let label := e.toEquiv.optionCongr
  refine ⟨Harmonic.blocks label, Harmonic.blocks_isBlockDesign label, ?_⟩
  intro a
  have eqsum : (a, (0 : Color)) + (a, 1) + (a, 2) = 0 := by
    revert a
    decide
  have hsum : e (a,0) + e (a,1) + e (a,2) = 0 := by
    rw [← map_add, ← map_add, eqsum, map_zero]
  have noneFactor : Harmonic.pointFactor (none : Option K) = 1 := by
    change Polynomial.C 1 + Polynomial.C 0 * Polynomial.X = (1 : K[X])
    simp
  have someFactor (v : K) : Harmonic.pointFactor (some v) = Polynomial.C v + Polynomial.X := by
    change Polynomial.C v + Polynomial.C 1 * Polynomial.X = _
    simp
  have hone : (0 : Color) ≠ 1 := by decide
  have htwo : (0 : Color) ≠ 2 := by decide
  have hdiff : (1 : Color) ≠ 2 := by decide
  simp only [Harmonic.blocks, mem_filter, mem_univ, true_and]
  constructor
  · simp [hone, htwo, hdiff]
  · simp [label, hone, htwo, hdiff, noneFactor, someFactor, ← mul_assoc, coeff_three, hsum]


variable {I : Type*} [DecidableEq I]

private def proj : Lift I → Option I := Option.map Prod.fst

private def color : Lift I → Color
  | none => 0
  | some u => u.2

/-- Three distinct projected points determine the base block directly. A
repeated projection calls for the block through the distinguished point. -/
private def key (T : Finset (Lift I)) : Finset (Option I) :=
  let P := T.image proj
  if P.card = 3 then P else insert none P

private theorem image_sub_key (T : Finset (Lift I)) : T.image proj ⊆ key T := by
  simp only [key]
  split <;> simp_all

private theorem key_card {T : Finset (Lift I)} (ht : T.card = 3) : (key T).card ≤ 3 := by
  have h := card_image_le (s := T) (f := proj)
  simp only [key]
  split
  · omega
  · have := card_insert_le none (T.image proj)
    omega

variable [Fintype I]

private def transversal (B : Finset (Option I)) : Finset (Finset (Lift I)) :=
  univ.filter fun C ↦ C.card = 4 ∧ C.image proj = B ∧ ∑ x ∈ C, color x = 0

private theorem mem_transversal {B : Finset (Option I)} {C : Finset (Lift I)} :
    C ∈ transversal B ↔ C.card = 4 ∧ C.image proj = B ∧ ∑ x ∈ C, color x = 0 := by
  simp [transversal]

private theorem transversal_key {B : Finset (Option I)} (hb : B.card = 4)
    {C : Finset (Lift I)} (hc : C ∈ transversal B) {T : Finset (Lift I)}
    (htc : T ⊆ C) (ht : T.card = 3) : key T ⊆ B := by
  obtain ⟨hc4,hi,_⟩ := mem_transversal.mp hc
  have hinj : Set.InjOn proj (C : Set (Lift I)) := injOn_of_card_image_eq (hi ▸ hb.trans hc4.symm)
  have hd := (card_image_of_injOn (hinj.mono htc)).trans ht
  simpa [key, hd, hi] using (image_subset_image (f := proj) htc)

private theorem transversal_complete {B : Finset (Option I)} (hn : none ∉ B) (hb : B.card = 4)
    {T : Finset (Lift I)} (ht : T.card = 3) (hs : key T ⊆ B) :
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
    let a : Color := -(∑ x ∈ T, color x)
    let w : Lift I := some (i, a)
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
      | none => contradiction
      | some z => exact congrArg some (Prod.ext (Option.some.inj hvp) hvc)
    rw [hvw]


private def expand (j : Color ↪ I) : Lift Color ↪ Lift I :=
  (j.prodMap (Function.Embedding.refl Color)).optionMap

omit [DecidableEq I] [Fintype I] in
private theorem expand_range (j : Color ↪ I) {B : Finset (Option I)} (hb : none ∈ B)
    (hj : ∀ i, some i ∈ B ↔ ∃ a, j a = i) (x : Lift I) :
    proj x ∈ B ↔ ∃ y, expand j y = x := by
  cases x with
  | none => exact ⟨fun _ ↦ ⟨none,rfl⟩,fun _ ↦ hb⟩
  | some v =>
    rcases v with ⟨i,c⟩
    constructor
    · intro hi
      obtain ⟨a,ha⟩ := (hj i).mp hi
      exact ⟨some (a,c), by subst i; rfl⟩
    · rintro ⟨(_ | ⟨a,d⟩),h⟩
      · contradiction
      · exact (hj i).mpr ⟨a, congrArg Prod.fst (Option.some.inj h)⟩

private theorem mapped_complete {Y : Type*} [Fintype Y] [DecidableEq Y]
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

private def smallBlock (T : Finset (Lift I)) : Finset (Lift I) :=
  univ.filter fun x ↦ proj x ∈ key T

private theorem key_small {T : Finset (Lift I)} (ht : T.card = 3) (hs : (key T).card < 3) :
    ∃ i, key T = {none, some i} ∧ smallBlock T = column i := by
  classical
  have hn : none ∈ key T := by
    by_cases h : (T.image proj).card = 3
    · simp [key,h] at hs
    · simp [key,h]
  obtain ⟨i,c,hic⟩ : ∃ i c, some (i,c) ∈ T := by
    by_contra! h
    have hsub : T ⊆ {none} := by
      rintro (_ | ⟨i,c⟩) hx
      · simp
      · exact (h i c hx).elim
    have := card_le_card hsub
    simp [ht] at this
  have hi : some i ∈ key T := image_sub_key T (mem_image_of_mem proj hic)
  have hkey : key T = {none, some i} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le (insert_subset hn (singleton_subset_iff.mpr hi))
    simpa using (show (key T).card ≤ 2 by omega)
  refine ⟨i,hkey,?_⟩
  ext x
  cases x with
  | none => simp [smallBlock,hkey,proj,column]
  | some v =>
    obtain ⟨j,c⟩ := v
    have hc : ∀ d : Color, d = 0 ∨ d = 1 ∨ d = 2 := by decide
    rcases hc c with rfl | rfl | rfl <;> simp [smallBlock,hkey,proj,column] <;> tauto


private def Good (B : Finset (Option I)) (P : Finset (Finset (Lift I))) : Prop :=
  (∀ C ∈ P, C.card = 4) ∧
  (∀ C ∈ P, ∀ T ⊆ C, T.card = 3 → key T ⊆ B) ∧
  (∀ T, T.card = 3 → key T ⊆ B → ∃! C, C ∈ P ∧ T ⊆ C) ∧
  (∀ T, T.card = 3 → (key T).card < 3 → key T ⊆ B → smallBlock T ∈ P ∧ T ⊆ smallBlock T)

private theorem piece_exists (B : Finset (Option I)) (h4 : B.card = 4) :
    ∃ P, Good B P := by
  classical
  by_cases hn : none ∈ B
  · have hcard : Fintype.card Color = Fintype.card B.eraseNone := by
      rw [ZMod.card, Fintype.card_coe, card_eraseNone_of_mem hn,h4]
    let e : Color ≃ B.eraseNone := Fintype.equivOfCardEq hcard
    let j := e.toEmbedding.trans (Function.Embedding.subtype _)
    have hj (i : I) : some i ∈ B ↔ ∃ a, j a = i := by
      constructor
      · intro h
        let b : B.eraseNone := ⟨i,mem_eraseNone.mpr h⟩
        exact ⟨e.symm b, congrArg Subtype.val (e.apply_symm_apply b)⟩
      · rintro ⟨a,rfl⟩
        exact mem_eraseNone.mp (e a).property
    obtain ⟨G,hG,hcol⟩ := ten_point_template
    let f := expand j
    refine ⟨G.image (Finset.map f), ?_, ?_, ?_, ?_⟩
    · intro C hc
      obtain ⟨D,hD,rfl⟩ := mem_image.mp hc
      simpa using hG.1 D hD
    · intro C hc T hTC _
      obtain ⟨D,_,rfl⟩ := mem_image.mp hc
      have hproj : T.image proj ⊆ B := by
        intro v hv
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
        obtain ⟨y,_,hy⟩ := mem_map.mp (hTC hx)
        exact (expand_range j hn hj x).mpr ⟨y,hy⟩
      simp only [key]
      split
      · exact hproj
      · exact insert_subset hn hproj
    · intro T ht hTB
      apply mapped_complete hG f ht
      intro x hx
      exact (expand_range j hn hj x).mp (hTB (image_sub_key T (mem_image_of_mem proj hx)))
    · intro T ht hs hTB
      obtain ⟨i,hkey,hsmall⟩ := key_small ht hs
      obtain ⟨a,ha⟩ := (hj i).mp (hTB (by simp [hkey]))
      have hm : (column a).map f = column i := by
        subst i
        simp [column, f, expand, Function.Embedding.prodMap, Function.Embedding.optionMap]
      refine ⟨hsmall ▸ hm ▸ mem_image_of_mem _ (hcol a), ?_⟩
      intro x hx
      exact mem_filter.mpr ⟨mem_univ _,image_sub_key T (mem_image_of_mem proj hx)⟩
  · refine ⟨transversal B, fun _ h ↦ (mem_transversal.mp h).1,
      fun _ hc _ hTC ht ↦ transversal_key h4 hc hTC ht,
      fun _ ht hs ↦ transversal_complete hn h4 ht hs, ?_⟩
    intro T ht hs hTB
    obtain ⟨i,hkey,_⟩ := key_small ht hs
    exact (hn (hTB (by simp [hkey]))).elim

/-- Replace every point except infinity by three labelled copies. Ordinary
base quadruples lift by the zero-sum rule, and quadruples through infinity
lift to copies of the ten-point harmonic system. -/
theorem exists_pointed {H : Finset (Finset (Option I))} (hH : H.IsBlockDesign 3 4)
    (hn : 3 ≤ Fintype.card (Option I)) :
    ∃ G : Finset (Finset (Option (I × ZMod 3))), G.IsBlockDesign 3 4 := by
  classical
  let P (B : Finset (Option I)) : Finset (Finset (Lift I)) :=
    if h : B.card = 4 then (piece_exists B h).choose else ∅
  have hp (B) (hB : B ∈ H) : Good B (P B) := by
    have h := hH.1 B hB
    simpa only [P, dif_pos h] using (piece_exists B h).choose_spec
  exact ⟨_, glue hH hn P key smallBlock (fun _ ht ↦ key_card ht)
    (fun B hB ↦ (hp B hB).1) (fun B hB ↦ (hp B hB).2.1)
    (fun B hB ↦ (hp B hB).2.2.1) (fun B hB ↦ (hp B hB).2.2.2)⟩


private theorem relabel {A D : Type*} [Fintype A] [DecidableEq D]
    {G : Finset (Finset A)} (hG : G.IsBlockDesign 3 4) (e : A ≃ D) :
    (G.image (Finset.map e.toEmbedding)).IsBlockDesign 3 4 := by
  classical
  refine ⟨?_, fun T ht ↦ mapped_complete hG e.toEmbedding ht (fun x _ ↦ e.surjective x)⟩
  intro C hc
  obtain ⟨U,hu,rfl⟩ := mem_image.mp hc
  simpa using hG.1 U hu

/-- Hanani's tripling recurrence for the canonical finite ground sets. -/
theorem exists_tripling {n : ℕ} (hn : 3 ≤ n) {H : Finset (Finset (Fin n))}
    (hH : H.IsBlockDesign 3 4) :
    ∃ G : Finset (Finset (Fin (3 * n - 2))), G.IsBlockDesign 3 4 := by
  let I := Fin (n - 1)
  have hcard : Fintype.card (Option I) = n := by simp [I]; omega
  let e := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨G,hG⟩ := exists_pointed (relabel hH e) (by rwa [hcard])
  have hnew : Fintype.card (Option (I × ZMod 3)) = 3*n-2 := by
    simp [I, ZMod.card]
    omega
  exact ⟨_, relabel hG (Fintype.equivFinOfCardEq hnew)⟩

/-- Iterating tripling from the binary system on eight points. -/
theorem exists_seven_times_ternary (d : ℕ) :
    ∃ G : Finset (Finset (Fin (7 * 3^d + 1))), G.IsBlockDesign 3 4 := by
  induction d with
  | zero => exact Erdos722.exists_binary_quadruple_design 3
  | succ d ih =>
    obtain ⟨G,hG⟩ := ih
    have hpos := Nat.pow_pos (by decide : 0 < 3) (n := d)
    have h := exists_tripling (show 3 ≤ 7 * 3^d + 1 by omega) hG
    rwa [show 7 * 3^(d+1) + 1 = 3 * (7 * 3^d + 1) - 2 by rw [pow_succ]; omega]

private theorem old_orders_prime_to_eleven {n : ℕ}
    (h : n ∈ Submonoid.closure (Set.range (fun e : ℕ ↦ (2 : ℕ)^e) ∪
      Set.range (fun e : ℕ ↦ 3^e+1))) : ¬11 ∣ n := by
  have hp : Nat.Prime 11 := by decide
  induction h using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨e,rfl⟩ | ⟨e,rfl⟩
    · intro he
      exact (by decide : ¬11 ∣ 2) (hp.dvd_of_dvd_pow he)
    · have he : 3^e % 11 = 1 ∨ 3^e % 11 = 3 ∨ 3^e % 11 = 9 ∨ 3^e % 11 = 5 ∨ 3^e % 11 = 4 := by
        induction e with
        | zero => decide
        | succ e ih =>
          rw [pow_succ, Nat.mul_mod]
          rcases ih with h | h | h | h | h <;> rw [h] <;> decide
      change ¬11 ∣ 3^e+1
      omega
  | one => decide
  | mul x y _ _ hx hy => exact fun h ↦ (hp.dvd_mul.mp h).elim hx hy

/-- Infinitely many tripled orders lie outside the whole multiplicative
closure of the binary and ternary projective quadruple-system orders. -/
theorem cofinal_outside_product_closure (N : ℕ) :
    ∃ n > N, n ∉ Submonoid.closure (Set.range (fun e : ℕ ↦ (2 : ℕ)^e) ∪
      Set.range (fun e : ℕ ↦ 3^e+1)) ∧
      ∃ G : Finset (Finset (Fin n)), G.IsBlockDesign 3 4 := by
  let d := 5*N+1
  have hpow : 3^d % 11 = 3 := by
    dsimp [d]
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hN := Nat.lt_pow_self (n := d) (by decide : 1 < (3 : ℕ))
  have hd : N ≤ d := by dsimp [d]; omega
  refine ⟨7*3^d+1,by omega,fun h ↦ old_orders_prime_to_eleven h (by omega),exists_seven_times_ternary d⟩

#print axioms cofinal_outside_product_closure
#print axioms exists_seven_times_ternary
#print axioms exists_tripling
#print axioms exists_pointed
#print axioms glue
#print axioms ten_point_template

end Erdos722.Tripling