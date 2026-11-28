import Erdos722DennistonArcs
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic

/-!
# Classical Hermitian unitals

The affine Hermitian curve has equation `trace(y) = norm(x)` over a quadratic
extension of finite fields. Its secants, including those through its point at
infinity, give the blocks of the classical unital. See J. A. Thas,
*A combinatorial characterization of Hermitian curves* (1992).
-/

namespace Erdos722.HermitianUnital
open FiniteField Finset

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- Relative Frobenius of the quadratic extension. -/
noncomputable abbrev conjugate := frobeniusAlgEquivOfAlgebraic F E

private theorem conjugate_twice (h : Module.finrank F E = 2) (x : E) :
    conjugate F E (conjugate F E x) = x := by
  have ho : orderOf (conjugate F E) = 2 := (orderOf_frobeniusAlgEquivOfAlgebraic F E).trans h
  have he := pow_orderOf_eq_one (conjugate F E)
  rw [ho, pow_two] at he
  exact congrArg (fun f : E ≃ₐ[F] E => f x) he

private theorem norm_formula (h : Module.finrank F E = 2) (x : E) :
    algebraMap F E (Algebra.norm F x) = x * conjugate F E x := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow, h, Finset.prod_range_succ, Finset.prod_range_succ]
  simp [conjugate]

private theorem trace_formula (h : Module.finrank F E = 2) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + conjugate F E x := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, h, Finset.sum_range_succ, Finset.sum_range_succ]
  simp [conjugate]

/-- Completing the Hermitian norm on an affine line gives its tangent or secant equation. -/
theorem norm_sub_conjugate (h : Module.finrank F E = 2) (x m : E) :
    Algebra.norm F (x - conjugate F E m) =
      Algebra.norm F x - Algebra.trace F E (m * x) + Algebra.norm F m := by
  apply (algebraMap F E).injective
  rw [map_add (algebraMap F E), map_sub (algebraMap F E), norm_formula F E h, norm_formula F E h,
    norm_formula F E h, trace_formula F E h, map_sub, conjugate_twice F E h, map_mul]
  ring

#print axioms norm_sub_conjugate

/-- Every trace fiber in a quadratic extension of a finite field has size `q`. -/
theorem trace_fiber_card (h : Module.finrank F E = 2) (b : F) :
    Nat.card {y : E // Algebra.trace F E y = b} = Nat.card F := by
  let t := (Algebra.trace F E).toAddMonoidHom
  have ht : Function.Surjective t := Algebra.trace_surjective F E
  have he := Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective ht b)
  change Nat.card {y : E // Algebra.trace F E y = b} = Nat.card t.ker at he
  rw [he]
  have hk := t.ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr ht,
    Nat.card_congr AddSubgroup.topEquiv.toEquiv, Module.natCard_eq_pow_finrank (K := F) (V := E),
    h, pow_two] at hk
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hk

/-- A nonzero norm fiber in the same extension has size `q+1`. -/
theorem norm_fiber_card (h : Module.finrank F E = 2) {b : F} (hb : b ≠ 0) :
    Nat.card {x : E // Algebra.norm F x = b} = Nat.card F + 1 := by
  let g := Units.map (Algebra.norm F (S := E))
  let b' := Units.mk0 b hb
  have hs : Function.Surjective g := FiniteField.unitsMap_norm_surjective F E
  let e : {x : E // Algebra.norm F x = b} ≃ {x : Eˣ // g x = b'} :=
    { toFun := fun x => ⟨Units.mk0 x.val (Algebra.norm_ne_zero_iff.mp (x.property ▸ hb)), Units.ext x.property⟩
      invFun := fun x => ⟨x.val.val, congrArg Units.val x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext (Units.ext rfl) }
  have he := Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hs b')
  change Nat.card {x : Eˣ // g x = b'} = Nat.card g.ker at he
  rw [Nat.card_congr e, he]
  have hk := g.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs,
    Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_units, Nat.card_units,
    Module.natCard_eq_pow_finrank (K := F) (V := E), h] at hk
  have hq := Finite.one_lt_card (α := F)
  apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < Nat.card F - 1)
  rw [hk]
  obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Nat.card F ≠ 0)
  rw [hv]
  simp [pow_two, Nat.add_mul, Nat.mul_add, Nat.succ_eq_add_one]

#print axioms trace_fiber_card
#print axioms norm_fiber_card

/-- Affine points on the Hermitian curve in trace–norm coordinates. -/
abbrev AffinePoint := {P : E × E // Algebra.trace F E P.2 = Algebra.norm F P.1}

/-- The projective curve consists of the affine points and one point at infinity. -/
theorem unital_point_count (h : Module.finrank F E = 2) :
    Nat.card (Option (AffinePoint F E)) = Nat.card F ^ 3 + 1 := by
  classical
  let A (x : E) := {y : E // Algebra.trace F E y = Algebra.norm F x}
  let e : AffinePoint F E ≃ (x : E) × A x :=
    { toFun := fun P => ⟨P.val.1, P.val.2, P.property⟩
      invFun := fun ⟨x, y⟩ => ⟨(x, y.val), y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hf (x : E) : Nat.card (A x) = Nat.card F := trace_fiber_card F E h _
  have hc := Nat.card_congr e
  rw [Nat.card_sigma] at hc
  simp only [hf, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul,
    Module.natCard_eq_pow_finrank (K := F) (V := E), h] at hc
  let : Fintype (AffinePoint F E) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card, hc]
  ring

#print axioms unital_point_count

/-- The affine curve equation on a nonvertical line is a translated norm fiber. -/
theorem on_slope_iff (h : Module.finrank F E = 2) (m b x : E) :
    Algebra.trace F E (m * x + b) = Algebra.norm F x ↔
      Algebra.norm F (x - conjugate F E m) = Algebra.trace F E b + Algebra.norm F m := by
  rw [map_add, norm_sub_conjugate F E h]
  constructor
  · intro he
    linear_combination -he
  · intro he
    linear_combination -he

/-- A nonvertical secant has exactly `q+1` affine points. -/
theorem slope_secant_card (h : Module.finrank F E = 2) (m b : E)
    (hs : Algebra.trace F E b + Algebra.norm F m ≠ 0) :
    Nat.card {x : E // Algebra.trace F E (m * x + b) = Algebra.norm F x} = Nat.card F + 1 := by
  let e : E ≃ E := Equiv.subRight (conjugate F E m)
  exact (Nat.card_congr (e.subtypeEquiv (fun x => on_slope_iff F E h m b x))).trans
    (norm_fiber_card F E h hs)

/-- On a tangent line the affine equation has a unique solution. -/
theorem tangent_iff (h : Module.finrank F E = 2) (m b x : E)
    (ht : Algebra.trace F E b + Algebra.norm F m = 0) :
    Algebra.trace F E (m * x + b) = Algebra.norm F x ↔ x = conjugate F E m := by
  rw [on_slope_iff F E h, ht, Algebra.norm_eq_zero_iff, sub_eq_zero]

#print axioms slope_secant_card
#print axioms tangent_iff

/-- Incidence with an affine vertical line or a line of given slope.
The unique point at infinity belongs to all vertical lines. -/
def incident (d : Option E) (b : E) : Option (AffinePoint F E) → Prop
  | none => d = none
  | some P => match d with
    | none => P.val.1 = b
    | some m => P.val.2 = m * P.val.1 + b

private theorem vertical_card (h : Module.finrank F E = 2) (b : E) :
    Nat.card {P // incident F E none b P} = Nat.card F + 1 := by
  classical
  let B := {y : E // Algebra.trace F E y = Algebra.norm F b}
  let e : {P // incident F E none b P} ≃ Option B :=
    { toFun := fun a => match a with
        | ⟨none, _⟩ => none
        | ⟨some P, hp⟩ => some ⟨P.val.2, by
            change P.val.1 = b at hp
            exact hp ▸ P.property⟩
      invFun := fun a => match a with
        | none => ⟨none, rfl⟩
        | some y => ⟨some ⟨(b, y.val), y.property⟩, rfl⟩
      left_inv := by
        rintro ⟨_ | P, hp⟩
        · rfl
        · apply Subtype.ext
          apply congrArg some
          apply Subtype.ext
          exact Prod.ext hp.symm rfl
      right_inv := by rintro (_ | y) <;> rfl }
  let : Fintype B := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option,
    ← Nat.card_eq_fintype_card, trace_fiber_card F E h]

private theorem nonvertical_card (h : Module.finrank F E = 2) (m b : E)
    (hs : Algebra.trace F E b + Algebra.norm F m ≠ 0) :
    Nat.card {P // incident F E (some m) b P} = Nat.card F + 1 := by
  let e : {P // incident F E (some m) b P} ≃
      {x : E // Algebra.trace F E (m * x + b) = Algebra.norm F x} :=
    { toFun := fun a => match a with
        | ⟨none, hp⟩ => ((Option.some_ne_none m) hp).elim
        | ⟨some P, hp⟩ => ⟨P.val.1, by
            change P.val.2 = m * P.val.1 + b at hp
            exact hp ▸ P.property⟩
      invFun := fun x => ⟨some ⟨(x.val, m * x.val + b), x.property⟩, rfl⟩
      left_inv := by
        rintro ⟨_ | P, hp⟩
        · exact ((Option.some_ne_none m) hp).elim
        · apply Subtype.ext
          apply congrArg some
          apply Subtype.ext
          exact Prod.ext rfl hp.symm
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (slope_secant_card F E h m b hs)

omit [Fintype F] [Fintype E] in
private theorem affine_incident (l : Option E × E) (P : AffinePoint F E) :
    incident F E l.1 l.2 (some P) ↔ Denniston.intercept l.1 P.val = l.2 := by
  rcases l with ⟨_ | m, b⟩ <;> simp [incident, Denniston.intercept, sub_eq_iff_eq_add, add_comm]

omit [Fintype F] [Fintype E] in
private theorem line_at_infinity (P : AffinePoint F E) :
    ∃! l : Option E × E, incident F E l.1 l.2 none ∧ incident F E l.1 l.2 (some P) := by
  refine ⟨(none, P.val.1), ⟨rfl,rfl⟩, ?_⟩
  rintro ⟨d,b⟩ ⟨hd,hp⟩
  change d = none at hd
  subst d
  exact Prod.ext rfl hp.symm

omit [Fintype F] [Fintype E] in
private theorem unique_line {P Q : Option (AffinePoint F E)} (hne : P ≠ Q) :
    ∃! l : Option E × E, incident F E l.1 l.2 P ∧ incident F E l.1 l.2 Q := by
  cases P with
  | none =>
    cases Q with
    | none => exact (hne rfl).elim
    | some Q => exact line_at_infinity F E Q
  | some P =>
    cases Q with
    | none => simpa only [and_comm] using line_at_infinity F E P
    | some Q =>
      have hpq : P.val ≠ Q.val := fun h => hne (congrArg some (Subtype.ext h))
      simpa only [affine_incident] using Denniston.line_through hpq

/-- Vertical lines and nonvertical lines with nonzero translated norm level. -/
def secant : Option E → E → Prop
  | none, _ => True
  | some m, b => Algebra.trace F E b + Algebra.norm F m ≠ 0

private theorem secant_of_pair (l : Option E × E) {P Q : Option (AffinePoint F E)}
    (h : Module.finrank F E = 2) (hne : P ≠ Q)
    (hp : incident F E l.1 l.2 P) (hq : incident F E l.1 l.2 Q) : secant F E l.1 l.2 := by
  rcases l with ⟨_ | m, b⟩
  · trivial
  · intro ht
    rcases P with _ | P
    · exact (Option.some_ne_none m) hp
    rcases Q with _ | Q
    · exact (Option.some_ne_none m) hq
    change P.val.2 = m * P.val.1 + b at hp
    change Q.val.2 = m * Q.val.1 + b at hq
    have hx := ((tangent_iff F E h m b _ ht).mp (hp ▸ P.property)).trans
      ((tangent_iff F E h m b _ ht).mp (hq ▸ Q.property)).symm
    exact hne (congrArg some (Subtype.ext (Prod.ext hx (by rw [hp,hq,hx]))))

variable {V : Type*} [Fintype V]

private noncomputable def block (e : V ≃ Option (AffinePoint F E)) (l : Option E × E) : Finset V := by
  classical exact univ.filter fun v => incident F E l.1 l.2 (e v)

omit [Fintype F] [Fintype E] in
private theorem mem_block (e : V ≃ Option (AffinePoint F E)) (l : Option E × E) (v : V) :
    v ∈ block F E e l ↔ incident F E l.1 l.2 (e v) := by classical simp [block]

private theorem block_card (h : Module.finrank F E = 2) (e : V ≃ Option (AffinePoint F E))
    (l : Option E × E) (hs : secant F E l.1 l.2) : (block F E e l).card = Nat.card F + 1 := by
  classical
  let f : (block F E e l) ≃ {P // incident F E l.1 l.2 P} :=
    e.subtypeEquiv (fun v => mem_block F E e l v)
  rw [← Nat.card_eq_finsetCard, Nat.card_congr f]
  rcases l with ⟨_ | m,b⟩
  · exact vertical_card F E h b
  · exact nonvertical_card F E h m b hs

/-- The secants of the projective Hermitian curve form a Steiner pair design. -/
theorem exists_unital_design (h : Module.finrank F E = 2) (e : V ≃ Option (AffinePoint F E)) :
    ∃ D : Finset (Finset V), D.IsBlockDesign 2 (Nat.card F + 1) := by
  classical
  let D : Finset (Finset V) := univ.filter fun B => ∃ l, secant F E l.1 l.2 ∧ B = block F E e l
  have hD (B) : B ∈ D ↔ ∃ l, secant F E l.1 l.2 ∧ B = block F E e l := by simp [D]
  refine ⟨D, ?_, ?_⟩
  · intro B hB
    obtain ⟨l,hs,rfl⟩ := (hD B).mp hB
    exact block_card F E h e l hs
  · intro S hS
    obtain ⟨v,w,hvw,rfl⟩ := Finset.card_eq_two.mp hS
    have hne := e.injective.ne hvw
    obtain ⟨l,⟨hv,hw⟩,hu⟩ := unique_line F E hne
    refine ⟨block F E e l, ⟨(hD _).mpr ⟨l,secant_of_pair F E l h hne hv hw,rfl⟩, ?_⟩, ?_⟩
    · simpa only [insert_subset_iff, singleton_subset_iff, mem_block] using And.intro hv hw
    · rintro B ⟨hB,hsub⟩
      obtain ⟨m,_,rfl⟩ := (hD B).mp hB
      apply congrArg (block F E e)
      apply hu
      simpa only [insert_subset_iff, singleton_subset_iff, mem_block] using hsub

/-- A classical Hermitian unital of order `p^a`, on the exact upstream vertex type. -/
theorem prime_power_unital (p a : ℕ) [Fact p.Prime] (ha : 0 < a) :
    ∃ D : Finset (Finset (Fin ((p^a)^3 + 1))), D.IsBlockDesign 2 (p^a + 1) := by
  classical
  let F := GaloisField p a
  let E := FiniteField.Extension F p 2
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E := Fintype.ofFinite E
  have hF : Nat.card F = p^a := GaloisField.card p a ha.ne'
  have h : Module.finrank F E = 2 := FiniteField.finrank_extension F p 2
  let : Fintype (AffinePoint F E) := Fintype.ofFinite _
  have hc : Fintype.card (Option (AffinePoint F E)) = (p^a)^3 + 1 := by
    rw [← Nat.card_eq_fintype_card, unital_point_count F E h, hF]
  simpa only [hF] using exists_unital_design F E h (Fintype.equivFinOfCardEq hc).symm

#print axioms exists_unital_design
#print axioms prime_power_unital

end Erdos722.HermitianUnital
