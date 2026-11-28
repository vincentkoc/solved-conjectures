import Erdos722HermitianUnitals
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Collinear

/-!
# Filling finite projective lines with Hermitian unitals

Each line of projective space over a field of order `q^3` has the order of the
Hermitian unital over a field of order `q`. Replacing each such line by the
blocks of one unital gives an explicit sequence of orders at fixed block size.
-/

namespace Erdos722.HermitianUnital
open Finset
open scoped LinearAlgebra.Projectivization

/-- Replace each line of a linear space by a copy of a Steiner pair design. -/
theorem fill_lines {W V I : Type*} [Fintype V] {k : ℕ} {C : Finset (Finset W)}
    (hC : C.IsBlockDesign 2 k) (e : I → W ↪ V)
    (through : ∀ x y : V, x ≠ y → ∃! i, x ∈ Set.range (e i) ∧ y ∈ Set.range (e i)) :
    ∃ D : Finset (Finset V), D.IsBlockDesign 2 k := by
  classical
  let D : Finset (Finset V) := univ.filter fun A => ∃ i B, B ∈ C ∧ A = B.map (e i)
  have memD (A) : A ∈ D ↔ ∃ i B, B ∈ C ∧ A = B.map (e i) := by simp [D]
  refine ⟨D, ?_, ?_⟩
  · intro A hA
    obtain ⟨i,B,hB,rfl⟩ := (memD A).mp hA
    simpa using hC.1 B hB
  · intro S hS
    obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hS
    obtain ⟨i,⟨⟨a,ha⟩,⟨b,hb⟩⟩,hu⟩ := through x y hxy
    subst x y
    have hab : a ≠ b := fun he => hxy (congrArg (e i) he)
    obtain ⟨B,⟨hB,hsub⟩,huniq⟩ := hC.2 {a,b} (card_pair hab)
    obtain ⟨ha,hb⟩ := insert_subset_iff.mp hsub
    have hb' := singleton_subset_iff.mp hb
    refine ⟨B.map (e i), ⟨(memD _).mpr ⟨i,B,hB,rfl⟩, ?_⟩, ?_⟩
    · simp only [insert_subset_iff, singleton_subset_iff, mem_map']
      exact ⟨ha,hb'⟩
    · rintro A ⟨hA,hsub'⟩
      obtain ⟨j,T,hT,rfl⟩ := (memD A).mp hA
      obtain ⟨hx,hy⟩ := insert_subset_iff.mp hsub'
      have hy' := singleton_subset_iff.mp hy
      obtain ⟨c,hc,he⟩ := mem_map.mp hx
      obtain ⟨d,hd,hf⟩ := mem_map.mp hy'
      have hj := hu j ⟨⟨c,he⟩,⟨d,hf⟩⟩
      subst j
      apply congrArg (Finset.map (e i))
      apply huniq
      refine ⟨hT,insert_subset ((e i).injective he ▸ hc) ?_⟩
      exact singleton_subset_iff.mpr ((e i).injective hf ▸ hd)

#print axioms fill_lines

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

private def lineInclusion (L : Submodule K M) : ℙ K L ↪ ℙ K M :=
  ⟨Projectivization.map L.subtype L.injective_subtype,
    Projectivization.map_injective L.subtype L.injective_subtype⟩

private theorem in_line (L : Submodule K M) (P : ℙ K M) :
    P ∈ Set.range (lineInclusion L) ↔ P ∈ L.projectivization := by
  constructor
  · rintro ⟨a,rfl⟩
    induction a using Projectivization.ind with
    | h v hv => exact v.property
  · induction P using Projectivization.ind with
    | h v hv =>
      intro h
      let w : L := ⟨v,h⟩
      have hw : w ≠ 0 := fun h0 => hv (congrArg Subtype.val h0)
      exact ⟨Projectivization.mk K w hw,rfl⟩

private theorem through_projective_pair (P Q : ℙ K M) (hne : P ≠ Q) :
    ∃! L : {L : Submodule K M // Module.finrank K L = 2},
      P ∈ L.val.projectivization ∧ Q ∈ L.val.projectivization := by
  induction P using Projectivization.ind with
  | h u hu =>
    induction Q using Projectivization.ind with
    | h v hv =>
      have hi := (Projectivization.independent_mk_iff_LinearIndependent hu hv).mp
        ((Projectivization.independent_pair_iff_ne _ _).mpr hne)
      let L := Submodule.span K {u,v}
      have hL : Module.finrank K L = 2 := by
        change Module.finrank K (Submodule.span K {u,v}) = 2
        rw [← Matrix.range_cons_cons_empty u v ![]]
        simp [finrank_span_eq_card hi]
      refine ⟨⟨L,hL⟩, ⟨?_,?_⟩, ?_⟩
      · exact Submodule.mem_span_of_mem (by simp)
      · exact Submodule.mem_span_of_mem (by simp)
      · rintro ⟨N,hN⟩ ⟨hP,hQ⟩
        exact Subtype.ext (Projectivization.line_unique' hu hv hi N hN hP hQ)

private noncomputable def labels {X : Type*} [Finite X] {n : ℕ} (h : Nat.card X = n) : X ≃ Fin n := by
  let : Fintype X := Fintype.ofFinite X
  exact Fintype.equivFinOfCardEq (by rwa [← Nat.card_eq_fintype_card])

/-- Any pair design on a projective line can fill the lines in every dimension. -/
theorem projective_design (K : Type*) [Field K] [Finite K] (n k : ℕ)
    (seed : ∃ C : Finset (Finset (Fin (Nat.card K + 1))), C.IsBlockDesign 2 k) :
    ∃ D : Finset (Finset (Fin (∑ i ∈ range n, Nat.card K ^ i))), D.IsBlockDesign 2 k := by
  classical
  let M := Fin n → K
  let I := {L : Submodule K M // Module.finrank K L = 2}
  let V := Fin (∑ i ∈ range n, Nat.card K ^ i)
  let g : ℙ K M ≃ V := labels (Projectivization.card_of_finrank K M (by simp [M]))
  let c (L : I) : ℙ K L.val ≃ Fin (Nat.card K + 1) :=
    labels (Projectivization.card_of_finrank_two K L.val L.property)
  let e (L : I) := ((c L).symm.toEmbedding.trans (lineInclusion L.val)).trans g.toEmbedding
  have hmem (v : V) (L : I) : v ∈ Set.range (e L) ↔ g.symm v ∈ L.val.projectivization := by
    rw [← in_line]
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨(c L).symm t, (g.symm_apply_apply _).symm⟩
    · rintro ⟨t,ht⟩
      use c L t
      change g (lineInclusion L.val ((c L).symm (c L t))) = v
      rw [(c L).symm_apply_apply, ht, g.apply_symm_apply]
  obtain ⟨C,hC⟩ := seed
  apply fill_lines hC e
  intro x y hxy
  simpa only [hmem] using through_projective_pair (g.symm x) (g.symm y) (g.symm.injective.ne hxy)

/-- Orders `1 + q^3 + ⋯ + (q^3)^(n-1)` for the single fixed block size `q+1`. -/
theorem prime_power_projective_unitals (p a n : ℕ) [Fact p.Prime] (ha : 0 < a) :
    ∃ D : Finset (Finset (Fin (∑ i ∈ range n, ((p^a)^3)^i))), D.IsBlockDesign 2 (p^a + 1) := by
  let K := GaloisField p (a*3)
  have hK : Nat.card K = (p^a)^3 := by
    rw [← pow_mul]
    exact GaloisField.card p (a*3) (by positivity)
  exact hK ▸ projective_design K n (p^a + 1) (hK.symm ▸ prime_power_unital p a ha)

theorem frequently_projective_unitals (p a : ℕ) [Fact p.Prime] (ha : 0 < a) :
    ∃ᶠ n : ℕ in Filter.atTop, ∃ D : Finset (Finset (Fin n)), D.IsBlockDesign 2 (p^a + 1) := by
  apply Filter.frequently_atTop.mpr
  intro N
  refine ⟨_, ?_, prime_power_projective_unitals p a N ha⟩
  have hp := (Fact.out : p.Prime).pos
  calc
    N = ∑ _i ∈ range N, 1 := by simp
    _ ≤ _ := sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (by positivity)

#print axioms projective_design
#print axioms prime_power_projective_unitals
#print axioms frequently_projective_unitals

end Erdos722.HermitianUnital
