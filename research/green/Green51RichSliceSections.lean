import Green51PartialCircuitWords
import Green51DenseAdditivity
import Green51RichCircuitSlices

/-! # Common linear sections for all odd-girth-preserving extensions -/

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold Green51SliceStability
open scoped Classical Pointwise
variable {G V : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Module.Finite F G]
  [AddCommGroup V] [Module F V] [DecidableEq V] [Fintype V]

/-- The same linear section describes every extension that preserves the shortest circuit. -/
theorem glue_all_extensions {D C : Finset G} (m : ShortestOddCircuit D C) (π : G →ₗ[F] V)
    (ker : π.ker = Submodule.span F (C : Set G)) (k : ℕ) (k5 : 5 ≤ k) (H : Finset V) (zero : 0 ∈ H)
    (dense : 5 * Fintype.card V < 8 * H.card ∨ 6 ≤ k ∧ Fintype.card V < 2 * H.card)
    (stars : ∀ q ∈ H, ∃ t : G, π t = q ∧ ∃ I ⊆ C, k ≤ I.card ∧ ∀ i ∈ I, t + i ∈ D) :
    ∃ L : V →ₗ[F] G, π.comp L = LinearMap.id ∧ ∀ E : Finset G, D ⊆ E → ShortestOddCircuit E C → ∀ x ∈ E, ∃ i ∈ C, x = L (π x) + i := by
  classical
  obtain ⟨f0, I0, selected⟩ : ∃ (f0 : H → G) (I0 : H → Finset G),
      ∀ u : H, π (f0 u) = u ∧ I0 u ⊆ C ∧ k ≤ (I0 u).card ∧ ∀ i ∈ I0 u, f0 u + i ∈ D := by
    have choose_star (u : H) : ∃ t : G, ∃ I : Finset G,
        π t = u ∧ I ⊆ C ∧ k ≤ I.card ∧ ∀ i ∈ I, t + i ∈ D := by
      obtain ⟨t, val, I, sub, size, mem⟩ := stars u u.property
      exact ⟨t, I, val, sub, size, mem⟩
    choose f0 I0 ok using choose_star
    exact ⟨f0, I0, ok⟩
  let f (u : V) := if hu : u ∈ H then f0 ⟨u, hu⟩ else 0
  let I (u : V) := if hu : u ∈ H then I0 ⟨u, hu⟩ else ∅
  have good (u : V) (hu : u ∈ H) : π (f u) = u ∧ I u ⊆ C ∧ k ≤ (I u).card ∧ ∀ i ∈ I u, f u + i ∈ D := by
    simpa only [f, I, dif_pos hu] using selected ⟨u, hu⟩
  have onC {i : G} (hi : i ∈ C) : π i = 0 := LinearMap.mem_ker.mp (ker.symm ▸ Submodule.subset_span hi)
  have lies {E : Finset G} (incl : D ⊆ E) (me : ShortestOddCircuit E C) (u v : V) (hu : u ∈ H) (hv : v ∈ H) (x : G) (hx : x ∈ E) (at_sum : π x = u + v) :
      ∃ i ∈ C, x = (f u + f v) + i := by
    obtain ⟨uval, ui, u5, um⟩ := good u hu
    obtain ⟨vval, vi, v5, vm⟩ := good v hv
    have ink : f u + f v + x ∈ Submodule.span F (C : Set G) := by
      rw [←ker, LinearMap.mem_ker, map_add, map_add, uval, vval, at_sum, ZModModule.add_self]
    obtain ⟨i, hi, eq⟩ := two_fibre_container me ui vi (k5.trans u5) (k5.trans v5) (fun i hi => incl (um i hi)) (fun i hi => incl (vm i hi)) hx ink
    exact ⟨i, hi, by rw [←eq, ←add_assoc, ZModModule.add_self, zero_add]⟩
  have compat (u : V) (hu : u ∈ H) (v : V) (hv : v ∈ H) (hw : u + v ∈ H) :
      f (u + v) = f u + f v := by
    obtain ⟨val, inc, many, inside⟩ := good (u + v) hw
    apply partial_centres_unique m inc (by omega)
    intro i hi
    exact lies Subset.rfl m u v hu hv _ (inside i hi) (by rw [map_add, val, onC (inc hi), add_zero])
  have section_sums : ∃ L : V →ₗ[F] G, ∀ u v : V, u ∈ H → v ∈ H → L (u + v) = f u + f v := by
    rcases dense with enough | ⟨six, half⟩
    · obtain ⟨L, agree⟩ := vector_extension H f zero enough compat
      exact ⟨L, fun u v hu hv => by rw [map_add, agree u hu, agree v hv]⟩
    · apply extend_pair_sums H f half
      intro a b c d ha hb hc hd eq
      obtain ⟨pa, Ia, sa, aI⟩ := good a ha
      obtain ⟨pb, Ib, sb, bI⟩ := good b hb
      obtain ⟨pc, Ic, sc, cI⟩ := good c hc
      obtain ⟨pd, Id, sd, dI⟩ := good d hd
      apply four_fibre_relation m Ia Ib Ic Id (six.trans sa) (six.trans sb) (six.trans sc) (six.trans sd) aI bI cI dI
      rw [←ker, LinearMap.mem_ker, map_add, map_add, map_add, pa, pb, pc, pd, add_assoc (a+b), eq, ZModModule.add_self]
  obtain ⟨L, sums⟩ := section_sums
  have half : Fintype.card V < 2 * H.card := by
    rcases dense with enough | ⟨_, enough⟩ <;> omega
  have pair (u : V) : ∃ a ∈ H, ∃ b ∈ H, a + b = u := by
    obtain ⟨t, ht, hu, _⟩ := three_shifts H half u u
    exact ⟨t, ht, t + u, hu, by rw [←add_assoc, ZModModule.add_self, zero_add]⟩
  refine ⟨L, ?_, ?_⟩
  · ext u
    obtain ⟨a, ha, b, hb, rfl⟩ := pair u
    change π (L (a + b)) = a + b
    rw [sums a b ha hb, map_add, (good a ha).1, (good b hb).1]
  · intro E incl me x hx
    obtain ⟨a, ha, b, hb, eq⟩ := pair (π x)
    simpa only [←eq, sums a b ha hb] using lies incl me a b ha hb x hx eq.symm

end Green51GirthFrame
#print axioms Green51GirthFrame.glue_all_extensions

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51SliceStability
open scoped Classical Pointwise
variable {G V : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]
  [AddCommGroup V] [Module F V] [DecidableEq V] [Fintype V]

private theorem rich_count_arithmetic (g h b k : ℕ) (size : 5 ≤ g)
    (count : k ≤ h * g + b * 4) (near : (5 * g + 12) * (h + b) < 8 * k) : 5 * (h + b) < 8 * h := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ g by omega)
  by_contra! bad
  nlinarith only [count, near, Nat.mul_le_mul_right e bad]

private theorem half_count_arithmetic (g h b k : ℕ) (size : 6 ≤ g)
    (count : k ≤ h * g + b * 5) (near : (g + 5) * (h + b) < 2 * k) : h + b < 2 * h := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (show 5 ≤ g by omega)
  by_contra! bad
  have le : h ≤ b := by omega
  nlinarith only [count, near, Nat.mul_le_mul_right e le]

/-- Either density bound supplies a section containing every extension in the same translated fibres. -/
theorem dense_universal_projection {D C : Finset G} (m : ShortestOddCircuit D C) (g : 5 ≤ C.card)
    (π : G →ₗ[F] V) (surj : Function.Surjective π) (ker : π.ker = Submodule.span F (C : Set G))
    (near : (5 * C.card + 12) * Fintype.card V < 8 * D.card ∨
      6 ≤ C.card ∧ (C.card + 5) * Fintype.card V < 2 * D.card) :
    ∃ L : V →ₗ[F] G, π.comp L = LinearMap.id ∧ ∀ E : Finset G, D ⊆ E → ShortestOddCircuit E C → ∀ x ∈ E, ∃ i ∈ C, x = L (π x) + i := by
  let fibre (q : V) := D.filter fun x => π x = q
  let k := if (5 * C.card + 12) * Fintype.card V < 8 * D.card then 5 else 6
  have k5 : 5 ≤ k := by dsimp [k]; split <;> decide
  have kC : k ≤ C.card := by
    dsimp [k]; split
    · exact g
    · next no => exact (near.resolve_left no).1
  let H := univ.filter fun q => k ≤ (fibre q).card
  have cap (q : V) : (fibre q).card ≤ C.card := by
    obtain ⟨a, rfl⟩ := surj q
    dsimp only [fibre]
    rw [coded_fibre m π ker a]
    exact card_image_le.trans (slice_shape m g {a}).1
  have small (q : V) (hq : q ∈ Hᶜ) : (fibre q).card ≤ k-1 := by
    have h : ¬k ≤ (fibre q).card := fun he => mem_compl.mp hq (mem_filter.mpr ⟨mem_univ _, he⟩)
    omega
  have total : D.card = ∑ q, (fibre q).card := card_eq_sum_card_fiberwise fun x _ => mem_univ (π x)
  have one : ∑ q ∈ H, (fibre q).card ≤ H.card * C.card := by simpa using sum_le_sum (fun q (_ : q ∈ H) => cap q)
  have two : ∑ q ∈ Hᶜ, (fibre q).card ≤ Hᶜ.card * (k-1) := by simpa using sum_le_sum small
  have bound := Nat.add_le_add one two
  rw [sum_add_sum_compl, ←total] at bound
  have n := Finset.card_add_card_compl H
  have dense : 5 * Fintype.card V < 8 * H.card ∨ 6 ≤ k ∧ Fintype.card V < 2 * H.card := by
    by_cases old : (5 * C.card + 12) * Fintype.card V < 8 * D.card
    · have keq : k = 5 := if_pos old
      rw [keq] at bound
      exact Or.inl (n ▸ rich_count_arithmetic _ _ _ _ g bound (n ▸ old))
    · obtain ⟨six, high⟩ := near.resolve_left old
      have keq : k = 6 := if_neg old
      rw [keq] at bound ⊢
      exact Or.inr ⟨le_rfl, n ▸ half_count_arithmetic _ _ _ _ six bound (n ▸ high)⟩
  have rich0 : 0 ∈ H := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, kC.trans (card_le_card ?_)⟩
    intro i hi
    exact mem_filter.mpr ⟨m.1 hi, LinearMap.mem_ker.mp (ker.symm ▸ Submodule.subset_span hi)⟩
  apply glue_all_extensions m π ker k k5 H rich0 dense
  intro q hq
  obtain ⟨a, rfl⟩ := surj q
  have rich : k ≤ (fibre (π a)).card := (mem_filter.mp hq).2
  obtain ⟨t, ht, I, hI, sz, inside⟩ := rich_fibre m π ker a (k5.trans rich)
  exact ⟨t, ht, I, hI, rich.trans sz, inside⟩

end Green51GirthFrame
#print axioms Green51GirthFrame.dense_universal_projection
