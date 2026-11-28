import Green51CodimensionTwo

/-! # Coordinates from a shortest odd circuit -/

open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff

namespace Green51GirthFrame
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- A shortest odd zero-sum subset of the given directions. -/
def ShortestOddCircuit [DecidableEq G] (D C : Finset G) : Prop :=
  C ⊆ D ∧ Odd C.card ∧ (∑ x ∈ C, x) = 0 ∧
    ∀ R ⊆ D, Odd R.card → (∑ x ∈ R, x) = 0 → C.card ≤ R.card

/-- Either a single binary functional is one on all directions, or there is a shortest odd circuit. -/
theorem choose_circuit [Module.Finite F G] [DecidableEq G] (D : Finset G) :
    (∃ f : G →ₗ[F] F, ∀ x ∈ D, f x = 1) ∨ ∃ C, ShortestOddCircuit D C := by
  classical
  obtain ⟨B, sub, _, span, ind⟩ := Submodule.exists_finset_span_eq_linearIndepOn F (D : Set G)
  obtain ⟨f, ones⟩ := Module.exists_dual_forall_apply_eq_one ind
  change ∀ i ∈ B, f i = 1 at ones
  by_cases all : ∀ x ∈ D, f x = 1
  · exact .inl ⟨f, all⟩
  right
  push Not at all
  obtain ⟨x, hx, notone⟩ := all
  obtain ⟨S, sb, total⟩ := subset_sum B x (span.symm ▸ Submodule.subset_span hx)
  have zero : f x = 0 := ((show ∀ y : F, y = 0 ∨ y = 1 from by decide) _).resolve_right notone
  have eq := congrArg f total
  rw [map_sum, zero, sum_eq_card_nsmul (fun y hy => ones _ (sb hy))] at eq
  have even : 2 ∣ S.card := by simpa only [nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff] using eq
  have nx : x ∉ S := fun h => notone (ones _ (sb h))
  let fam := D.powerset.filter fun R => Odd R.card ∧ (∑ x ∈ R, x) = 0
  have good : insert x S ∈ fam := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (insert_subset hx (fun y hy => sub (sb hy))), ?_, ?_⟩
    · rw [card_insert_of_notMem nx, Nat.odd_iff]; omega
    · rw [sum_insert nx, total, ZModModule.add_self]
  obtain ⟨C, hC, least⟩ := fam.exists_min_image Finset.card ⟨_, good⟩
  obtain ⟨subC, oddC, sumC⟩ := mem_filter.mp hC
  exact ⟨C, mem_powerset.mp subC, oddC, sumC, fun R hr ho hs => least R (mem_filter.mpr ⟨mem_powerset.mpr hr, ho, hs⟩)⟩

/-- Deleting a point of a shortest odd circuit leaves an independent family. -/
theorem independent_erase [DecidableEq G] {D C : Finset G} (minC : ShortestOddCircuit D C) {p : G} (hp : p ∈ C) :
    LinearIndepOn F id ((C.erase p : Finset G) : Set G) := by
  classical
  obtain ⟨sub, odd, zero, least⟩ := minC
  let T := C.erase p
  obtain ⟨B, bt, _, span, ind⟩ := Submodule.exists_finset_span_eq_linearIndepOn F (T : Set G)
  have whole : B = T := by
    apply Finset.Subset.antisymm (show B ⊆ T from bt)
    intro v hv
    by_contra nv
    obtain ⟨S, sb, eq⟩ := subset_sum B v (span.symm ▸ Submodule.subset_span hv)
    have ns : v ∉ S := fun h => nv (sb h)
    let R := insert v S
    have rt : R ⊆ T := insert_subset hv (fun x hx => bt (sb hx))
    have rc : R ⊆ C := rt.trans (erase_subset _ _)
    have smaller : R.card < C.card := by
      have le := card_le_card rt
      change R.card ≤ (C.erase p).card at le
      rw [card_erase_of_mem hp] at le
      have := card_pos.mpr (show C.Nonempty from ⟨_, hp⟩)
      omega
    have zr : (∑ x ∈ R, x) = 0 := by dsimp only [R]; rw [sum_insert ns, eq, ZModModule.add_self]
    by_cases par : Odd R.card
    · exact (not_le_of_gt smaller) (least R (rc.trans sub) par zr)
    · have total := sum_sdiff rc (f := id)
      change (∑ x ∈ C \ R, x) + (∑ x ∈ R, x) = ∑ x ∈ C, x at total
      rw [zr, add_zero, zero] at total
      have pos : 0 < R.card := card_pos.mpr ⟨v, mem_insert_self _ _⟩
      have sz := card_sdiff_of_subset rc
      have le := least (C \ R) (sdiff_subset.trans sub) (by simp only [Nat.odd_iff] at odd par ⊢; omega) total
      omega
  rw [←show B = C.erase p from whole]
  exact ind

/-- Complementary subsets of a binary zero-sum set have the same sum. -/
theorem circuit_complement_sum [DecidableEq G] {C S : Finset G} (sc : S ⊆ C) (zero : (∑ x ∈ C, x) = 0) :
    (∑ x ∈ C \ S, x) = ∑ x ∈ S, x := by
  have h := sum_sdiff sc (f := id)
  change (∑ x ∈ C \ S, x) + (∑ x ∈ S, x) = ∑ x ∈ C, x at h
  rw [zero] at h
  calc
    _ = (∑ x ∈ C \ S, x) + ((∑ x ∈ S, x) + (∑ x ∈ S, x)) := by rw [ZModModule.add_self, add_zero]
    _ = _ := by rw [←add_assoc, h, zero_add]

end Green51GirthFrame

namespace Green51GirthFrame
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

/-- Complete a shortest circuit with independent directions, keeping the additional basis
directions in the original set. Each direction has an odd representation in these coordinates. -/
theorem coordinates {D C : Finset G} (m : ShortestOddCircuit D C) {p : G} (hp : p ∈ C) :
    ∃ H : Finset G, C.erase p ⊆ H ∧ H ⊆ D ∧ LinearIndepOn F id (H : Set G) ∧
      H.card ≤ Module.finrank F G ∧
      ∀ x ∈ D, ∃ Q ⊆ H \ (C.erase p), ∃ S ⊆ C, Odd (S.card + Q.card) ∧ (∑ s ∈ S, s) + (∑ q ∈ Q, q) = x := by
  classical
  let B := C.erase p
  have ind := independent_erase m hp
  have bd : (B : Set G) ⊆ (D : Set G) := fun x hx => m.1 (mem_erase.mp hx).2
  let H := (ind.extend bd).toFinset
  have extH : (H : Set G) = ind.extend bd := Set.coe_toFinset _
  have bh : B ⊆ H := fun x hx => (Set.mem_toFinset.mpr (ind.subset_extend bd hx))
  have hd : H ⊆ D := fun x hx => ind.extend_subset bd (Set.mem_toFinset.mp hx)
  have ih : LinearIndepOn F id (H : Set G) := extH ▸ ind.linearIndepOn_extend bd
  refine ⟨H, bh, hd, ih, by simpa using ih.linearIndependent.fintype_card_le_finrank, ?_⟩
  intro x hx
  have mem : x ∈ Submodule.span F (H : Set G) := extH ▸ ind.subset_span_extend bd hx
  obtain ⟨T, th, rep⟩ := subset_sum H x mem
  let R := T ∩ B
  let Q := T \ B
  have split := sum_inter_add_sum_sdiff T B id
  change (∑ s ∈ R, s) + (∑ q ∈ Q, q) = ∑ t ∈ T, t at split
  have rc : R ⊆ C := inter_subset_right.trans (erase_subset _ _)
  refine ⟨Q, fun u hu => mem_sdiff.mpr ⟨th (mem_sdiff.mp hu).1, (mem_sdiff.mp hu).2⟩, ?_⟩
  by_cases odd : Odd (R.card + Q.card)
  · exact ⟨R, rc, odd, split.trans rep⟩
  · have co := card_sdiff_add_card_eq_card rc
    have cp := m.2.1
    refine ⟨C \ R, sdiff_subset, by simp only [Nat.odd_iff] at cp odd ⊢; omega, ?_⟩
    rw [circuit_complement_sum rc m.2.2.1, split, rep]

end Green51GirthFrame

#print axioms Green51GirthFrame.choose_circuit
#print axioms Green51GirthFrame.independent_erase
#print axioms Green51GirthFrame.circuit_complement_sum
#print axioms Green51GirthFrame.coordinates
