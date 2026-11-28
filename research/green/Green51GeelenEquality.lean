import Green51CircuitCentres

/-! # Equality in Geelen's odd-girth bound -/

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

omit [DecidableEq G] in
private theorem circuit_span_sum {U C : Finset G} (uc : U ⊆ C) :
    (∑ x ∈ U, x) ∈ Submodule.span F (C : Set G) :=
  Submodule.sum_mem _ fun _ hx => Submodule.subset_span (uc hx)

private theorem outside_coordinates {H B C : Finset G} (bc : B ⊆ C)
    (whole : Submodule.span F (H : Set G) = ⊤) (x : G) :
    ∃ Q ⊆ H \ B, x + (∑ q ∈ Q, q) ∈ Submodule.span F (C : Set G) := by
  obtain ⟨U, uh, rep⟩ := subset_sum H x (whole ▸ Submodule.mem_top)
  let Q := U \ B
  refine ⟨Q, fun y hy => mem_sdiff.mpr ⟨uh (mem_sdiff.mp hy).1, (mem_sdiff.mp hy).2⟩, ?_⟩
  have eq := sum_inter_add_sum_sdiff U B id
  change (∑ x ∈ U ∩ B, x) + (∑ q ∈ Q, q) = ∑ u ∈ U, u at eq
  rw [←rep, ←eq, add_assoc, ZModModule.add_self, add_zero]
  exact circuit_span_sum (inter_subset_right.trans bc)

variable [Fintype G]

/-- Equality for a fixed shortest circuit makes the directions a full pullback of that circuit. -/
theorem circuit_equality {D C : Finset G} (m : ShortestOddCircuit D C) (g : 5 ≤ C.card)
    (saturates : C.card * 2 ^ (Module.finrank F G + 1 - C.card) ≤ D.card) :
    ∃ P : Submodule F G, IsCompl P (Submodule.span F (C : Set G)) ∧
      ∀ x, x ∈ D ↔ ∃ t ∈ P, ∃ i ∈ C, x = t + i := by
  classical
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < C.card by omega)
  let B := C.erase p
  obtain ⟨H, bh, _, ind, hRank, reps⟩ := coordinates m hp
  let Z := H \ B
  have bc : B.card = C.card - 1 := card_erase_of_mem hp
  have zc : Z.card + B.card = H.card := card_sdiff_add_card_eq_card bh
  have cover := cover_by_slices (D := D) (C := C) (Z := Z) reps
  have lower : D.card ≤ ∑ Q ∈ Z.powerset, (sliceWords D C Q).card :=
    ((card_le_card cover).trans card_biUnion_le).trans (sum_le_sum fun Q _ => card_image_le)
  have caps : (∑ Q ∈ Z.powerset, (sliceWords D C Q).card) ≤ ∑ _ ∈ Z.powerset, C.card :=
    sum_le_sum fun Q _ => (slice_shape m g Q).1
  have sumC : (∑ _ ∈ Z.powerset, C.card) = C.card * 2 ^ Z.card := by simp [smul_eq_mul, mul_comm]
  have bound := lower.trans (caps.trans_eq sumC)
  have zrank : Z.card = Module.finrank F G + 1 - C.card := by
    by_contra! ne
    have smaller : Z.card < Module.finrank F G + 1 - C.card := by omega
    have power := Nat.pow_lt_pow_right (by decide : 1 < 2) smaller
    exact (Nat.not_lt_of_ge (saturates.trans bound)) (Nat.mul_lt_mul_of_pos_left power (by omega))
  have eqS : (∑ Q ∈ Z.powerset, (sliceWords D C Q).card) = ∑ _ ∈ Z.powerset, C.card := by
    apply le_antisymm caps
    rw [sumC, zrank]
    exact saturates.trans lower
  have fullQ (Q : Finset G) (qz : Q ⊆ Z) := (slice_shape m g Q).2
    ((sum_eq_sum_iff_of_le (fun Q (_ : Q ∈ Z.powerset) => (slice_shape m g Q).1)).mp eqS Q (mem_powerset.mpr qz))
  let V := Submodule.span F (C : Set G)
  have atQ (Q : Finset G) (qz : Q ⊆ Z) : ∃ t, (∀ i ∈ C, t + i ∈ D) ∧
      t + (∑ q ∈ Q, q) ∈ V ∧ ∀ S ∈ sliceWords D C Q, ∃ i ∈ C, sliceValue Q S = t + i := by
    obtain ⟨T, tc, eq⟩ := fullQ Q qz
    let t := sliceValue Q T
    have swap (i : G) : sliceValue Q (T ∆ {i}) = t + i := by
      dsimp [t, sliceValue]
      rw [sum_word, sum_singleton, add_right_comm]
    refine ⟨t, ?_, ?_, ?_⟩
    · intro i hi
      have mem : T ∆ {i} ∈ sliceWords D C Q := by rw [eq]; exact mem_image.mpr ⟨i, hi, rfl⟩
      exact swap i ▸ (mem_filter.mp mem).2.2
    · dsimp only [t, sliceValue]; rw [add_assoc, ZModModule.add_self, add_zero]
      exact circuit_span_sum tc
    · intro S hs
      rw [eq] at hs
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hs
      exact ⟨i, hi, swap i⟩
  apply centre_complement m g
  · intro x
    have fullH : Submodule.span F (H : Set G) = ⊤ := by
      have hi := ind.linearIndependent.span_eq_top_of_card_eq_finrank' (by
        simpa using (show H.card = Module.finrank F G by omega))
      simpa using hi
    obtain ⟨Q, qz, hx⟩ := outside_coordinates (erase_subset p C) fullH x
    obtain ⟨t, ht, hv, _⟩ := atQ Q qz
    refine ⟨t, ht, ?_⟩
    have v := V.add_mem hx hv
    rw [add_add_add_comm, ZModModule.add_self, add_zero] at v
    exact v
  · intro x hx
    obtain ⟨Q, qin, v⟩ := mem_biUnion.mp (cover hx)
    obtain ⟨S, hs, rep⟩ := mem_image.mp v
    obtain ⟨t, ht, _, all⟩ := atQ Q (mem_powerset.mp qin)
    obtain ⟨i, hi, eq⟩ := all S hs
    exact ⟨t, ht, i, hi, rep.symm.trans eq⟩

private theorem strict_scale {g k : ℕ} (hg : 2 ≤ g) (lt : g < k) :
    k < g * 2 ^ (k - g) := by
  obtain ⟨d, eq⟩ := Nat.exists_eq_add_of_le (show g + 1 ≤ k by omega)
  subst k
  have diff : g + 1 + d - g = 1 + d := by omega
  rw [diff]
  induction d with
  | zero => simp; omega
  | succ d ih =>
    rw [Nat.add_succ 1 d, pow_succ, ←Nat.mul_assoc]
    omega

/-- All sets attaining Geelen's bound are pullbacks of a spanning odd circuit. -/
theorem geelen_equality (D : Finset G) (g : ℕ) (hg : 5 ≤ g)
    (short : ∀ R ⊆ D, Odd R.card → (∑ a ∈ R, a) = 0 → g ≤ R.card)
    (nonaffine : ¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x = 1)
    (large : g * 2 ^ (Module.finrank F G + 1 - g) ≤ D.card) :
    ∃ C, ShortestOddCircuit D C ∧ C.card = g ∧ ∃ P : Submodule F G,
      IsCompl P (Submodule.span F (C : Set G)) ∧
      ∀ x, x ∈ D ↔ ∃ t ∈ P, ∃ i ∈ C, x = t + i := by
  classical
  rcases choose_circuit D with affine | ⟨C, m⟩
  · exact (nonaffine affine).elim
  have minSize := short C m.1 m.2.1 m.2.2.1
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < C.card by omega)
  obtain ⟨H, sub, _, _, rank, _⟩ := coordinates m hp
  have le := (card_le_card sub).trans rank
  rw [card_erase_of_mem hp] at le
  have top := geelen_bound D C.card (by omega) m.2.2.2 nonaffine
  have size : C.card = g := by
    by_contra ne
    have less := strict_scale (by omega : 2 ≤ g) (show g < C.card by omega)
    have exps : C.card - g + (Module.finrank F G + 1 - C.card) = Module.finrank F G + 1 - g := by omega
    have dep := Nat.mul_lt_mul_of_pos_right less (by positivity : 0 < 2 ^ (Module.finrank F G + 1 - C.card))
    rw [Nat.mul_assoc, ←pow_add, exps] at dep
    exact (not_lt_of_ge (large.trans top)) dep
  refine ⟨C, m, size, circuit_equality m (by omega) ?_⟩
  rwa [size]

open Green51Hyperplane

omit [Fintype G] in
/-- An odd circuit has rank one below its size. -/
theorem circuit_rank {C D : Finset G} (m : ShortestOddCircuit D C) :
    Module.finrank F (Submodule.span F (C : Set G)) + 1 = C.card := by
  classical
  have odd := m.2.1
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < C.card by rw [Nat.odd_iff] at odd; omega)
  let B := C.erase p
  have bp : (∑ x ∈ B, x) = p := by
    simpa [B, sdiff_singleton_eq_erase] using circuit_complement_sum (singleton_subset_iff.mpr hp) m.2.2.1
  have span : Submodule.span F (C : Set G) = Submodule.span F (B : Set G) := by
    apply le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono (erase_subset p C))
    intro x hx
    change x ∈ Submodule.span F (B : Set G)
    by_cases h : x = p
    · have v := circuit_span_sum (Subset.rfl : B ⊆ B)
      rw [bp] at v
      exact h.symm ▸ v
    · exact Submodule.subset_span (mem_erase.mpr ⟨h, hx⟩)
  rw [span, finrank_span_finset_eq_card (independent_erase m hp), card_erase_of_mem hp]
  rw [Nat.odd_iff] at odd; omega

omit [Fintype G] in
/-- Two binary linear coordinates separate every direction in an extremal configuration from zero. -/
theorem extremal_coordinates {C D : Finset G} (m : ShortestOddCircuit D C) (g : 5 ≤ C.card)
    {P : Submodule F G} (compl : IsCompl P (Submodule.span F (C : Set G)))
    (full : ∀ x, x ∈ D ↔ ∃ t ∈ P, ∃ i ∈ C, x = t + i) :
    ∃ f : G →ₗ[F] F × F, ∀ x ∈ D, f x ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < C.card by omega)
  have er := card_erase_of_mem hp
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < (C.erase p).card by omega)
  have er2 := card_erase_of_mem hi
  obtain ⟨j, hj⟩ := card_pos.mp (show 0 < ((C.erase p).erase i).card by omega)
  obtain ⟨ji, jmem⟩ := mem_erase.mp hj
  have ind := independent_erase m hp
  obtain ⟨f, fi, _⟩ := coordinate_colour m hp (Subset.rfl : C.erase p ⊆ C.erase p) ind hi
  obtain ⟨h, hj, _⟩ := coordinate_colour m hp (Subset.rfl : C.erase p ⊆ C.erase p) ind jmem
  let V := Submodule.span F (C : Set G)
  let proj : G →ₗ[F] G := V.subtype.comp (V.projectionOnto P compl.symm)
  refine ⟨(f.prod h).comp proj, ?_⟩
  intro x hx
  obtain ⟨t, ht, a, ha, rfl⟩ := (full x).mp hx
  have ad : a ∈ V := Submodule.subset_span ha
  have t0 : proj t = 0 := by
    change ((V.projectionOnto P compl.symm t : V) : G) = 0
    rw [Submodule.projectionOnto_apply_of_mem_right compl.symm ht]; rfl
  have a0 : proj a = a := by
    change ((V.projectionOnto P compl.symm a : V) : G) = a
    rw [Submodule.projectionOnto_apply_of_mem_left compl.symm ad]
  change (f (proj (t + a)), h (proj (t + a))) ≠ 0
  rw [map_add, t0, a0, zero_add]
  intro eq
  by_cases ai : a = i
  · have z : h a = 0 := congrArg Prod.snd eq
    rw [hj a ha (by exact ai ▸ Ne.symm ji)] at z
    exact one_ne_zero z
  · have z : f a = 0 := congrArg Prod.fst eq
    exact one_ne_zero ((fi a ha ai).symm.trans z)

omit [Fintype G] in
/-- The complementary subspace is the full translation stabilizer of the extremal directions. -/
theorem periods_iff {C D : Finset G} (m : ShortestOddCircuit D C) (g : 5 ≤ C.card)
    {P : Submodule F G} (compl : IsCompl P (Submodule.span F (C : Set G)))
    (full : ∀ x, x ∈ D ↔ ∃ t ∈ P, ∃ i ∈ C, x = t + i) (t : G) :
    t ∈ P ↔ ∀ x ∈ D, x + t ∈ D := by
  classical
  constructor
  · rintro ht x hx
    obtain ⟨p, hp, i, hi, rfl⟩ := (full x).mp hx
    exact (full _).mpr ⟨p + t, P.add_mem hp ht, i, hi, add_right_comm p i t⟩
  · intro stable
    let V := Submodule.span F (C : Set G)
    have mem : t ∈ P ⊔ V := by rw [show P ⊔ V = ⊤ from compl.sup_eq_top]; trivial
    obtain ⟨p, hp, v, hv, eq⟩ := Submodule.mem_sup.mp mem
    have tc (i) (hi : i ∈ C) : t + i ∈ D := by simpa [add_comm] using stable i (m.1 hi)
    have pc (i) (hi : i ∈ C) : p + i ∈ D := (full _).mpr ⟨p, hp, i, hi, rfl⟩
    have zc (i) (hi : i ∈ C) : 0 + i ∈ D := by simpa using m.1 hi
    have diff : t + p + 0 ∈ V := by rw [←eq, add_zero, add_right_comm, ZModModule.add_self, zero_add]; exact hv
    have zero := centres_compatible m g tc pc zc diff
    rw [add_zero, ←eq, add_right_comm, ZModModule.add_self, zero_add] at zero
    simpa [←eq, zero] using hp

end Green51GirthFrame

#print axioms Green51GirthFrame.circuit_equality
#print axioms Green51GirthFrame.geelen_equality
#print axioms Green51GirthFrame.circuit_rank
#print axioms Green51GirthFrame.extremal_coordinates
#print axioms Green51GirthFrame.periods_iff
