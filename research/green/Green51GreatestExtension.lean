import Green51RichSliceSections

/-! # The greatest extension preserving odd girth -/

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

/-- The range of the section complements the circuit span and contains all admissible fibres after translation. -/
theorem universal_circuit_container {D C : Finset G} (m : ShortestOddCircuit D C) (g : 5 ≤ C.card)
    (near : min (5 * C.card + 12) (4 * C.card + 20) * 2 ^ (Module.finrank F G + 1 - C.card) < 8 * D.card) :
    ∃ P : Submodule F G, IsCompl P (Submodule.span F (C : Set G)) ∧
      ∀ E : Finset G, D ⊆ E → ShortestOddCircuit E C → ∀ x ∈ E, ∃ t ∈ P, ∃ i ∈ C, x = t + i := by
  classical
  let V := Submodule.span F (C : Set G)
  let _ : Fintype (G ⧸ V) := Fintype.ofFinite _
  have rank := V.finrank_quotient_add_finrank
  have rc := circuit_rank m
  change Module.finrank F V + 1 = C.card at rc
  have order : Fintype.card (G ⧸ V) = 2 ^ (Module.finrank F G + 1 - C.card) := by
    rw [Module.card_eq_pow_finrank (K := F)]
    have dim : Module.finrank F (G ⧸ V) = Module.finrank F G + 1 - C.card := by omega
    simp [F, dim]
  obtain ⟨L, section_eq, dirs⟩ := dense_universal_projection m g V.mkQ V.mkQ_surjective (Submodule.ker_mkQ V) (by
    rw [order]
    by_cases h : 5*C.card+12 ≤ 4*C.card+20
    · exact Or.inl (by rwa [min_eq_left h] at near)
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h))] at near
      refine Or.inr ⟨by omega, ?_⟩
      nlinarith only [near])
  have lift (u : G ⧸ V) : V.mkQ (L u) = u := LinearMap.congr_fun section_eq u
  refine ⟨L.range, ⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hv
    obtain ⟨u, rfl⟩ := hx
    have zero : V.mkQ (L u) = 0 := LinearMap.mem_ker.mp ((Submodule.ker_mkQ V).symm ▸ hv)
    rw [lift] at zero
    rw [zero, map_zero]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    let p := L (V.mkQ x)
    have v : x + p ∈ V := by
      rw [←Submodule.ker_mkQ V, LinearMap.mem_ker, map_add, show V.mkQ p = V.mkQ x from lift _, ZModModule.add_self]
    exact Submodule.mem_sup.mpr ⟨p, ⟨_, rfl⟩, x + p, v, by rw [add_left_comm, ZModModule.add_self, add_zero]⟩
  · intro E incl me x hx
    obtain ⟨i, hi, eq⟩ := dirs E incl me x hx
    exact ⟨L (V.mkQ x), ⟨_, rfl⟩, i, hi, eq⟩

end Green51GirthFrame
#print axioms Green51GirthFrame.universal_circuit_container

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

/-- Taking all cosets of the circuit by a complementary subspace preserves its odd girth and gives the sharp size. -/
theorem container_size_girth {D C : Finset G} (m : ShortestOddCircuit D C) (P : Submodule F G)
    (compl : IsCompl P (Submodule.span F (C : Set G))) :
    let U := (P : Set G).toFinset + C
    ShortestOddCircuit U C ∧ U.card = C.card * 2 ^ (Module.finrank F G + 1 - C.card) := by
  classical
  let V := Submodule.span F (C : Set G)
  let proj : G →ₗ[F] G := V.subtype.comp (V.projectionOnto P compl.symm)
  have parts {t i : G} (ht : t ∈ P) (hi : i ∈ C) : proj (t + i) = i := by
    change ((V.projectionOnto P compl.symm (t + i) : V) : G) = i
    rw [map_add, Submodule.projectionOnto_apply_of_mem_right compl.symm ht,
      Submodule.projectionOnto_apply_of_mem_left compl.symm (show i ∈ V from Submodule.subset_span hi), zero_add]
  let U := (P : Set G).toFinset + C
  have maps {x : G} (hx : x ∈ U) : proj x ∈ C := by
    obtain ⟨t, ht, i, hi, rfl⟩ := mem_add.mp hx
    rwa [parts (Set.mem_toFinset.mp ht) hi]
  refine ⟨⟨fun i hi => mem_add.mpr ⟨0, Set.mem_toFinset.mpr P.zero_mem, i, hi, zero_add _⟩,
    m.2.1, m.2.2.1, ?_⟩, ?_⟩
  · intro R sub odd total
    by_contra! small
    obtain ⟨i, hi, missing⟩ := exists_mem_notMem_of_card_lt_card (show (R.image proj).card < C.card from card_image_le.trans_lt small)
    obtain ⟨f, ones⟩ := extend_values (independent_erase m hi) (fun _ => (1 : F))
    have onR (x : G) (hx : x ∈ R) : f (proj x) = 1 :=
      ones _ (show proj x ∈ C.erase i from mem_erase.mpr ⟨fun eq => missing (eq ▸ mem_image_of_mem proj hx), maps (sub hx)⟩)
    have val := congrArg (f.comp proj) total
    rw [map_sum, map_zero] at val
    change ∑ x ∈ R, f (proj x) = 0 at val
    rw [sum_eq_card_nsmul onR, nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff] at val
    rw [Nat.odd_iff] at odd
    change 2 ∣ R.card at val
    omega
  · have mult : U.card = (P : Set G).toFinset.card * C.card := by
      apply Finset.card_add_iff.mpr
      rintro ⟨x,i⟩ ⟨hx,hi⟩ ⟨y,j⟩ ⟨hy,hj⟩ eq
      change x+i = y+j at eq
      have same := congrArg proj eq
      rw [parts (Set.mem_toFinset.mp hx) hi, parts (Set.mem_toFinset.mp hy) hj] at same
      change i = j at same
      subst j
      exact Prod.ext (add_right_cancel eq) rfl
    have rP := Submodule.finrank_add_eq_of_isCompl compl
    have rC := circuit_rank m
    have pc : (P : Set G).toFinset.card = 2 ^ (Module.finrank F G + 1 - C.card) := by
      have dim : Module.finrank F P = Module.finrank F G + 1 - C.card := by omega
      have ord := Module.card_eq_pow_finrank (K := F) (V := P)
      simpa [F, dim] using ord
    rw [mult, pc, Nat.mul_comm]

end Green51GirthFrame
#print axioms Green51GirthFrame.container_size_girth

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

/-- A nonaffine set in the stability range has a circuit at the prescribed lower bound for its odd girth. -/
theorem shortest_at_bound (D : Finset G) (g : ℕ) (hg : 5 ≤ g) (odd : Odd g)
    (short : ∀ R ⊆ D, Odd R.card → (∑ i ∈ R, i) = 0 → g ≤ R.card)
    (no : ¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x = 1)
    (near : min (5 * g + 12) (4 * g + 20) * 2 ^ (Module.finrank F G + 1 - g) < 8 * D.card) :
    ∃ C, ShortestOddCircuit D C ∧ C.card = g := by
  obtain ⟨C, m⟩ := (choose_circuit D).resolve_left no
  have le := short C m.1 m.2.1 m.2.2.1
  have same : C.card = g := by
    by_contra bigger
    have oc := m.2.1
    have next : g + 2 ≤ C.card := by rw [Nat.odd_iff] at odd oc; omega
    have rc := circuit_rank m
    have rv := Submodule.finrank_le (Submodule.span F (C : Set G))
    have upper := geelen_bound D (g + 2) (by omega) (fun R sub par sum => next.trans (m.2.2.2 R sub par sum)) no
    let e := Module.finrank F G + 1 - (g + 2)
    have shift : Module.finrank F G + 1 - g = e + 2 := by dsimp [e]; omega
    rw [shift, pow_add] at near
    change D.card ≤ (g + 2) * 2 ^ e at upper
    have pos : 0 < 2 ^ e := Nat.pow_pos (by decide)
    have low : 2*g+5 ≤ min (5*g+12) (4*g+20) := le_min (by omega) (by omega)
    have prod := Nat.mul_le_mul_right (2^e) low
    rw [show (2:ℕ)^2 = 4 by decide] at near
    nlinarith only [upper, near, prod, pos]
  exact ⟨C, m, same⟩


/-- All supersets preserving the odd girth lie inside one greatest such superset, of extremal cardinality. -/
theorem greatest_girth_extension (D : Finset G) (g : ℕ) (hg : 5 ≤ g) (odd : Odd g)
    (short : ∀ R ⊆ D, Odd R.card → (∑ x ∈ R, x) = 0 → g ≤ R.card)
    (no : ¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x = 1)
    (near : min (5 * g + 12) (4 * g + 20) * 2 ^ (Module.finrank F G + 1 - g) < 8 * D.card) :
    ∃ C, ShortestOddCircuit D C ∧ C.card = g ∧ ∃ P : Submodule F G,
      IsCompl P (Submodule.span F (C : Set G)) ∧
      let U := (P : Set G).toFinset + C
      IsGreatest {E : Finset G | D ⊆ E ∧ ∀ R ⊆ E, Odd R.card → (∑ x ∈ R, x) = 0 → g ≤ R.card} U ∧
      U.card = g * 2 ^ (Module.finrank F G + 1 - g) := by
  obtain ⟨C, m, eq⟩ := shortest_at_bound D g hg odd short no near
  subst g
  obtain ⟨P, compl, contains⟩ := universal_circuit_container m hg near
  have bound {E : Finset G} (incl : D ⊆ E) (me : ShortestOddCircuit E C) :
      E ⊆ (P : Set G).toFinset + C := by
    intro x hx
    obtain ⟨t, ht, i, hi, val⟩ := contains E incl me x hx
    exact mem_add.mpr ⟨t, Set.mem_toFinset.mpr ht, i, hi, val.symm⟩
  obtain ⟨mU, card⟩ := container_size_girth m P compl
  exact ⟨C, m, rfl, P, compl, ⟨⟨bound Subset.rfl m, mU.2.2.2⟩,
    fun E h => bound h.1 ⟨m.1.trans h.1, m.2.1, m.2.2.1, h.2⟩⟩, card⟩

end Green51GirthFrame
#print axioms Green51GirthFrame.shortest_at_bound
#print axioms Green51GirthFrame.greatest_girth_extension
