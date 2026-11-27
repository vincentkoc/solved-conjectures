import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.FieldTheory.Finite.Extension

/-!
# Witt's circle geometry

Projective images of a subfield line give a Steiner 3-design.
See Shiro Iwasaki, *Translations of the squares in a finite field and related
designs with linear fractional groups*, §1, Example 3.
-/

namespace Erdos722.Sublines

open Matrix OnePoint Finset

variable {K : Type*} [Field K] [DecidableEq K]

private theorem move_to_infty (x : OnePoint K) :
    ∃ g : GL (Fin 2) K, g • x = ∞ := by
  cases x with
  | infty => exact ⟨1, one_smul _ _⟩
  | coe a =>
    let M : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, -a]
    have hu : M.det ≠ 0 := by simp [M, det_fin_two]
    refine ⟨GeneralLinearGroup.mkOfDetNeZero M hu, ?_⟩
    simp [smul_some_eq_ite, M]

/-- A projectivity carries the standard ordered frame to any ordered triple
of distinct points, over an arbitrary field. -/
theorem exists_frame {a b c : OnePoint K} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g : GL (Fin 2) K, g • (∞ : OnePoint K) = a ∧
      g • ((0 : K) : OnePoint K) = b ∧ g • ((1 : K) : OnePoint K) = c := by
  obtain ⟨g, hg⟩ := move_to_infty a
  have finite {w : OnePoint K} (h : a ≠ w) : ∃ t : K, g • w = (t : OnePoint K) := by
    cases he : g • w with
    | infty => exact (h (MulAction.injective g (hg.trans he.symm))).elim
    | coe t => exact ⟨t, rfl⟩
  obtain ⟨s, hs⟩ := finite hab
  obtain ⟨t, ht⟩ := finite hac
  have hts : t - s ≠ 0 := sub_ne_zero.mpr (fun e ↦
    hbc (MulAction.injective g (hs.trans ((congrArg OnePoint.some e.symm).trans ht.symm))))
  let M : Matrix (Fin 2) (Fin 2) K := !![t - s, s; 0, 1]
  let u := GeneralLinearGroup.mkOfDetNeZero M (by simpa [M, det_fin_two] using hts)
  refine ⟨g⁻¹ * u, ?_, ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff, hg]
    simp [u, M, smul_infty_eq_ite]
  · rw [mul_smul, inv_smul_eq_iff, hs]
    simp [u, M, smul_some_eq_ite]
  · rw [mul_smul, inv_smul_eq_iff, ht]
    simp [u, M, smul_some_eq_ite]

private theorem fixes_frame {g : GL (Fin 2) K}
    (hi : g • (∞ : OnePoint K) = ∞) (hz : g • ((0 : K) : OnePoint K) = ((0 : K) : OnePoint K))
    (ho : g • ((1 : K) : OnePoint K) = ((1 : K) : OnePoint K)) (x : OnePoint K) : g • x = x := by
  have hc := smul_infty_eq_self_iff.mp hi
  have hd : g 1 1 ≠ 0 := fun h ↦ g.det_ne_zero (by simp [det_fin_two, hc, h])
  have hb : g 0 1 = 0 := by
    simpa [smul_some_eq_ite, hc, hd, OnePoint.coe_eq_coe, div_eq_zero_iff] using hz
  have ha : g 0 0 = g 1 1 := by
    simpa [smul_some_eq_ite, hc, hd, hb, OnePoint.coe_eq_coe, div_eq_one_iff_eq hd] using ho
  cases x with
  | infty => exact hi
  | coe x => simp [smul_some_eq_ite, hc, hd, hb, ha, mul_div_cancel_left₀]

private theorem same_action {g h : GL (Fin 2) K}
    (hi : g • (∞ : OnePoint K) = h • ∞)
    (hz : g • ((0 : K) : OnePoint K) = h • ((0 : K) : OnePoint K))
    (ho : g • ((1 : K) : OnePoint K) = h • ((1 : K) : OnePoint K))
    (x : OnePoint K) : g • x = h • x := by
  have fix {w : OnePoint K} (hw : g • w = h • w) : (h⁻¹ * g) • w = w := by
    simp [mul_smul, hw]
  simpa only [mul_smul, inv_smul_eq_iff] using fixes_frame (fix hi) (fix hz) (fix ho) x

variable {F V : Type*} [Field F] [Fintype F]

/-- A projective image of the embedded subfield line, transported to labelled points. -/
noncomputable def subline (f : F →+* K) (label : V ≃ OnePoint K) (g : GL (Fin 2) K) :
    Finset V := by
  classical
  exact univ.image (fun t : OnePoint F ↦ label.symm (g • t.map f))

private theorem mem_subline (f : F →+* K) (label : V ≃ OnePoint K) (g : GL (Fin 2) K) (v : V) :
    v ∈ subline f label g ↔ ∃ t : OnePoint F, g • t.map f = label v := by
  classical
  simp [subline, Equiv.symm_apply_eq]

private theorem card_subline (f : F →+* K) (label : V ≃ OnePoint K) (g : GL (Fin 2) K) :
    (subline f label g).card = Fintype.card F + 1 := by
  classical
  have hi : Function.Injective (OnePoint.map (f : F → K)) := by
    intro x y
    cases x <;> cases y <;> simp [f.injective.eq_iff]
  have inj : Function.Injective (fun t : OnePoint F ↦ label.symm (g • t.map f)) :=
    label.symm.injective.comp ((MulAction.injective g).comp hi)
  rw [subline, card_image_of_injective _ inj, card_univ]
  exact Fintype.card_option

variable [DecidableEq F]

/-- A change of coordinates over the small field preserves its subline. -/
private theorem reparametrize (f : F →+* K) (label : V ≃ OnePoint K)
    (g : GL (Fin 2) K) (u : GL (Fin 2) F) :
    subline f label (g * u.map f) = subline f label g := by
  ext v
  simp only [mem_subline, mul_smul, ← OnePoint.map_smul]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨u • t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨u⁻¹ • t, by simpa using ht⟩

private theorem subline_through (f : F →+* K) (label : V ≃ OnePoint K)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {g : GL (Fin 2) K} (hi : g • (∞ : OnePoint K) = label a)
    (hz : g • ((0 : K) : OnePoint K) = label b)
    (ho : g • ((1 : K) : OnePoint K) = label c)
    (h : GL (Fin 2) K) (ha : a ∈ subline f label h) (hb : b ∈ subline f label h)
    (hc : c ∈ subline f label h) : subline f label h = subline f label g := by
  obtain ⟨x, hx⟩ := (mem_subline _ _ _ _).mp ha
  obtain ⟨y, hy⟩ := (mem_subline _ _ _ _).mp hb
  obtain ⟨z, hh⟩ := (mem_subline _ _ _ _).mp hc
  have neq {i j : OnePoint F} {v w : V} (hn : v ≠ w)
      (hv : h • i.map f = label v) (hw : h • j.map f = label w) : i ≠ j := by
    rintro rfl
    exact hn (label.injective (hv.symm.trans hw))
  obtain ⟨u, ui, uz, uo⟩ := exists_frame (neq hab hx hy) (neq hac hx hh) (neq hbc hy hh)
  have comp (t : OnePoint F) : (h * u.map f) • t.map f = h • (u • t).map f := by
    rw [mul_smul, OnePoint.map_smul]
  have eqv : ∀ t : OnePoint K, (h * u.map f) • t = g • t := by
    apply same_action
    · simpa [ui] using (comp ∞).trans (by rw [ui, hx, hi])
    · simpa using (comp ((0 : F) : OnePoint F)).trans (by rw [uz, hy, hz])
    · simpa using (comp ((1 : F) : OnePoint F)).trans (by rw [uo, hh, ho])
  rw [← reparametrize f label h u]
  ext v
  simp only [mem_subline, eqv]

/-- All projective images of the small field's line. -/
noncomputable def blocks [Fintype V] (f : F →+* K) (label : V ≃ OnePoint K) :
    Finset (Finset V) := by
  classical
  exact univ.filter (fun B ↦ ∃ g : GL (Fin 2) K, B = subline f label g)

/-- Any field embedding gives the upstream Steiner incidence predicate on
the finite labelled projective line over the larger field. -/
theorem blocks_isBlockDesign [Fintype V] (f : F →+* K) (label : V ≃ OnePoint K) :
    (blocks f label).IsBlockDesign 3 (Fintype.card F + 1) := by
  classical
  have memB (B : Finset V) : B ∈ blocks f label ↔ ∃ g, B = subline f label g := by simp [blocks]
  refine ⟨?_, ?_⟩
  · intro B hB
    obtain ⟨g, rfl⟩ := (memB B).mp hB
    exact card_subline f label g
  · intro S hS
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hS
    obtain ⟨g, hi, hz, ho⟩ := exists_frame
      (label.injective.ne hab) (label.injective.ne hac) (label.injective.ne hbc)
    refine ⟨subline f label g, ⟨(memB _).mpr ⟨g, rfl⟩, ?_⟩, ?_⟩
    · simp only [insert_subset_iff, singleton_subset_iff, mem_subline]
      exact ⟨⟨∞, by simpa using hi⟩, ⟨((0 : F) : OnePoint F), by simpa using hz⟩,
        ⟨((1 : F) : OnePoint F), by simpa using ho⟩⟩
    · rintro B ⟨hB, hs⟩
      obtain ⟨h, rfl⟩ := (memB B).mp hB
      simp only [insert_subset_iff, singleton_subset_iff] at hs
      exact subline_through f label hab hac hbc hi hz ho h hs.1 hs.2.1 hs.2.2

/-- For q = p^e, the subline construction gives Steiner designs on q^d+1
points with blocks of size q+1 for every positive extension degree d. -/
theorem exists_prime_power_subline_design (p e d : ℕ) [Fact p.Prime] (he : 0 < e) (hd : 0 < d) :
    ∃ H : Finset (Finset (Fin ((p ^ e) ^ d + 1))), H.IsBlockDesign 3 (p ^ e + 1) := by
  classical
  let F := GaloisField p e
  let : NeZero d := ⟨hd.ne'⟩
  let K := FiniteField.Extension F p d
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hF : Nat.card F = p ^ e := GaloisField.card p e he.ne'
  have hK : Nat.card K = (p ^ e) ^ d := (FiniteField.natCard_extension F p d).trans (by rw [hF])
  have hpt : Fintype.card (OnePoint K) = (p ^ e) ^ d + 1 := by
    change Fintype.card (Option K) = _
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card, hK]
  let label := (Fintype.equivFinOfCardEq hpt).symm
  refine ⟨blocks (algebraMap F K) label, ?_⟩
  simpa only [← Nat.card_eq_fintype_card, hF] using blocks_isBlockDesign (algebraMap F K) label

/-- For each fixed prime-power block parameter, the constructed orders are
cofinal. This is the frequent-order version of the upstream conclusion. -/
theorem frequently_prime_power_subline_design (p e : ℕ) [Fact p.Prime] (he : 0 < e) :
    ∃ᶠ n : ℕ in Filter.atTop, ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 (p ^ e + 1) := by
  apply Filter.frequently_atTop.mpr
  intro N
  have hq := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  have hg := Nat.lt_pow_self (n := N + 1) hq
  exact ⟨(p ^ e) ^ (N + 1) + 1, by omega, exists_prime_power_subline_design p e _ he (by omega)⟩

#print axioms exists_frame
#print axioms blocks_isBlockDesign
#print axioms exists_prime_power_subline_design
#print axioms frequently_prime_power_subline_design

end Erdos722.Sublines
