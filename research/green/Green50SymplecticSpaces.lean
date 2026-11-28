import Mathlib

/-! # Dimension of an affine space of symplectic forms over a finite field

A double count picks a hyperplane on which the kernel of evaluation descends faithfully.
Induction removes one symplectic plane at a time.
-/

open Finset
namespace Green50SymplecticSpaces
private theorem incoming_vertex {V : Type*} [Fintype V] [DecidableEq V] [Zero V]
    (R : V → V → Prop) [DecidableRel R] (m : ℕ)
    (hne : (univ.erase (0 : V)).Nonempty)
    (h : ∀ v ∈ univ.erase (0 : V), m ≤ ((univ.erase 0).filter (R v)).card) :
    ∃ x ∈ univ.erase (0 : V), m ≤ ((univ.erase 0).filter (fun v => R v x)).card := by
  by_contra! hn
  exact (lt_irrefl _) (Finset.card_nsmul_lt_card_nsmul_of_le_of_lt (R := ℕ) R hne h hn)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
local notation "Form" => LinearMap.BilinForm K V

private def evaluate (T : Submodule K Form) (v : V) : T →ₗ[K] Module.Dual K V :=
  (LinearMap.applyₗ (R := K) (M₂ := Module.Dual K V) v).comp T.subtype

private theorem partner {J : Form} {T : Submodule K Form}
    (h : ∀ A ∈ T, Function.Injective (J + A)) {v : V} (hv : v ≠ 0) :
    ∃ y : V, J v y = 1 ∧ ∀ A ∈ T, A v y = 0 := by
  have hout : J v ∉ (evaluate T v).range := by
    rintro ⟨⟨A, hA⟩,he⟩
    change A v = J v at he
    apply hv
    have hinj := h ((-1 : K) • A) (T.smul_mem _ hA)
    apply hinj
    ext w
    simp [← he]
  obtain ⟨d, hd, hker⟩ := Submodule.exists_le_ker_of_notMem hout
  let z := (Module.evalEquiv K V).symm d
  have hz (f : Module.Dual K V) : f z = d f := Module.apply_evalEquiv_symm_apply K V f d
  refine ⟨(d (J v))⁻¹ • z, ?_, ?_⟩
  · simp [hz, hd]
  · intro A hA
    have hzero : d (A v) = 0 := hker (show A v ∈ (evaluate T v).range from ⟨⟨A, hA⟩, rfl⟩)
    simp [hz, hzero]

private def planeMap (J : Form) (x z : V) := (J x).prod (J z)

omit [FiniteDimensional K V] in
private theorem plane_surj (J : Form) (ha : J.IsAlt) {x z : V} (hz : J x z = 1) :
    Function.Surjective (planeMap J x z) := by
  rintro ⟨a, b⟩
  refine ⟨a • z - b • x, Prod.ext ?_ ?_⟩ <;>
    simp [planeMap, ha.self_eq_zero, hz, ← ha.neg_eq x z]

private theorem fibre_card [DecidableEq K] [Fintype K] [Fintype V] [DecidableEq V] (J : Form)
    (ha : J.IsAlt) (v y : V) (hvy : J v y = 1) :
    ((univ.erase 0).filter (fun x : V => J v x = 0 ∧ J y x = 1)).card =
      Fintype.card K ^ (Module.finrank K V - 2) := by
  classical
  let e := planeMap J v y
  have hsur := plane_surj J ha hvy
  have eqfilter : ((univ.erase 0).filter (fun x : V => J v x = 0 ∧ J y x = 1)) =
      univ.filter (fun x => e x = (0, 1)) := by
    ext x
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and]
    change (x ≠ 0 ∧ (J v x = 0 ∧ J y x = 1)) ↔ (J v x, J y x) = (0, 1)
    rw [Prod.mk.injEq]
    constructor
    · exact And.right
    · intro h; exact ⟨fun hx => by simpa [hx] using h.2, h⟩
  rw [eqfilter, AddMonoidHom.card_fiber_eq_of_mem_range e (hsur (0, 1)) (hsur 0)]
  have hk : Fintype.card e.ker = (univ.filter (fun x => e x = 0)).card := by
    exact Fintype.card_of_subtype _ (by simp)
  rw [← hk, Module.card_eq_pow_finrank (K := K)]
  congr 1
  have hr := e.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsur, finrank_top, Module.finrank_prod,
    Module.finrank_self] at hr
  omega
private theorem spanning_section [Fintype K] [Fintype V] (J : Form) (ha : J.IsAlt)
    {T : Submodule K Form} (h : ∀ A ∈ T, Function.Injective (J + A))
    (hdim : 2 ≤ Module.finrank K V) :
    ∃ x : V, x ≠ 0 ∧ ∃ S : Set V, Submodule.span K S = (J x).ker ∧
      ∀ v ∈ S, ∃ y, J y x = 1 ∧ ∀ A ∈ T, A v y = 0 := by
  classical
  have hex (v : V) : ∃ y, v ≠ 0 → J v y = 1 ∧ ∀ A ∈ T, A v y = 0 := by
    by_cases hv : v = 0
    · exact ⟨0, fun hn => (hn hv).elim⟩
    · obtain ⟨y, hy⟩ := partner h hv
      exact ⟨y, fun _ => hy⟩
  choose y hy using hex
  let R (v x : V) : Prop := J v x = 0 ∧ J (y v) x = 1
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K V)
  have hne : (univ.erase (0 : V)).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨v, mem_erase.mpr ⟨hv, mem_univ _⟩⟩
  obtain ⟨x, hx, hsize⟩ := incoming_vertex R (Fintype.card K ^ (Module.finrank K V - 2)) hne
    (fun v hv => (fibre_card J ha v (y v) (hy v (mem_erase.mp hv).1).1).ge)
  let S := (univ.erase (0 : V)).filter (fun v => R v x)
  let P := Submodule.span K (S : Set V)
  have hH : P ≤ (J x).ker := by
    refine Submodule.span_le.mpr ?_
    intro v hv
    have he := (mem_filter.mp (show v ∈ S from hv)).2.1
    change J x v = 0
    rw [← ha.neg_eq v x, he, neg_zero]
  have hJ : Function.Injective J := by simpa using h 0 T.zero_mem
  have hf : J x ≠ 0 := fun eq => (mem_erase.mp hx).1 (hJ (eq.trans (map_zero J).symm))
  have hr := (J x).finrank_range_add_finrank_ker
  have htop : (J x).range = ⊤ := LinearMap.range_eq_top.mpr (LinearMap.surjective_iff_ne_zero.mpr hf)
  rw [htop, finrank_top, Module.finrank_self] at hr
  have eq : P = (J x).ker := by
    by_contra hn
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hH hn)
    have hsmall : Module.finrank K P ≤ Module.finrank K V - 2 := by omega
    let allP := (P : Set V).toFinset
    have hinc : insert 0 S ⊆ allP := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact Set.mem_toFinset.mpr P.zero_mem
      · exact Set.mem_toFinset.mpr (Submodule.subset_span (show v ∈ (S : Set V) from hv))
    have h0 : 0 ∉ S := by simp [S]
    have hc := card_le_card hinc
    rw [card_insert_of_notMem h0] at hc
    have hpc : allP.card = Fintype.card P := (Fintype.card_of_subtype _ (by simp [allP])).symm
    rw [hpc, Module.card_eq_pow_finrank (K := K)] at hc
    have hpow := Nat.pow_le_pow_right (Fintype.card_pos (α := K)) hsmall
    change Fintype.card K ^ (Module.finrank K V - 2) ≤ S.card at hsize
    omega
  refine ⟨x, (mem_erase.mp hx).1, S, eq, ?_⟩
  intro v hv
  have hv' := mem_filter.mp (show v ∈ S from hv)
  exact ⟨y v, hv'.2.2, (hy v (mem_erase.mp hv'.1).1).2⟩
omit [FiniteDimensional K V] in
private theorem complement_decomp (J : Form) (ha : J.IsAlt) {x z : V} (hz : J x z = 1) (w : V) :
    ∃ u : (planeMap J x z).ker, w = u.val - (J z w) • x + (J x w) • z := by
  let u := w + (J z w) • x - (J x w) • z
  have hu : u ∈ (planeMap J x z).ker := by
    change (J x u, J z u) = (0, 0)
    simp [u, ha.self_eq_zero, hz, ← ha.neg_eq x z]
  exact ⟨⟨u, hu⟩, by dsimp [u]; abel⟩

private theorem complement_dim (J : Form) (ha : J.IsAlt) {x z : V} (hz : J x z = 1) :
    Module.finrank K (planeMap J x z).ker + 2 = Module.finrank K V := by
  have hr := (planeMap J x z).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (plane_surj J ha hz), finrank_top, Module.finrank_prod,
    Module.finrank_self] at hr
  omega

omit [FiniteDimensional K V] in
private theorem restrict_nondegenerate (J F : Form) (ha : J.IsAlt) (fa : F.IsAlt)
    (hf : Function.Injective F) {x z : V} (hz : J x z = 1) (hfx : F x = J x) :
    Function.Injective (F.restrict (planeMap J x z).ker) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hrad
  have hu (w : (planeMap J x z).ker) : F (u : V) (w : V) = 0 :=
    congrArg (fun f : Module.Dual K (planeMap J x z).ker => f w) hrad
  obtain ⟨hxu, hzu⟩ := Prod.mk.inj (show (J x u.val, J z u.val) = (0, 0) from u.property)
  have fxz : F x z = 1 := by rw [hfx, hz]
  let d := u.val - F u.val z • x
  have dx : F d x = 0 := by simp [d, ha.self_eq_zero, ← fa.neg_eq x u.val, hfx, hxu]
  have dz : F d z = 0 := by simp [d, fxz]
  have dw (w : (planeMap J x z).ker) : F d w.val = 0 := by
    have hxw : J x w.val = 0 := congrArg Prod.fst w.property
    simp [d, hu, hfx, hxw]
  have hd : d = 0 := by
    apply hf
    ext w
    obtain ⟨u',he⟩ := complement_decomp J ha hz w
    conv_lhs => rw [he]
    simp [dx, dz, dw]
  have hcoef := congrArg (J z) hd
  have cz : F u.val z = 0 := by
    simpa [d, hzu, ← ha.neg_eq x z, hz] using hcoef
  exact Subtype.ext (by simpa [d, cz] using hd)
private def restrictionMap (T : Submodule K Form) (x : V) (W : Submodule K V) :
    (evaluate T x).ker →ₗ[K] LinearMap.BilinForm K W where
  toFun A := A.val.val.restrict W
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional K V] in
private theorem restriction_injective {J : Form} (ha : J.IsAlt) {T : Submodule K Form}
    (hT : ∀ A ∈ T, A.IsAlt) {x z : V} (hz : J x z = 1) {S : Set V}
    (hspan : Submodule.span K S = (J x).ker)
    (hS : ∀ v ∈ S, ∃ y, J y x = 1 ∧ ∀ A ∈ T, A v y = 0) :
    Function.Injective (restrictionMap T x (planeMap J x z).ker) := by
  let : AddCommGroup (evaluate T x).ker := Module.addCommMonoidToAddCommGroup K
  have zero (A : (evaluate T x).ker) (hrest : restrictionMap T x (planeMap J x z).ker A = 0) : A = 0 := by
    let F : Form := A.val.val
    have hfx : F x = 0 := A.property
    have fa := hT F A.val.property
    have Horth (v w : V) (hv : J x v = 0) (hw : J x w = 0) : F v w = 0 := by
      obtain ⟨a, ea⟩ := complement_decomp J ha hz v
      obtain ⟨b, eb⟩ := complement_decomp J ha hz w
      have hab : F a.val b.val = 0 :=
        congrArg (fun G : LinearMap.BilinForm K (planeMap J x z).ker => G a b) hrest
      have hax : F a.val x = 0 := by rw [← fa.neg_eq, hfx]; simp
      calc
        F v w = F (a.val - (J z v) • x) (b.val - (J z w) • x) := by
          congr 2
          · simpa [hv] using ea
          · simpa [hw] using eb
        _ = 0 := by simp [hfx, hab, hax]
    have hrad : (J x).ker ≤ F.ker := by
      rw [← hspan, Submodule.span_le]
      intro v hv
      have hv0 : J x v = 0 := (hspan ▸ Submodule.subset_span hv : v ∈ (J x).ker)
      obtain ⟨y, hy, fy⟩ := hS v hv
      change F v = 0
      ext w
      have hy' : J x y = -1 := by rw [← ha.neg_eq, hy]
      have hw : J x (w + (J x w) • y) = 0 := by simp [hy']
      have e := Horth v _ hv0 hw
      simpa [fy F A.val.property] using e
    have hzker : F z = 0 := by
      ext w
      obtain ⟨b, eb⟩ := complement_decomp J ha hz w
      have bz : F b.val = 0 := hrad (show J x b.val = 0 from congrArg Prod.fst b.property)
      have zxb : F z x = 0 := by rw [← fa.neg_eq, hfx]; simp
      have zb : F z b.val = 0 := by rw [← fa.neg_eq, bz]; simp
      conv_lhs => rw [eb]
      simp [zb, zxb, fa.self_eq_zero]
    apply Subtype.ext
    apply Subtype.ext
    change F = 0
    ext w v
    obtain ⟨a, ea⟩ := complement_decomp J ha hz w
    have ar : F a.val = 0 := hrad (show J x a.val = 0 from congrArg Prod.fst a.property)
    conv_lhs => rw [ea]
    simp [ar, hfx, hzker]
  intro A B he
  apply sub_eq_zero.mp
  apply zero
  rw [map_sub, he, sub_self]
private theorem evaluation_cost (J : Form) (ha : J.IsAlt) {T : Submodule K Form}
    (hT : ∀ A ∈ T, A.IsAlt) {x z : V} (hz : J x z = 1) (hzT : ∀ A ∈ T, A x z = 0) :
    Module.finrank K (evaluate T x).range + 2 ≤ Module.finrank K V := by
  let d := (Module.Dual.eval K V x).prod (Module.Dual.eval K V z)
  have hd : Function.Surjective d := by
    rintro ⟨a, b⟩
    refine ⟨J (b • x - a • z), Prod.ext ?_ ?_⟩ <;>
      simp [d, Module.Dual.eval_apply, ha.self_eq_zero, hz, ← ha.neg_eq x z]
  have hs : (evaluate T x).range ≤ d.ker := by
    rintro _ ⟨⟨A, hA⟩,rfl⟩
    change (A x x, A x z) = (0, 0)
    rw [(hT A hA).self_eq_zero, hzT A hA]
  have hc := Submodule.finrank_mono hs
  have hr := d.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hd, finrank_top, Module.finrank_prod, Module.finrank_self,
    Subspace.dual_finrank_eq] at hr
  omega
universe u

/-- Over a finite field of any size, an affine space of symplectic forms in dimension
2k has dimension at most k(k−1). -/
theorem dimension_bound (K : Type*) [Field K] [Fintype K] (k : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (J : LinearMap.BilinForm K V) (T : Submodule K (LinearMap.BilinForm K V)),
      J.IsAlt → (∀ A ∈ T, A.IsAlt) → (∀ A ∈ T, Function.Injective (J + A)) →
      Module.finrank K V = 2 * k → Module.finrank K T ≤ k * (k - 1) := by
  induction k with
  | zero =>
    intro V _ _ _ J T _ _ _ hd
    have : Subsingleton V := Module.finrank_zero_iff.mp (by simpa using hd)
    have : Subsingleton (LinearMap.BilinForm K V) := inferInstance
    exact Nat.le_of_eq Module.finrank_zero_of_subsingleton
  | succ k ih =>
    intro V _ _ _ J T ha hT hgood hd
    classical
    let : Fintype V := Module.fintypeOfFintype (Module.finBasis K V)
    obtain ⟨x, hx, S,hs, hS⟩ := spanning_section J ha hgood (by omega)
    obtain ⟨z, hz, hzT⟩ := partner hgood hx
    let W := (planeMap J x z).ker
    let L := restrictionMap T x W
    have hW : Module.finrank K W = 2 * k := by
      have := complement_dim J ha hz
      dsimp [W]; omega
    have hralt : (J.restrict W).IsAlt := fun v => ha v.val
    have htalt : ∀ A ∈ L.range, A.IsAlt := by
      rintro _ ⟨A, rfl⟩ v
      exact hT _ A.val.property v.val
    have hrgood : ∀ A ∈ L.range, Function.Injective (J.restrict W + A) := by
      rintro _ ⟨A, rfl⟩
      have he : (J + A.val.val) x = J x := by
        change J x + A.val.val x = J x
        rw [show A.val.val x = 0 from A.property, add_zero]
      exact restrict_nondegenerate J (J + A.val.val) ha (ha.add (hT _ A.val.property))
        (hgood _ A.val.property) hz he
    have small := ih (J.restrict W) L.range hralt htalt hrgood hW
    have hdim := LinearMap.finrank_range_of_inj (restriction_injective ha hT hz hs hS)
    change Module.finrank K L.range = Module.finrank K (evaluate T x).ker at hdim
    have evaldim := evaluation_cost J ha hT hz hzT
    let : AddCommGroup T := Module.addCommMonoidToAddCommGroup K
    have rankdim := (evaluate T x).finrank_range_add_finrank_ker
    have budget : (k + 1) * (k + 1 - 1) = k * (k - 1) + 2 * k := by
      cases k with
      | zero => simp
      | succ k => simp; ring
    omega

end Green50SymplecticSpaces

#print axioms Green50SymplecticSpaces.dimension_bound
