import Green51GoldForms
import Green51BCHSubfieldFlats
import Green51TwoAlternating
import Green51LocalFlats

/-! # Two binary BCH coordinates in odd field degree -/

open Green50Downsets Green51BCH Green51BCHCompression Green51GoldForms
open scoped Pointwise
namespace Green51OddPencils
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
variable {H : Type*} [AddCommGroup H] [Module F H]

/-- When seventh powering is bijective, a common isotropic subspace can be scaled
into the absolute trace kernel without changing the two vanishing conditions. -/
theorem two_tests_in_odd (k : ℕ) (hk : 0 < k) (dim : Module.finrank F K = 2*k+1)
    (seven : (Nat.card Kˣ).Coprime 7) (L : K →ₗ[F] H) (rank : Module.finrank F L.range ≤ 2) :
    ∃ (p : Space K × H) (W : Submodule F (Space K × H)), Module.finrank F W = k+1 ∧
      p+ᵥ (W:Set _) ⊆ Set.range (lifted L) + Set.range (lifted L) := by
  obtain ⟨e,inj⟩ := finrank_le_iff_exists_linearMap.mp
    (show Module.finrank F L.range ≤ Module.finrank F (Cube 2) by simp [Cube];omega)
  let f := e.comp L.rangeRestrict
  let B (i : Fin 2) := bracketForm ((LinearMap.proj i).comp f) 1
  have alt (i : Fin 2) : (B i).IsAlt := fun x => by
    change f (1 * bracket x x) i = 0
    simp [bracket,CharTwo.add_self_eq_zero]
  obtain ⟨V,d,iso,iso'⟩ := Green51TwoAlternating.simultaneous F k (B 0) (B 1) (alt 0) (alt 1) dim
  have kill (x : K) (hx : x ∈ V) (y : K) (hy : y ∈ V) : L (bracket x y) = 0 := by
    have both (i : Fin 2) : B i x y=0 := by fin_cases i <;> first | exact iso x hx y hy | exact iso' x hx y hy
    have hz : f (bracket x y)=0 := funext (fun i => by simpa [B,bracketForm] using both i)
    exact congrArg Subtype.val ((e.map_eq_zero_iff inj).mp hz)
  obtain ⟨s,ns,sub⟩ := Green51BracketRank.scale_into_trace V.subtype (by omega)
  let u := (Units.mk0 s ns)^(-3:ℤ)
  obtain ⟨v,hv⟩ := (powCoprime seven).surjective u
  change v^7=u at hv
  have scale : (v:K)^7*s^3=1 := by
    change (v^7 : Kˣ).val*s^3=1
    rw [hv]
    simp [u,zpow_neg,ns]
  let g := LinearMap.mulLeft F s
  have embed : Function.Injective g := fun _ _ eq => mul_left_cancel₀ ns eq
  have rd := (V.equivMapOfInjective g embed).finrank_eq
  change Module.finrank F V = Module.finrank F (V.map g) at rd
  obtain ⟨p,W,r,inside⟩ := Green51BracketRank.flat_of_trace_space L (v:K) v.ne_zero (V.map g)
    (by rintro _ ⟨x,hx,rfl⟩; exact sub ⟨x,hx⟩) (by
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      have eq : (v:K)^7 * bracket (g x) (g y) = ((v:K)^7*s^3)*bracket x y := by
        simp only [g,LinearMap.mulLeft_apply,bracket]; ring
      rw [eq,scale,one_mul]; exact kill x hx y hy)
  exact ⟨p,W,by omega,inside⟩

omit [CharP K 2] in
private theorem units_coprime_seven (h : ¬3 ∣ Module.finrank F K) : (Nat.card Kˣ).Coprime 7 := by
  have prime : Nat.Prime 7 := by decide
  rw [Nat.coprime_comm,prime.coprime_iff_not_dvd,Nat.card_units,Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := F),ZMod.card]
  intro d
  apply h
  have nz : 0 < 2^(Module.finrank F K) := by positivity
  have div := (ZMod.natCast_eq_zero_iff _ 7).mpr d
  have eq : (2 : ZMod 7)^(Module.finrank F K)=1 := by
    rw [Nat.cast_sub (by omega : 1≤2^(Module.finrank F K)),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,sub_eq_zero] at div
    exact div
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ord : orderOf (2 : ZMod 7)=3 := orderOf_eq_prime (by decide) (by decide)
  exact ord ▸ orderOf_dvd_of_pow_eq_one eq

open Green51LocalFlats in
/-- Every nonzero binary projection of rank at most two has the same maximum
flat dimension in odd field degree not divisible by three. -/
theorem odd_maximum [FiniteDimensional F H] {k : ℕ} (hk : 0 < k) (dim : Module.finrank F K = 2*k+1)
    (div : ¬3 ∣ Module.finrank F K) (L : K →ₗ[F] H) (nL : L ≠ 0) (rank : Module.finrank F L.range ≤ 2) :
    maxCosetDim F (Space K × H) (Set.range (lifted L) + Set.range (lifted L)) = k+1 := by
  obtain ⟨p,W,d,inside⟩ := two_tests_in_odd k hk dim (units_coprime_seven div) L rank
  apply le_antisymm _ ((le_iff_coset (by omega : 0 < k+1) _).mpr ⟨W,p,d,inside⟩)
  by_contra! high
  obtain ⟨V,q,sz,sub⟩ := (le_iff_coset (by omega : 0 < k+2) _).mp high
  have lim := half_bound L nL q V sub (by omega)
  omega

end Green51OddPencils
#print axioms Green51OddPencils.two_tests_in_odd
#print axioms Green51OddPencils.odd_maximum
