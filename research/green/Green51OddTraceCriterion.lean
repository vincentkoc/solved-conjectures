import Green51OddTraceFlats
import Green51PencilCoefficients
import Green51PencilHyperplanes
import Green51BCHFourForces

/-! # An exact coefficient test for odd-degree two-bit BCH projections -/

open Green51GoldForms Green51BCHCompression
namespace Green51OddTrace
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
open Green51BCH Green51BCHOptimality Green51LocalFlats
open scoped Pointwise
open Green51PencilWindows

/-- A full-degree ratio has one common isotropic space of dimension k+1. -/
theorem unique_space (Q : K →ₗ[F] F) (nQ : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    {k : ℕ} (degree : Module.finrank F K = 2*k+1) {b : K} (generates : Algebra.adjoin F {b}=⊤)
    (U : Submodule F K) (large : k+1 ≤ Module.finrank F U)
    (iso : ∀ x∈U,∀ y∈U,Q (bracket x y)=0 ∧ Q (b*bracket x y)=0) :
    Submodule.span F (Set.range (fun j : Fin (k+1) => term k b j.val)) = U := by
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact forced Q nQ sq degree b (term k b) (term_zero k b) (term_step degree b) U large
      (fun x hx y hy => (iso x hx y hy).1) (fun x hx y hy => (iso x hx y hy).2) j.val (by omega)
  · have dim := finrank_span_eq_card (term_independent degree generates)
    rw [Fintype.card_fin] at dim
    have limit := isotropic_bound Q nQ U (fun x hx y hy => (iso x hx y hy).1)
    omega

/-- Every hyperplane containing the companion coefficients contains a largest common
isotropic space, including ratios in proper subfields. -/
theorem realize (Q : K →ₗ[F] F) (nQ : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    {k : ℕ} (degree : Module.finrank F K=2*k+1) (b : K) (l : K →ₗ[F] F)
    (vanish : ∀ j : Fin (k+1),l (term k b j.val)=0) :
    ∃ U : Submodule F K, Module.finrank F U=k+1 ∧ U≤l.ker ∧
      ∀ x∈U,∀ y∈U,Q (bracket x y)=0 ∧ Q (b*bracket x y)=0 := by
  let A := bracketForm Q 1
  let B := bracketForm Q b
  let D := Submodule.span F (Set.range (fun j : Fin (k+1) => term k b j.val))
  have alt (c : K) : (bracketForm Q c).IsAlt := fun x => by
    change Q (c*bracket x x)=0
    simp [bracket,CharTwo.add_self_eq_zero]
  obtain ⟨S,dimS,first,second⟩ := Green51TwoAlternating.simultaneous F k A B (alt 1) (alt b) degree
  have iso (x) (hx : x∈S) (y) (hy : y∈S) : Q (bracket x y)=0 := by
    simpa [A,bracketForm] using first x hx y hy
  have inS : D≤S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact forced Q nQ sq degree b (term k b) (term_zero k b) (term_step degree b) S
      dimS.ge iso second j.val (by omega)
  have selfA : D≤A.orthogonal D := fun x hx y hy => first y (inS hy) x (inS hx)
  have selfB : D≤B.orthogonal D := fun x hx y hy => second y (inS hy) x (inS hx)
  have inD (i : ℕ) (hi : i≤k) : term k b i∈D :=
    Submodule.subset_span ⟨⟨i,by omega⟩,rfl⟩
  have oneD : (1:K)∈D := term_zero k b ▸ inD 0 (by omega)
  have oneA : (1:K)∈A.ker := by
    apply (radical Q nQ sq 1 1).mpr
    simp [CharTwo.add_self_eq_zero]
  have radDim := Submodule.finrank_mono (Submodule.span_le.mpr
    (Set.singleton_subset_iff.mpr (show (1:K) ∈ D ⊓ A.ker from ⟨oneD,oneA⟩)))
  rw [finrank_span_singleton one_ne_zero] at radDim
  have cross : A.orthogonal D ≤ B.orthogonal D := by
    intro y hy
    have annih : D ≤ (B.flip y).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change bracketForm Q b (term k b i.val) y=0
      rw [bracketForm_apply_squared Q sq]
      by_cases last : i.val=k
      · rw [last,term_end degree b,zero_mul,map_zero]
      · have hi : i.val<k := by omega
        rw [←term_step degree b i.val hi]
        have same := bracketForm_apply_squared Q sq 1 (term k b (i.val+1)) y
        simp only [one_pow,one_mul] at same
        rw [←same]
        exact hy _ (inD (i.val+1) (by omega))
    exact fun x hx => annih hx
  have hzero : D≤l.ker := Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩;exact vanish j)
  obtain ⟨U,_,ker,dim,aa,bb⟩:=Green51PencilHyperplanes.in_hyperplane A B (alt 1) (alt b) degree D
    ((Submodule.finrank_mono inS).trans_eq dimS) radDim selfA selfB cross l hzero
  refine ⟨U,dim,ker,fun x hx y hy => ⟨?_,bb hy x hx⟩⟩
  simpa [A,bracketForm] using aa hy x hx

theorem all_ratios (Q : K →ₗ[F] F) (nQ : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z)
    {k : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k+1)
    {a : K} (na : a≠0) (b : K) :
    let L:=twoTraces Q a (a*b)
    k+1 ≤ maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)) ↔
      ∃ h : K,h≠0 ∧ ∀ j : Fin (k+1),Q ((a^2*h^7)*term k b j.val)=0 := by
  intro L
  refine (scaled_flat_iff Q test degree (by omega : 3≤k+1) na b).trans ?_
  constructor
  · rintro ⟨U,dim,iso,h,nh,z⟩
    refine ⟨h,nh,fun j => z _ ?_⟩
    exact forced Q nQ sq degree b (term k b) (term_zero k b) (term_step degree b) U dim.ge
      (fun x hx y hy => (iso x hx y hy).1) (fun x hx y hy => (iso x hx y hy).2) j.val (by omega)
  · rintro ⟨h,nh,z⟩
    obtain ⟨U,d,ker,iso⟩:=realize Q nQ sq degree b (Q.comp (LinearMap.mulLeft F (a^2*h^7))) z
    exact ⟨U,d,iso,h,nh,fun _ hx => ker hx⟩

open scoped Classical in
theorem exact_maximum (Q : K →ₗ[F] F) (nQ : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z)
    {k : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k+1) {a : K} (na : a≠0) (b : K) :
    let L:=twoTraces Q a (a*b)
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)) =
      if ∃ h : K,h≠0 ∧ ∀ j : Fin (k+1),Q ((a^2*h^7)*term k b j.val)=0 then k+1 else k := by
  intro L
  let A:= Set.range (lifted L)+Set.range (lifted L)
  let value:=maxCosetDim F (Space K × (F×F)) A
  have non : L≠0 := by
    intro e
    apply nQ
    ext x
    have h := congrArg Prod.fst (LinearMap.congr_fun e (a⁻¹*x))
    change Q (a*(a⁻¹*x))=0 at h
    change Q x=0
    simpa only [←mul_assoc,mul_inv_cancel₀ na,one_mul] using h
  have lower : k≤value := by
    obtain ⟨p,W,dim,inside⟩ := Green51BCHExceptional.two_tests_floor (k-1) (by omega) L
      ((Submodule.finrank_le _).trans (by simp))
    exact (le_iff_coset (by omega : 0<k) _).mpr ⟨W,p,by omega,inside⟩
  have upper : value ≤ k+1 := by
    by_contra! high
    obtain ⟨W,p,dim,inside⟩:=(le_iff_coset (by omega : 0<k+2) A).mp high
    have lim:=half_bound L non p W inside (by omega)
    omega
  have iff := all_ratios Q nQ sq test hk degree na b
  change k+1≤value ↔ _ at iff
  change value = _
  split_ifs with hit
  · exact upper.antisymm (iff.mpr hit)
  · have lt:=mt iff.mp hit
    omega

open scoped Classical in
/-- Exact largest affine dimension in the double of the two-coordinate absolute trace graph. -/
theorem absolute_maximum {k : ℕ} (hk : 2 ≤ k) (degree : Module.finrank F K = 2*k+1)
    {a : K} (na : a ≠ 0) (b : K) :
    let T := Algebra.trace F K
    let L := twoTraces T a (a*b)
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L) + Set.range (lifted L)) =
      if ∃ h : K, h ≠ 0 ∧ ∀ j : Fin (k+1), T ((a^2*h^7)*term k b j.val)=0 then k+1 else k :=
  exact_maximum (Algebra.trace F K) (Algebra.trace_ne_zero F K) absolute_trace_test.1
    absolute_trace_test.2 hk degree na b

end Green51OddTrace

#print axioms Green51OddTrace.unique_space
#print axioms Green51OddTrace.realize
#print axioms Green51OddTrace.all_ratios
#print axioms Green51OddTrace.exact_maximum
#print axioms Green51OddTrace.absolute_maximum
