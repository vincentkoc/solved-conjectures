import Green51EvenTraceSpace
import Green51EvenTraceRank
import Green51OddPencils

/-! # The maximum affine dimension for every two-trace graph of even degree -/

namespace Green51EvenChains
open Green51GoldForms Green51PencilWindows Green51BCH Green51BCHCompression Green51LocalFlats
open scoped Pointwise
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

theorem fixed_criterion {k : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k)
    {a : K} (na : a≠0) (l : ℕ) (b : K) (period : orbit b l=b) :
    let T := Algebra.trace F K
    let L := twoTraces T a (a*b)
    k+1 ≤ maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)) ↔
      ∃ h : K,h≠0 ∧ ∀ w : Quartic K,∀ i : Fin (l+1),T ((a^2*h^7)*(w.val*term l b i.val))=0 := by
  intro T L
  have nQ : T≠0 := Algebra.trace_ne_zero F K
  have tr := absolute_trace_test (K:=K)
  refine (scaled_flat_iff T tr.2 nQ tr.1 degree (by omega : 3≤k+1) le_rfl na b).trans ?_
  constructor
  · rintro ⟨U,size,iso,h,nh,z⟩
    let f := T.comp (LinearMap.mulLeft F (a^2*h^7))
    have ker : U≤f.ker := fun x hx => z x hx
    have all := (in_hyperplane_iff T nQ tr.1 degree l b period f).mp ⟨U,size,ker,iso⟩
    refine ⟨h,nh,fun w i => ?_⟩
    exact all (Green51PencilChains.generators l (entry l b) w i.val (by omega))
  · rintro ⟨h,nh,z⟩
    let f := T.comp (LinearMap.mulLeft F (a^2*h^7))
    have ker : space l b≤f.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨w,i⟩,rfl⟩
      exact z w i
    obtain ⟨U,size,killed,iso⟩ := (in_hyperplane_iff T nQ tr.1 degree l b period f).mpr ker
    exact ⟨U,size,iso,h,nh,fun _ hx => killed hx⟩

theorem saturated_of_coprime {k : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k)
    {a : K} (na : a≠0) (l : ℕ) (b : K) (period : orbit b l=b)
    (cop : (Nat.card Kˣ).Coprime 7) :
    let L := twoTraces (Algebra.trace F K) a (a*b)
    k+1 ≤ maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)) := by
  intro L
  let T:=Algebra.trace F K
  have nQ : T≠0 := Algebra.trace_ne_zero F K
  have tr := absolute_trace_test (K:=K)
  obtain ⟨U,size,_,iso⟩ := (in_hyperplane_iff T nQ tr.1 degree l b period 0).mpr (by simp)
  have proper : U<⊤ := lt_top_iff_ne_top.mpr (by
    intro eq
    rw [eq,finrank_top,degree] at size
    omega)
  obtain ⟨f,nf,inc⟩ := U.exists_le_ker_of_lt_top proper
  obtain ⟨v,rep⟩ := represent T nQ f
  have nv : v≠0 := by rintro rfl;apply nf;ext x;simp [rep]
  let w := Units.mk0 (v/a^2) (div_ne_zero nv (pow_ne_zero 2 na))
  obtain ⟨u,pw⟩ := (powCoprime cop).surjective w
  have eq : a^2*(u:K)^7=v := by
    have val : (u:K)^7=v/a^2 := congrArg (fun x:Kˣ => (x:K)) pw
    rw [val];field_simp
  apply (scaled_flat_iff T tr.2 nQ tr.1 degree (by omega : 3≤k+1) le_rfl na b).mpr
  exact ⟨U,size,iso,u,u.ne_zero,fun x hx => by rw [eq,←rep];exact inc hx⟩
end Green51EvenChains

namespace Green51EvenChains
open Green51GoldForms Green51PencilWindows Green51BCH Green51BCHCompression Green51LocalFlats Green51BCHOptimality
open scoped Pointwise
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

def coefficientTest (l : ℕ) (a b : K) : Prop := orbit b l=b ∧
  ∃ h : K,h≠0 ∧ ∀ w : Quartic K, ∀ i : Fin (l+1),
    Algebra.trace F K ((a^2*h^7)*(w.val*term l b i.val))=0

theorem large_iff {k s l : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k)
    (parts : 2*k=2^s*(2*l+1)) {a : K} (na : a≠0) (b : K) :
    let L := twoTraces (Algebra.trace F K) a (a*b)
    k+1 ≤ maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)) ↔
      coefficientTest l a b := by
  intro L
  by_cases h : orbit b l=b
  · simpa [coefficientTest,h] using fixed_criterion hk degree na l b h
  · have move : Green51FrobeniusPencil.fr (2*l+1) b≠b := by
      rw [orbit_expr] at h
      exact h
    have size := Green51FrobeniusPencil.exact_of_moves hk degree na (fun i =>
      Green51FrobeniusPencil.moves_of_not_fixed (degree.trans parts) move i.val)
    change maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L))=k at size
    simp [coefficientTest,h,size]

open scoped Classical in
theorem absolute_maximum {k s l : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k)
    (parts : 2*k=2^s*(2*l+1)) {a : K} (na : a≠0) (b : K) :
    let L := twoTraces (Algebra.trace F K) a (a*b)
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)) =
      if coefficientTest l a b then k+1 else k := by
  intro L
  let Q:=Algebra.trace F K
  have nQ : Q≠0 := Algebra.trace_ne_zero F K
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
    obtain ⟨V,p,dim,sub⟩:=(le_iff_coset (by omega : 0<k+2) A).mp high
    have lim:=half_bound L non p V sub (by omega)
    omega
  have iff:=large_iff hk degree parts na b
  change k+1≤value ↔ _ at iff
  change value = _
  split_ifs with hit
  · exact upper.antisymm (iff.mpr hit)
  · have lt:=mt iff.mp hit
    omega

open scoped Classical in
theorem subfield_maximum {k s l : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k)
    (parts : 2*k=2^s*(2*l+1)) (cop : ¬3 ∣ Module.finrank F K) {a : K} (na : a≠0) (b : K) :
    let L := twoTraces (Algebra.trace F K) a (a*b)
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)) =
      if b^(2^(2*l+1))=b then k+1 else k := by
  intro L
  have criterion : coefficientTest l a b ↔ b^(2^(2*l+1))=b := by
    constructor
    · exact fun hit => (orbit_expr b l).symm.trans hit.1
    · intro fixed
      apply (large_iff hk degree parts na b).mp
      exact saturated_of_coprime hk degree na l b ((orbit_expr b l).trans fixed) (Green51OddPencils.units_coprime_seven cop)
  simpa only [criterion] using absolute_maximum hk degree parts na b
end Green51EvenChains

#print axioms Green51EvenChains.fixed_criterion
#print axioms Green51EvenChains.saturated_of_coprime
#print axioms Green51EvenChains.large_iff
#print axioms Green51EvenChains.absolute_maximum
#print axioms Green51EvenChains.subfield_maximum
