import Green51BCHThreshold
/-! # Flats from scaled subfields in projected binary BCH doubles -/
open Green51BCH Green51BCHCompression Green51BCHOptimality
open scoped Pointwise
namespace Green51BracketRank
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

/-- A linear image of dimension below the field degree can be scaled into the absolute trace kernel. -/
theorem scale_into_trace {E : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]
    (f : E →ₗ[F] K) (room : Module.finrank F E < Module.finrank F K) :
    ∃ s : K, s ≠ 0 ∧ ∀ x, s * f x ∈ (artinSchreier (K := K)).range := by
  obtain ⟨Q,test⟩ := trace_test (K:=K)
  let P := (((Algebra.lmul F K).toLinearMap.compl₂ f).compr₂ Q)
  have rank := P.finrank_range_add_finrank_ker
  have bound := Submodule.finrank_le P.range
  change Module.finrank F P.range≤Module.finrank F (E →ₗ[F] F) at bound
  rw [Module.finrank_linearMap F F,Module.finrank_self,mul_one] at bound
  obtain ⟨s,mem,ns⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show P.ker≠⊥ by
    intro z;rw [z,finrank_bot] at rank;omega)
  exact ⟨s, ns, fun x => (test _).mp (LinearMap.congr_fun (show P s = 0 from mem) x)⟩

/-- A proper subfield can be scaled into the Artin–Schreier image; its
pair brackets lie in a third-power scale of the same subfield. -/
theorem subfield_flat {E : Type*} [Field E] [Algebra F E] [Finite E]
    (j : E →ₐ[F] K) (room : Module.finrank F E<Module.finrank F K) :
    ∃ S : Submodule F K, Module.finrank F S=Module.finrank F E ∧
    ∃ (p : Space K × (K ⧸ S)) (W : Submodule F (Space K × (K ⧸ S))),
      Module.finrank F W=Module.finrank F E ∧
      p+ᵥ (W:Set _) ⊆ Set.range (lifted S.mkQ)+Set.range (lifted S.mkQ) := by
  obtain ⟨s,ns,scaled⟩ := scale_into_trace j.toLinearMap room
  let f (a : K) := (LinearMap.mulLeft F a).comp j.toLinearMap
  have inj (a : K) (ha : a≠0) : Function.Injective (f a) :=
    fun _ _ h => j.injective (mul_left_cancel₀ ha h)
  let A := (f s).range
  let S := (f (s^3)).range
  have ra : Module.finrank F A=Module.finrank F E := (f s).finrank_range_of_inj (inj s ns)
  have rs : Module.finrank F S=Module.finrank F E := (f (s^3)).finrank_range_of_inj (inj _ (pow_ne_zero _ ns))
  let AS := artinSchreier (K:=K)
  have sub : A≤AS.range := by
    rintro _ ⟨a,rfl⟩
    exact scaled a
  let U := A.comap AS
  have ker : AS.ker≤U := by
    intro v hv
    change AS v∈A
    rw [show AS v=0 from hv]
    exact A.zero_mem
  have rankU := Green51QuadraticFlats.map_rank AS U ker
  change Module.finrank F ((A.comap AS).map AS)+Module.finrank F (artinSchreier (K:=K)).ker=Module.finrank F U at rankU
  rw [Submodule.map_comap_eq_self sub,ra,artinSchreier_ker,finrank_span_singleton one_ne_zero] at rankU
  have one : (1:K)∈U := by
    apply ker
    change (1:K)^2+1=0
    rw [one_pow,CharTwo.add_self_eq_zero]
  have kill (b) (hb : b∈U) (c) (hc : c∈U) : S.mkQ (moore 1 b c)=0 := by
    obtain ⟨x,hx⟩ := hb
    obtain ⟨y,hy⟩ := hc
    have xb : s*j x=b*(b+1) := by change s*j x=b^2+b at hx;rw [hx];ring
    have yc : s*j y=c*(c+1) := by change s*j y=c^2+c at hy;rw [hy];ring
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨x*y*(x+y),?_⟩
    change s^3*j (x*y*(x+y))=moore 1 b c
    rw [moore_bracket,one_mul,←xb,←yc]
    simp only [map_mul,map_add,bracket]
    ring
  obtain ⟨p,W,dim,inside⟩ := produces_flat S.mkQ U 1 one one_ne_zero kill
  exact ⟨S,rs,p,W,by omega,inside⟩

theorem flat_of_divisor (d : ℕ) (pos : 0<d)
    (dvd : d∣Module.finrank F K) (proper : d<Module.finrank F K) :
    ∃ S : Submodule F K, Module.finrank F S=d ∧
    ∃ (p : Space K × (K ⧸ S)) (W : Submodule F (Space K × (K ⧸ S))),
      Module.finrank F W=d ∧ p+ᵥ (W:Set _) ⊆ Set.range (lifted S.mkQ)+Set.range (lifted S.mkQ) := by
  let E := GaloisField 2 d
  have dim : Module.finrank F E=d := GaloisField.finrank 2 (by omega)
  have emb : Nonempty (E →ₐ[F] K) := FiniteField.nonempty_algHom_of_finrank_dvd (by rw [dim];exact dvd)
  obtain ⟨j⟩ := emb
  simpa [dim] using subfield_flat j (by rw [dim];exact proper)

end Green51BracketRank
#print axioms Green51BracketRank.scale_into_trace
#print axioms Green51BracketRank.subfield_flat
#print axioms Green51BracketRank.flat_of_divisor