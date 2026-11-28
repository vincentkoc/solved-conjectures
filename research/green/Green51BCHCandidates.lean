import Green51BCHThreshold
import Green51BinaryThreePlanes

/-! # Candidate kernels for projected seventh powers over the 64-element field -/

open Green50Downsets Green51BCH Green51BCHCompression Green51BCHOptimality Green51BCHFlags
open scoped Pointwise
namespace Green51BCHExceptional
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K]

abbrev TraceSpace (K : Type*) [Field K] [CharP K 2] [Algebra F K] :=
  (artinSchreier (K:=K)).range

private def normalize (t : K) : K →ₗ[F] TraceSpace K :=
  artinSchreier.rangeRestrict.comp (LinearMap.mulLeft F t⁻¹)

private theorem normalize_ker {t : K} (nt : t≠0) :
    (normalize t).ker=Submodule.span F {t} := by
  apply le_antisymm
  · intro x hx
    have root : t⁻¹*x ∈ (artinSchreier (K:=K)).ker :=
      congrArg Subtype.val (show normalize t x=0 from hx)
    rw [artinSchreier_ker,Submodule.mem_span_singleton] at root
    obtain ⟨r,hr⟩ := root
    rcases (show ∀ r:F,r=0 ∨ r=1 from by decide) r with rfl|rfl
    · simp only [zero_smul] at hr
      have z := (mul_eq_zero.mp hr.symm).resolve_left (inv_ne_zero nt)
      exact z ▸ Submodule.zero_mem _
    · simp only [one_smul] at hr
      have z : x=t := by calc
        x=t*(t⁻¹*x) := by field_simp
        _=t := by rw [←hr,mul_one]
      rw [z]
      exact Submodule.subset_span (Set.mem_singleton t)
  · apply Submodule.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change (t⁻¹*t)^2+t⁻¹*t=0
    rw [inv_mul_cancel₀ nt,one_pow,CharTwo.add_self_eq_zero]

private theorem normalized_minor {t : K} (nt : t≠0) (b c : K) :
    t^7*bracket ((normalize t b : TraceSpace K):K) ((normalize t c : TraceSpace K):K)=moore t b c := by
  rw [moore_bracket]
  change t^7*bracket ((t⁻¹*b)^2+t⁻¹*b) ((t⁻¹*c)^2+t⁻¹*c)=_
  unfold bracket
  field_simp

/-- The span of the scaled pair brackets on a subspace of the trace hyperplane. -/
def candidate (h : K) (A : Submodule F (TraceSpace K)) : Submodule F K :=
  Submodule.span F {z | ∃ a∈A,∃ b∈A,z=h*bracket (a:K) (b:K)}

abbrev NinthRoots (K : Type*) [Field K] := {h : Kˣ // h^9=1}

def candidateMap (v : NinthRoots K × Planes (TraceSpace K)) : Submodule F K :=
  candidate (v.1.val:K) v.2.val

omit [CharP K 2] in
theorem units_card [Finite K] (dim : Module.finrank F K=6) : Nat.card Kˣ=63 := by
  rw [Nat.card_units,Module.natCard_eq_pow_finrank (K:=F),dim,Nat.card_eq_fintype_card,ZMod.card]
  decide

/-- Every three-dimensional kernel producing a three-flat occurs in the finite candidate map. -/
theorem kernel_in_candidates [Fintype K] (dim : Module.finrank F K=6) (S : Planes K)
    (p : Space K × (K ⧸ S.val)) (W : Submodule F (Space K × (K ⧸ S.val)))
    (inside : p+ᵥ (W:Set _) ⊆ Set.range (lifted S.val.mkQ)+Set.range (lifted S.val.mkQ))
    (big : 3≤Module.finrank F W) : S.val∈Set.range (candidateMap (K:=K)) := by
  classical
  obtain ⟨t,U,nt,ht,sz,kill⟩ := input_four_of_flat S.val.mkQ p W inside big
  let A := U.map (normalize t)
  have line : (normalize t).ker≤U := by
    rw [normalize_ker nt];exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ht)
  have size := Green51QuadraticFlats.map_rank (normalize t) U line
  rw [normalize_ker nt,finrank_span_singleton nt,sz] at size
  let C := candidate (t^7) A
  have below : C≤S.val := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨b,hb,rfl⟩,_,⟨c,hc,rfl⟩,rfl⟩
    rw [normalized_minor nt]
    exact (Submodule.Quotient.mk_eq_zero _).mp (kill b hb c hc)
  have contains (b : K) (hb : b∈U) (c : K) (hc : c∈U) : moore t b c∈C := by
    apply Submodule.subset_span
    exact ⟨normalize t b,⟨b,hb,rfl⟩,normalize t c,⟨c,hc,rfl⟩,(normalized_minor nt b c).symm⟩
  obtain ⟨p',W',rank,flat⟩ := produces_flat C.mkQ U t ht nt
    (fun b hb c hc => (Submodule.Quotient.mk_eq_zero _).mpr (contains b hb c hc))
  have rc : 3≤Module.finrank F C := by
    by_contra! small
    have sc := excludes_three C.mkQ (by rw [Submodule.ker_mkQ];omega) p' W' flat
    omega
  let h := Units.mk0 t nt
  have order : (h^7)^9=1 := by
    rw [←pow_mul]
    have power := pow_card_eq_one (x:=h)
    rwa [←Nat.card_eq_fintype_card,units_card dim] at power
  refine ⟨(⟨h^7,order⟩,⟨A,by dsimp [A];omega⟩),?_⟩
  change C=S.val
  exact Submodule.eq_of_le_of_finrank_le below (by rw [S.property];exact rc)

end Green51BCHExceptional
#print axioms Green51BCHExceptional.kernel_in_candidates
