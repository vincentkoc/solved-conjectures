import Green51QuotientOrigin
import Green51MissingMaskClassification

/-! # Translations that preserve realizability by a dense binary double -/

namespace Green51OriginRecovery
open Finset Green53ParityThreshold Green51GirthFrame Green51Hyperplane
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

private theorem shift_nonaffine {C D : Finset G} (m : ShortestOddCircuit D C)
    (P : Submodule F G) (comp : IsCompl P (Submodule.span F (C : Set G)))
    (sub : D ⊆ (P : Set G).toFinset+C)
    (dense : ((P : Set G).toFinset+C).card < 2*D.card) (b : G) :
    ¬∃ f : G →ₗ[F] F, ∀ x ∈ D.map (Equiv.addRight b).toEmbedding, f x = 1 := by
  rintro ⟨f,ones⟩
  have const (x : G) (hx : x ∈ D) : f x=1-f b := by
    have h := ones _ (mem_map_of_mem (Equiv.addRight b).toEmbedding hx)
    change f (x+b)=1 at h
    exact eq_sub_of_add_eq (f.map_add x b ▸ h)
  have annih := kills_periods_of_majority P C D sub dense f (1-f b) const
  have zero := congrArg f m.2.2.1
  rw [map_sum,map_zero,sum_eq_card_nsmul (fun c hc => const c (m.1 hc))] at zero
  obtain ⟨j,hj⟩ := m.2.1
  rw [hj,add_nsmul,one_nsmul,show 2*j=j*2 by omega,mul_nsmul,two_nsmul,ZModModule.add_self,zero_add] at zero
  have kp : P ≤ f.ker := fun x hx => LinearMap.mem_ker.mpr (annih x hx)
  have kv : Submodule.span F (C : Set G) ≤ f.ker := Submodule.span_le.mpr (fun x hx =>
    LinearMap.mem_ker.mpr ((const x (m.1 hx)).trans zero))
  have bmem : b ∈ P ⊔ Submodule.span F (C : Set G) := by rw [comp.sup_eq_top]; trivial
  have fb := LinearMap.mem_ker.mp ((sup_le kp kv) bmem)
  exact one_ne_zero (by simpa only [fb,sub_zero] using zero)

private theorem frame_certificate {s r : ℕ} (hs : 5 ≤ s) {D : Finset (𝔽₂ (2*(s+1)+r))}
    (no : ¬∃ f : (𝔽₂ (2*(s+1)+r)) →ₗ[F] F, ∀ x ∈ D, f x=1)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*D.card)
    (realized : ∃ A : Finset (𝔽₂ (2*(s+1)+r)), (A+A)ᶜ=D ∧ threshold (2*s)<(A.dens : ℝ)) :
    ∃ C, ShortestOddCircuit D C ∧ C.card=2*s+3 ∧ ∃ P : Submodule F (𝔽₂ (2*(s+1)+r)),
      IsCompl P (Submodule.span F (C : Set _)) ∧ D ⊆ (P : Set (𝔽₂ (2*(s+1)+r))).toFinset+C ∧
      (P : Set (𝔽₂ (2*(s+1)+r))).toFinset.card=2^r ∧
      ((P : Set (𝔽₂ (2*(s+1)+r))).toFinset+C).card+2*(P : Set (𝔽₂ (2*(s+1)+r))).toFinset.card<2*D.card := by
  have amb : Module.finrank F (𝔽₂ (2*(s+1)+r))=2*(s+1)+r := by simp [𝔽₂,𝔽]
  have small := (Green51MissingMasks.realizable_iff_odd_girth hs D no near).mp realized
  obtain ⟨C,m,sz,P,comp,great,num⟩ := greatest_girth_extension D (2*s+3) (by omega)
    (by exact ⟨s+1,by omega⟩) small no (by
      rw [amb,show 2*(s+1)+r+1-(2*s+3)=r by omega]; exact near)
  have rank := circuit_rank m
  have both := Submodule.finrank_add_eq_of_isCompl comp
  rw [amb] at both
  have pr : Module.finrank F P=r := by omega
  have pc : (P : Set (𝔽₂ (2*(s+1)+r))).toFinset.card=2^r := by
    rw [Set.toFinset_card];change Fintype.card P=2^r
    rw [Module.card_eq_pow_finrank (K := F),pr];rfl
  refine ⟨C,m,sz,P,comp,great.1.1,pc,?_⟩
  rw [amb,show 2*(s+1)+r+1-(2*s+3)=r by omega] at num
  rw [num,pc]
  have bound := Nat.mul_le_mul_right (2^r) (show 4*((2*s+3)+2) ≤
    min (5*(2*s+3)+12) (4*(2*s+3)+20) by omega)
  rw [Nat.mul_assoc,Nat.add_mul] at bound
  omega

/-- A realized missing mask in the nonaffine branch meets every affine hyperplane. -/
theorem nonaffine_after_shift {s r : ℕ} (hs : 5 ≤ s) {D : Finset (𝔽₂ (2*(s+1)+r))}
    (no : ¬∃ f : (𝔽₂ (2*(s+1)+r)) →ₗ[F] F, ∀ x ∈ D, f x=1)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*D.card)
    (realized : ∃ A : Finset (𝔽₂ (2*(s+1)+r)), (A+A)ᶜ=D ∧ threshold (2*s)<(A.dens : ℝ))
    (b : 𝔽₂ (2*(s+1)+r)) :
    ¬∃ f : (𝔽₂ (2*(s+1)+r)) →ₗ[F] F, ∀ x ∈ D.map (Equiv.addRight b).toEmbedding, f x=1 := by
  obtain ⟨C,m,_,P,comp,sub,_,enough⟩ := frame_certificate hs no near realized
  exact shift_nonaffine m P comp sub (by omega) b

/-- Exactly one subspace of shifts gives further dense sumsets. The overlap test recovers it from
the given missing directions, so it can be computed without choosing a generating input. -/
theorem realizable_shifts {s r : ℕ} (hs : 5 ≤ s) {D : Finset (𝔽₂ (2*(s+1)+r))}
    (no : ¬∃ f : (𝔽₂ (2*(s+1)+r)) →ₗ[F] F, ∀ x ∈ D, f x=1)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*D.card)
    (realized : ∃ A : Finset (𝔽₂ (2*(s+1)+r)), (A+A)ᶜ=D ∧ threshold (2*s)<(A.dens : ℝ)) :
    ∃ P : Submodule F (𝔽₂ (2*(s+1)+r)), (P : Set (𝔽₂ (2*(s+1)+r))).toFinset.card=2^r ∧
      ∀ b, (b∈P ↔ 2*2^r < lag D b) ∧
        ((∃ A : Finset (𝔽₂ (2*(s+1)+r)), (A+A)ᶜ=D.map (Equiv.addRight b).toEmbedding ∧
          threshold (2*s)<(A.dens : ℝ)) ↔ b∈P) := by
  classical
  obtain ⟨C,m,sz,P,comp,sub,pc,enough⟩ := frame_certificate hs no near realized
  refine ⟨P,pc,fun b => ⟨by simpa only [pc] using recover_period m P comp sub enough b,?_⟩⟩
  let J := D.map (Equiv.addRight b).toEmbedding
  constructor
  · intro valid
    have nonaff := shift_nonaffine m P comp sub (by omega) b
    have more : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*J.card := by simpa [J] using near
    obtain ⟨B,mB,len,Q,cQ,sQ,qc,eQ⟩ := frame_certificate hs nonaff more valid
    have qe : Q=P := by
      ext t
      rw [recover_period mB Q cQ sQ eQ t,recover_period m P comp sub enough t,pc,qc]
      exact Iff.of_eq (congrArg (2*2^r < ·) (lag_shift D b t))
    subst Q
    have orig := quotient_labels m P comp sub (fun c hc => ⟨0,P.zero_mem,by simpa using m.1 hc⟩)
    have moved := quotient_labels mB P cQ sQ (fun c hc => ⟨0,P.zero_mem,by simpa using mB.1 hc⟩)
    have z := shifted_label_sum P D b (orig.1.symm ▸ m.2.1) orig.2
    exact (Submodule.Quotient.mk_eq_zero P).mp (z.symm.trans moved.2)
  · intro hb
    apply Green51MissingMasks.realize_in_container hs m sz P comp
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨p,hp,i,hi,rfl⟩ := mem_add.mp (sub ha)
    exact mem_add.mpr ⟨p+b,Set.mem_toFinset.mpr (P.add_mem (Set.mem_toFinset.mp hp) hb),i,hi,
      add_right_comm p b i⟩

end Green51OriginRecovery
#print axioms Green51OriginRecovery.realizable_shifts
#print axioms Green51OriginRecovery.nonaffine_after_shift
