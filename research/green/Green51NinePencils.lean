import Green51OddPencils
import Green51NineRadicals
import Green51TwoGold

/-! # A 512-point subset of the binary 29-cube with no affine five-space in its double -/

open Green51BCH Green51BCHCompression Green51BCHOptimality Green51GoldForms
open scoped Pointwise
namespace Green51NinePencils
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

private theorem scalar_one (Q : K →ₗ[F] F) (test : ∀ z,Q z=0 ↔ ∃ y:K,y^2+y=z)
    (size : Fintype.card K=512) : Q 1=1 := by
  rcases (show ∀ a:F,a=0 ∨ a=1 from by decide) (Q 1) with h|h
  · obtain ⟨x,eq⟩ := (test 1).mp h
    have nx : x≠0 := by intro z;simp [z] at eq
    have cube : x^3=1 := by
      linear_combination (norm := (ring_nf;reduce_mod_char!)) (x+1)*eq
    have all := FiniteField.pow_card_sub_one_eq_one x nx
    rw [size,show 512-1=3*170+1 by decide,pow_succ,pow_mul,cube,one_pow,one_mul] at all
    rw [all,one_pow,CharTwo.add_self_eq_zero] at eq
    exact (zero_ne_one eq).elim
  · exact h

/-- An explicit surjective two-bit map excludes all affine five-spaces from the BCH double. -/
theorem nine_excludes_five (m : Module.finrank F K=9) :
    ∃ L : K →ₗ[F] F×F, Function.Surjective L ∧
      ∀ (p : Space K × (F×F)) (W : Submodule F (Space K × (F×F))),
      p+ᵥ (W:Set _) ⊆ Set.range (lifted L)+Set.range (lifted L) → Module.finrank F W≤4 := by
  have size : Fintype.card K=512 := by rw [Module.card_eq_pow_finrank (K:=F),ZMod.card,m];decide
  obtain ⟨g,rel,period⟩ := Green51SeventhOrbit.orbit_root (K:=K) size
  have : Fact (Nat.Prime 73) := ⟨by decide⟩
  have root : IsPrimitiveRoot g 73 := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime period (by rintro rfl;simp at rel))
  obtain ⟨Q,nq,sq,test⟩ := trace_functional (K:=K)
  have one := scalar_one Q test size
  obtain ⟨zero,other⟩ := beta_traces Q one sq g rel
  have nb : beta g≠0 := by intro z;simp [z] at other
  have n1 : beta g≠1 := by intro z;rw [z,one] at zero;exact one_ne_zero zero
  let L:=Q.prod (Q.comp (LinearMap.mulLeft F (beta g)))
  refine ⟨L,Green51TwoGold.pair_surjective Q nq nb n1,?_⟩
  intro p W inside
  by_contra! big
  obtain ⟨t,nt,A,rank,trace,iso⟩ := Green51BracketRank.trace_space_of_flat L p W inside (by omega)
  let s:=t^343
  have non : s≠0 := pow_ne_zero _ nt
  have all := FiniteField.pow_card_sub_one_eq_one t nt
  rw [size] at all
  have small : t^511=1 := all
  have cube : s^3=t^7 := by
    rw [show s^3=t^(343*3) by rw [pow_mul],show 343*3=511*2+7 by decide,pow_add,pow_mul,small,one_pow,one_mul]
  have seven : (s⁻¹)^73=1 := by
    rw [inv_pow,show s^73=t^(343*73) by rw [pow_mul],show 343*73=511*49 by decide,pow_mul,small,one_pow,inv_one]
  obtain ⟨j,hj,hp⟩:=root.eq_pow_of_pow_eq_one seven
  let f:=LinearMap.mulLeft F s
  let U:=A.map f
  have dimU := (A.equivMapOfInjective f (fun _ _ eq => mul_left_cancel₀ non eq)).finrank_eq
  change Module.finrank F A=Module.finrank F U at dimU
  have kill (x : K) (hx : x∈U) (y : K) (hy : y∈U) : L (bracket x y)=0 := by
    obtain ⟨a,ha,rfl⟩:=hx
    obtain ⟨b,hb,rfl⟩:=hy
    have eq : bracket (f a) (f b)=s^3*bracket a b := by simp only [f,LinearMap.mulLeft_apply,bracket];ring
    rw [eq,cube];exact iso a ha b hb
  have forced:=chain_forced Q nq sq m size g rel U (by omega)
    (fun x hx y hy => congrArg Prod.fst (kill x hx y hy))
    (fun x hx y hy => congrArg Prod.snd (kill x hx y hy))
  apply blocks_trace Q one sq g rel ⟨j,hj⟩ U forced
  rintro _ ⟨a,ha,rfl⟩
  change Q (g^j*(s*a))=0
  rw [hp,←mul_assoc,inv_mul_cancel₀ non,one_mul]
  exact (test a).mpr (trace ha)

open Green50Downsets Green51LocalFlats Classical in
/-- Four is the minimum achievable largest-flat dimension among two-bit projections. -/
theorem nine_optimal (m : Module.finrank F K=9) :
    IsLeast (Set.range (fun L : K →ₗ[F] F × F =>
      maxCosetDim F (Space K × (F × F)) (Set.range (lifted L)+Set.range (lifted L)))) 4 := by
  have low (L : K →ₗ[F] F × F) : 4 ≤ maxCosetDim F (Space K × (F × F))
      (Set.range (lifted L)+Set.range (lifted L)) := by
    have rank : Module.finrank F L.range≤2 := (Submodule.finrank_le _).trans (by simp)
    obtain ⟨p,W,d,inside⟩:=Green51BCHExceptional.two_tests_floor 3 (by omega) L rank
    exact (le_iff_coset (by decide : 0<4) _).mpr ⟨W,p,d,inside⟩
  obtain ⟨L,_,bound⟩:=nine_excludes_five m
  constructor
  · refine ⟨L,le_antisymm ?_ (low L)⟩
    by_contra! high
    obtain ⟨W,p,sz,sub⟩:=(le_iff_coset (by decide : 0<5) _).mp high
    have lim:=bound p W sub
    omega
  · rintro _ ⟨L,rfl⟩
    exact low L

open Green50Downsets Green51LocalFlats Finset in
/-- A set of exactly 512 points in the 29-cube whose double excludes every affine five-space. -/
theorem cube_witness :
    ∃ A : Finset (𝔽₂ 29), A.card = 512 ∧ maxCosetDim F (𝔽₂ 29) ↑(A + A) ≤ 4 := by
  classical
  let E:=GaloisField 2 9
  let _ : Fintype E:=Fintype.ofFinite E
  have sz : Module.finrank F E=9 := GaloisField.finrank 2 (by decide)
  obtain ⟨L,_,avoid⟩:=nine_excludes_five sz
  let j : (Space E × (F×F)) ≃ₗ[F] Cube 29 := LinearEquiv.ofFinrankEq _ _ (by simp [Space,Cube,sz])
  obtain ⟨A,card,bound⟩:=transport_dimension L j avoid
  have cardE : Fintype.card E=512 := by rw [Module.card_eq_pow_finrank (K:=F),ZMod.card,sz];decide
  refine ⟨A,card.trans cardE,?_⟩
  by_contra! high
  obtain ⟨W,p,sz,sub⟩:=(le_iff_coset (by decide : 0<5) _).mp high
  exact (by decide : ¬(5:ℕ)≤4) (sz.symm.trans_le (bound W p sub))

open Green50Downsets Green51LocalFlats Finset in
/-- The same witness bounds the guaranteed dimension on the original Green 51 cube. -/
theorem twenty_nine {α : ℝ} (density : α ≤ 512 / (2:ℝ)^29) :
    Green51.guaranteedMaxCosetDim 29 α ≤ 4 := by
  obtain ⟨A,card,bound⟩ := cube_witness
  have adm : α ≤ (A.dens : ℝ) := by
    rw [Finset.nnratCast_dens,card]
    norm_num [Cube] at density ⊢
    exact density
  exact (csInf_le (OrderBot.bddBelow _) ⟨A,adm,rfl⟩ :
    Green51.guaranteedMaxCosetDim 29 α ≤ maxCosetDim F (𝔽₂ 29) ↑(A+A)).trans bound

end Green51NinePencils
#print axioms Green51NinePencils.nine_excludes_five
#print axioms Green51NinePencils.nine_optimal
#print axioms Green51NinePencils.cube_witness
#print axioms Green51NinePencils.twenty_nine
