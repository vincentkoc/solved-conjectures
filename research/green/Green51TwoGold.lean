import Green51GoldPencils
import Green51BCHFourForces
import Green51BCHPlateau
/-! # Exact optimum for two linear BCH coordinates in even field dimension -/
open Green51GoldForms Green51BCH Green51BCHCompression
open scoped Pointwise
namespace Green51TwoGold
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

omit [CharP K 2] in
private theorem exists_noncube {k:ℕ} (dim : Module.finrank F K=2*k) :
    ∃ c:K, ∀ y:K, y^3≠c := by
  classical
  have h3 : 3∣Fintype.card Kˣ := by
    rw [Fintype.card_units,Module.card_eq_pow_finrank (K:=F),ZMod.card,dim,pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨w,hw⟩ := exists_prime_orderOf_dvd_card (G:=Kˣ) 3 h3
  have w3 : (w:K)^3=1 := by
    have eq := pow_orderOf_eq_one w
    rw [hw] at eq
    exact congrArg (fun u:Kˣ => (u:K)) eq
  by_contra! all
  have inj : Function.Injective (fun x:K => x^3) := Finite.injective_iff_surjective.mpr all
  have w1 : (w:K)=1 := inj (w3.trans (one_pow 3).symm)
  have eq : w=1 := Units.ext w1
  simp [eq] at hw

omit [Fintype K] in
/-- Distinct nonzero trace coefficients give a surjective pair of binary coordinates. -/
theorem pair_surjective (Q : K →ₗ[F] F) (nq : Q≠0) {c:K} (nc:c≠0) (n1:c≠1) :
    Function.Surjective (Q.prod (Q.comp (LinearMap.mulLeft F c))) := by
  let L := Q.prod (Q.comp (LinearMap.mulLeft F c))
  change Function.Surjective L
  rw [←LinearMap.range_eq_top]
  by_contra h
  obtain ⟨f,nf,vanishes⟩ := L.range.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr h)
  let a := f (1,0)
  let b := f (0,1)
  have formula (u v:F) : f (u,v)=u*a+v*b := by
    have e : (u,v)=u • ((1,0):F×F)+v • ((0,1):F×F) := by ext <;> simp
    rw [e,map_add,map_smul,map_smul]; rfl
  have detect (d:K) (all : ∀ x:K,Q (d*x)=0) : d=0 := by
    by_contra nd
    apply nq
    ext x
    simpa [←mul_assoc,nd] using all (d⁻¹*x)
  have both (x:K) : Q x*a+Q (c*x)*b=0 :=
    (formula (Q x) (Q (c*x))).symm.trans (show f (L x)=0 from vanishes (LinearMap.mem_range_self L x))
  have bits : ∀ t:F,t=0 ∨ t=1 := by decide
  rcases bits a with ha|ha <;> rcases bits b with hb|hb
  · exact nf (LinearMap.ext (fun ⟨u,v⟩ => by simp [formula,ha,hb]))
  · exact nc (detect c (fun x => by simpa [ha,hb] using both x))
  · exact one_ne_zero (detect 1 (fun x => by simpa [ha,hb] using both x))
  · have z : (1:K)+c=0 := detect _ (fun x => by simpa [add_mul,map_add,ha,hb] using both x)
    exact n1 (CharTwo.add_eq_zero.mp z).symm

/-- A surjective pair of trace tests excludes all flats above half the field dimension. -/
theorem two_tests_bound {k : ℕ} (hk : 2 ≤ k) (dim : Module.finrank F K = 2*k) :
    ∃ L : K →ₗ[F] F × F, Function.Surjective L ∧
      ∀ (p : Space K × (F × F)) (W : Submodule F (Space K × (F × F))),
        p +ᵥ (W : Set _) ⊆ Set.range (lifted L) + Set.range (lifted L) → Module.finrank F W ≤ k := by
  obtain ⟨c, noncube⟩ := exists_noncube dim
  obtain ⟨Q, nq, sq, _⟩ := trace_functional (K := K)
  have nc : c ≠ 0 := fun h => noncube 0 (by simp [h])
  have n1 : c ≠ 1 := fun h => noncube 1 (by simp [h])
  let L := Q.prod (Q.comp (LinearMap.mulLeft F c))
  refine ⟨L, pair_surjective Q nq nc n1, ?_⟩
  intro p W inside
  by_contra! large
  obtain ⟨r, hr⟩ := cubic_ratios Q nq sq L (a := 1) (b := c) one_ne_zero nc
    (LinearMap.fst F F F) (LinearMap.snd F F F) (fun z => by simp [L]) (fun _ => rfl)
    p W inside (by omega) (by omega)
  exact noncube r (by simpa using hr)

open Green50Downsets Green51LocalFlats in
/-- Half the extension degree is the exact optimum over all pairs of linear tests. -/
theorem optimal {k:ℕ} (hk : 2≤k) (dim : Module.finrank F K=2*k) :
    IsLeast (Set.range (fun L:K →ₗ[F] F×F =>
      maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)))) k := by
  let score (L : K →ₗ[F] F×F) :=
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L))
  have lower (L : K →ₗ[F] F×F) : k ≤ score L := by
    have rank : Module.finrank F L.range≤2 := (Submodule.finrank_le L.range).trans (by simp)
    obtain ⟨p,W,sz,sub⟩ := Green51BCHExceptional.two_tests_in_even (k-1) (by omega) L rank
    exact (le_iff_coset (by omega : 0<k) _).mpr ⟨W,p,by omega,sub⟩
  refine ⟨?_,?_⟩
  · obtain ⟨L,_,bound⟩ := two_tests_bound hk dim
    refine ⟨L,le_antisymm ?_ (lower L)⟩
    by_contra! high
    obtain ⟨W,p,sz,sub⟩ := (le_iff_coset (by omega : 0<k+1) _).mp high
    exact (Nat.not_succ_le_self k) (sz.symm.trans_le (bound p W sub))
  · rintro _ ⟨L,rfl⟩
    exact lower L

open Green50Downsets Green51LocalFlats Finset in
/-- The two-bit construction provides a finite-set witness on the exact Green 51 cube. -/
theorem guaranteed {k:ℕ} (hk : 2≤k) {α:ℝ} (density : α≤(2:ℝ)^(2*k)/2^(6*k+2)) :
    Green51.guaranteedMaxCosetDim (6*k+2) α≤k := by
  classical
  let E := GaloisField 2 (2*k)
  let _ : Fintype E := Fintype.ofFinite E
  have sz : Module.finrank F E=2*k := GaloisField.finrank 2 (by omega)
  obtain ⟨L,_,avoid⟩ := two_tests_bound hk sz
  let j : (Space E × (F×F)) ≃ₗ[F] Cube (6*k+2) := LinearEquiv.ofFinrankEq _ _ (by simp [Space,Cube,sz];omega)
  obtain ⟨A,card,bound⟩ := transport_dimension L j avoid
  have cardE : Fintype.card E=2^(2*k) := by rw [Module.card_eq_pow_finrank (K:=F),ZMod.card,sz]
  have adm : α≤(A.dens:ℝ) := by simpa [Finset.nnratCast_dens,card,cardE,Cube] using density
  have inf : Green51.guaranteedMaxCosetDim (6*k+2) α ≤ maxCosetDim F (𝔽₂ (6*k+2)) ↑(A+A) :=
    csInf_le (OrderBot.bddBelow _) ⟨A,adm,rfl⟩
  apply inf.trans
  by_contra! high
  obtain ⟨W,p,rank,sub⟩ := (le_iff_coset (by omega : 0<k+1) _).mp high
  exact (Nat.not_succ_le_self k) (rank.symm.trans_le (bound W p sub))

end Green51TwoGold
#print axioms Green51TwoGold.pair_surjective
#print axioms Green51TwoGold.two_tests_bound
#print axioms Green51TwoGold.optimal
#print axioms Green51TwoGold.guaranteed
