import Green51BCHDirections
import Green53PolynomialColours
/-! # Seventh powers meeting a binary subspace of codimension at most three -/
open Green50Downsets Green53PolynomialColours Green52CubicPolar
open scoped Pointwise
namespace Green51BCHOptimality
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K]
omit [Algebra F K] in
private theorem triple_seventh (a b c x : K) :
    fwdDiff c (fwdDiff b (fwdDiff a (fun y : K => y^7))) x =
      a*b*c*(a+b)*(a+c)*(b+c)*(a+b+c) := by
  rw [←Green51BCH.seventh x a b c]
  simp only [fwdDiff,Green51BCH.cubeSum,CharTwo.sub_eq_add,add_assoc,add_left_comm,add_comm]
theorem seventh_cubic_of_dimension {d : ℕ} (L : K →ₗ[F] Cube d) : Cubic (fun x : K => L (x^7)) := by
  have step (z : K) (f : K → K) : fwdDiff z (fun x => L (f x)) = fun x => L (fwdDiff z f x) := by
    funext x; simp [fwdDiff]
  intro a b c d x
  change fwdDiff d (fwdDiff c (fwdDiff b (fwdDiff a (fun y : K => L ((fun z : K => z^7) y))))) x=0
  rw [step,step,step,step]
  change L (fwdDiff c (fwdDiff b (fwdDiff a (fun y : K => y^7))) (x+d) -
    fwdDiff c (fwdDiff b (fwdDiff a (fun y : K => y^7))) x)=0
  rw [triple_seventh,triple_seventh,sub_self,map_zero]

theorem seventh_cubic (L : K →ₗ[F] Cube 3) : Cubic (fun x : K => L (x^7)) :=
  seventh_cubic_of_dimension L

theorem seventh_meets_of_dimension [Fintype K] {d : ℕ} (L : K →ₗ[F] Cube d) (room : 3*d < Module.finrank F K) :
    ∃ h : K,h≠0 ∧ L (h^7)=0 := by
  classical
  obtain ⟨S,small,hits⟩ := Green53PolynomialColours.fibre_hits (fun x : K => L (x^7))
    (seventh_cubic_of_dimension L) 0 ⟨0,by simp⟩
  by_contra! none
  have full : S=Finset.univ := Finset.eq_univ_of_forall fun x => by
    obtain ⟨s,hs,hit⟩ := hits x
    have z : x+s=0 := by by_contra nz;exact none (x+s) nz hit
    rwa [CharTwo.add_eq_zero.mp z]
  rw [full,Finset.card_univ,Module.card_eq_pow_finrank (K:=F),ZMod.card] at small
  exact (Nat.not_le_of_lt (Nat.pow_lt_pow_right (by decide : 1<2) room)) small

theorem seventh_meets [Fintype K] (L : K →ₗ[F] Cube 3) (large : 10 ≤ Module.finrank F K) :
    ∃ x : K,x≠0 ∧ L (x^7)=0 :=
  seventh_meets_of_dimension L (by omega)

def artinSchreier : K →ₗ[F] K where
  toFun x := x^2+x
  map_add' x y := by rw [CharTwo.add_sq];abel
  map_smul' a x := by
    rcases (show ∀ a:F, a=0 ∨ a=1 from by decide) a with rfl|rfl <;> simp

theorem artinSchreier_ker : (artinSchreier (K:=K)).ker=Submodule.span F {1} := by
  apply le_antisymm
  · intro x hx
    change x^2+x=0 at hx
    have hx' : x*(x+1)=0 := by linear_combination hx
    rcases mul_eq_zero.mp hx' with z|z
    · exact z ▸ Submodule.zero_mem _
    · exact (CharTwo.add_eq_zero.mp z).symm ▸ Submodule.subset_span (Set.mem_singleton 1)
  · apply Submodule.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    change (1:K)^2+1=0
    rw [one_pow,CharTwo.add_self_eq_zero]

theorem trace_test [Finite K] :
    ∃ Q : K →ₗ[F] F, ∀ x : K,Q x=0 ↔ ∃ y : K,y^2+y=x := by
  let A : K →ₗ[F] K := artinSchreier
  have ker : A.ker=Submodule.span F {1} := artinSchreier_ker
  have rank := A.finrank_range_add_finrank_ker
  rw [ker,finrank_span_singleton (one_ne_zero : (1:K)≠0)] at rank
  have dim := A.range.finrank_quotient_add_finrank
  let e : (K ⧸ A.range) ≃ₗ[F] F := LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_self];omega)
  refine ⟨e.toLinearMap.comp A.range.mkQ,fun x => ?_⟩
  change e (A.range.mkQ x)=0 ↔ x∈A.range
  rw [LinearEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

omit [CharP K 2] in
theorem seventh_meets_coprime [Fintype K] (L : K →ₗ[F] Cube 3)
    (room : 4 ≤ Module.finrank F K) (primeTo : (Nat.card Kˣ).Coprime 7) :
    ∃ x : K,x≠0 ∧ L (x^7)=0 := by
  have rank := L.finrank_range_add_finrank_ker
  have lim : Module.finrank F L.range ≤ 3 := by simpa [Cube] using Submodule.finrank_le L.range
  obtain ⟨w,hw⟩ : ∃ w:L.ker,w≠0 := by
    by_contra! no
    have bot : L.ker=⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact (Submodule.mem_bot _).mpr (congrArg Subtype.val (no ⟨x,hx⟩))
    rw [bot,finrank_bot] at rank;omega
  let u := Units.mk0 w.val (fun h => hw (Subtype.ext h))
  obtain ⟨z,eq⟩ := (powCoprime primeTo).surjective u
  refine ⟨z.val,z.ne_zero,?_⟩
  have id : z.val^7=w.val := congrArg Units.val eq
  rw [id];exact w.property

/-- Every system of three binary linear tests vanishes on a nonzero seventh power. -/
def MeetsSeventhPowers (K : Type*) [Field K] [Algebra F K] : Prop :=
  ∀ L : K →ₗ[F] Cube 3, ∃ x : K, x≠0 ∧ L (x^7)=0

theorem meets_of_large [Fintype K] (large :
    10 ≤ Module.finrank F K ∨ 4 ≤ Module.finrank F K ∧ (Nat.card Kˣ).Coprime 7) :
    MeetsSeventhPowers K :=
  fun L => large.elim (seventh_meets L)
    (fun ⟨room,coprime⟩ => seventh_meets_coprime L room coprime)

/-- A common nonzero multiplier makes three prescribed Artin–Schreier equations soluble. -/
theorem simultaneous_of_meeting [Fintype K] (v : Fin 3 → K) (meets : MeetsSeventhPowers K) :
    ∃ a : K,a≠0 ∧ ∀ i,∃ z : K,z^2+z=a^7*v i := by
  obtain ⟨Q,test⟩ := trace_test (K:=K)
  let L : K →ₗ[F] Cube 3 :=
    { toFun x i := Q (x*v i)
      map_add' x y := by funext i; simp [add_mul]
      map_smul' r x := by funext i; simp }
  obtain ⟨x,nz,eq⟩ := meets L
  exact ⟨x,nz,fun i => (test _).mp (congrFun eq i)⟩

/-- A common nonzero multiplier makes three prescribed Artin–Schreier equations soluble. -/
theorem simultaneous_artin_schreier [Fintype K] (v : Fin 3 → K) (large :
    10 ≤ Module.finrank F K ∨ 4 ≤ Module.finrank F K ∧ (Nat.card Kˣ).Coprime 7) :
    ∃ a : K,a≠0 ∧ ∀ i,∃ z : K,z^2+z=a^7*v i :=
  simultaneous_of_meeting v (meets_of_large large)

end Green51BCHOptimality
#print axioms Green51BCHOptimality.seventh_meets
#print axioms Green51BCHOptimality.seventh_cubic
#print axioms Green51BCHOptimality.artinSchreier_ker
#print axioms Green51BCHOptimality.trace_test
#print axioms Green51BCHOptimality.seventh_meets_coprime
#print axioms Green51BCHOptimality.meets_of_large
#print axioms Green51BCHOptimality.simultaneous_of_meeting
#print axioms Green51BCHOptimality.simultaneous_artin_schreier
#print axioms Green51BCHOptimality.seventh_cubic_of_dimension
#print axioms Green51BCHOptimality.seventh_meets_of_dimension
