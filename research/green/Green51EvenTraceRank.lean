import Green51FrobeniusPencil
import Green51BCHFourForces
import Green51LocalFlats

/-! # The odd part of the field degree bounds the rank of an oversized projection -/

open Finset Green51BCHCompression
open Fin.NatCast
namespace Green51FrobeniusPencil
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
open Green51BCH Green51GoldForms Green51LocalFlats Green51BCHOptimality
open scoped Pointwise

theorem projected_ceiling {H : Type*} [AddCommGroup H] [Module F H] [Module.Finite F H]
    {k : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k)
    (L : K →ₗ[F] H) {a b : K} (na : a≠0) (moves : ∀ i : Fin k, fr (2*i.val+1) b≠b)
    (f g : H →ₗ[F] F) (l : ∀ z, f (L z)=Algebra.trace F K (a*z))
    (r : ∀ z, g (L z)=Algebra.trace F K ((a*b)*z)) :
    maxCosetDim F (Space K × H) (Set.range (lifted L)+Set.range (lifted L))≤k := by
  by_contra! large
  let _ : NeZero k := ⟨by omega⟩
  obtain ⟨W,p,rank,sub⟩ := (le_iff_coset (by omega : 0<k+1) _).mp large
  obtain ⟨t,nt,U,dimU,_,kill⟩ := Green51BracketRank.trace_space_of_flat L p W sub (by omega)
  have bound := isotropic_ceiling degree (a:=a*t^7) (mul_ne_zero na (pow_ne_zero _ nt)) moves U (by
    intro x hx y hy
    have h := kill x hx y hy
    constructor
    · rw [mul_assoc,←l,h,map_zero]
    · rw [show a*t^7*b*bracket x y=(a*b)*(t^7*bracket x y) by ring,←r,h,map_zero])
  omega

theorem exact_of_moves {k : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k)
    {a b : K} (na : a≠0) (moves : ∀ i : Fin k, fr (2*i.val+1) b≠b) :
    let L := twoTraces (Algebra.trace F K) a (a*b)
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L))=k := by
  intro L
  apply le_antisymm
  · exact projected_ceiling hk degree L na moves (LinearMap.fst F F F) (LinearMap.snd F F F)
      (fun _ => rfl) (fun _ => rfl)
  · obtain ⟨p,W,r,inside⟩ := Green51BCHExceptional.two_tests_floor (k-1) (by omega) L
      ((Submodule.finrank_le _).trans (by simp))
    exact (le_iff_coset (by omega : 0<k) _).mpr ⟨W,p,by omega,inside⟩

theorem moves_of_not_fixed {s t : ℕ} (degree : Module.finrank F K = 2^s*t)
    {b : K} (outside : fr t b ≠ b) (i : ℕ) : fr (2*i+1) b ≠ b := by
  intro fix
  apply outside
  let f (x : K) := x^2
  have whole : Function.IsPeriodicPt f (2^s*t) b := by
    change (fun x : K => x^2)^[2^s*t] b = b
    rw [pow_iterate]
    have sz := Module.card_eq_pow_finrank (K:=F) (V:=K)
    rw [ZMod.card,degree] at sz
    rw [←sz];exact FiniteField.pow_card b
  have small : Function.IsPeriodicPt f (2*i+1) b := by
    change (fun x : K => x^2)^[2*i+1] b=b
    rw [pow_iterate];exact fix
  have cop : (2*i+1).Coprime (2^s) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm,Nat.prime_two.coprime_iff_not_dvd]
    omega
  have div : Function.minimalPeriod f b ∣ t :=
    (cop.coprime_dvd_left small.minimalPeriod_dvd).dvd_of_dvd_mul_left whole.minimalPeriod_dvd
  have fixed : Function.IsPeriodicPt f t b := Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr div
  change (fun x : K => x^2)^[t] b=b at fixed
  rw [pow_iterate] at fixed
  exact fixed

theorem moves_of_dyadic {d : ℕ} (degree : Module.finrank F K = 2^d)
    {b : K} (n0 : b ≠ 0) (n1 : b ≠ 1) (i : ℕ) : fr (2*i+1) b ≠ b := by
  apply moves_of_not_fixed (s:=d) (t:=1) (by simpa using degree) _ i
  intro h
  have idem : b^2=b := h
  exact n1 ((mul_eq_left₀ n0).mp (by simpa [sq] using idem))

/-- In every extension of dyadic degree at least four, each surjective pair attains exactly half the degree. -/
theorem surjective_dyadic {d : ℕ} (hd : 0<d) (degree : Module.finrank F K = 2^(d+1))
    (L : K →ₗ[F] F×F) (onto : Function.Surjective L) :
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L))=2^d := by
  let T:=Algebra.trace F K
  obtain ⟨a,fa⟩ := represent T (Algebra.trace_ne_zero F K) ((LinearMap.fst F F F).comp L)
  obtain ⟨c,fc⟩ := represent T (Algebra.trace_ne_zero F K) ((LinearMap.snd F F F).comp L)
  obtain ⟨x,hx⟩:=onto (1,0)
  obtain ⟨y,hy⟩:=onto (0,1)
  have x1 : T (a*x)=1 := (fa x).symm.trans (congrArg Prod.fst hx)
  have x0 : T (c*x)=0 := (fc x).symm.trans (congrArg Prod.snd hx)
  have y1 : T (c*y)=1 := (fc y).symm.trans (congrArg Prod.snd hy)
  have na : a≠0 := by rintro rfl;simp at x1
  have nc : c≠0 := by rintro rfl;simp at y1
  have ca : c≠a := by rintro rfl;exact zero_ne_one (x0.symm.trans x1)
  have norm : a*(c/a)=c := by field_simp
  have eq : L=twoTraces T a (a*(c/a)) := by
    rw [norm];ext z
    · exact fa z
    · exact fc z
  rw [eq]
  have enough : 2≤2^d := (Nat.pow_le_pow_right (by decide : 0<2) hd : 2^1≤2^d)
  exact exact_of_moves enough (by simpa [pow_succ',Nat.mul_comm] using degree) na
    (fun i => moves_of_dyadic degree (div_ne_zero nc na) (fun h => ca ((div_eq_one_iff_eq na).mp h)) i.val)

theorem scalars_in_subfield {H : Type*} [AddCommGroup H] [Module F H] [Module.Finite F H]
    {k s t : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k) (factors : 2*k=2^s*t)
    (L : K →ₗ[F] H) (large :
      k < maxCosetDim F (Space K × H) (Set.range (lifted L)+Set.range (lifted L))) :
    ∃ a : K, a≠0 ∧ ∀ l : L.dualMap.range, ∃ c : K,
      fr t c=c ∧ ∀ z : K, l.val z = Algebra.trace F K ((a*c)*z) := by
  by_cases hL : L=0
  · refine ⟨1,one_ne_zero,?_⟩
    rintro ⟨l,g,rfl⟩
    exact ⟨0,map_zero _,fun z => by simp [hL]⟩
  obtain ⟨z,hz⟩ : ∃ z,L z≠0 := by contrapose! hL;ext x;exact hL x
  obtain ⟨f,one⟩ := Module.Projective.exists_dual_eq_one F hz
  obtain ⟨a,ha⟩ := represent (Algebra.trace F K) (Algebra.trace_ne_zero F K) (f.comp L)
  have na : a≠0 := by
    rintro rfl
    have eq:=ha z
    simp [one] at eq
  refine ⟨a,na,?_⟩
  rintro ⟨l,g,rfl⟩
  obtain ⟨v,hv⟩ := represent (Algebra.trace F K) (Algebra.trace_ne_zero F K) (g.comp L)
  have cancel : a*(v/a)=v := by field_simp
  refine ⟨v/a,?_,fun z => by rw [cancel];exact hv z⟩
  by_contra moves
  have bound := projected_ceiling hk degree L na
    (fun i => moves_of_not_fixed (degree.trans factors) moves i.val)
    f g ha (fun z => by rw [cancel];exact hv z)
  omega

open Polynomial in
theorem rank_ceiling {H : Type*} [AddCommGroup H] [Module F H] [Module.Finite F H]
    {k s t : ℕ} (hk : 2≤k) (ht : 0<t) (degree : Module.finrank F K=2*k)
    (factors : 2*k=2^s*t) (L : K →ₗ[F] H) (large :
      k < maxCosetDim F (Space K × H) (Set.range (lifted L)+Set.range (lifted L))) :
    Module.finrank F L.range ≤ t := by
  classical
  obtain ⟨a,_,all⟩ := scalars_in_subfield hk degree factors L large
  choose c fixed rep using all
  have inj : Function.Injective c := by
    intro x y eq
    apply Subtype.ext
    ext z
    rw [rep x,rep y,eq]
  let P : K[X] := X^(2^t)-X
  have big : 1<2^t := Nat.one_lt_pow (by omega) (by decide)
  have deg : P.natDegree=2^t := by
    rw [show P=X^(2^t)-X from rfl,natDegree_sub_eq_left_of_natDegree_lt (by simpa using big)]
    simp
  have np : P≠0 := by intro zero;rw [zero,natDegree_zero] at deg;omega
  have sub : ∀ x,c x∈P.roots.toFinset := by
    intro x
    rw [Multiset.mem_toFinset,mem_roots np]
    change P.eval (c x)=0
    simp [P,← fr_apply (K:=K),fixed]
  let ι (x : L.dualMap.range) : P.roots.toFinset := ⟨c x,sub x⟩
  let _ : Finite L.dualMap.range := Finite.of_injective ι (fun x y eq => inj (congrArg Subtype.val eq))
  let _ : Fintype L.dualMap.range := Fintype.ofFinite _
  have count:=Fintype.card_le_of_injective ι (fun x y eq => inj (congrArg Subtype.val eq))
  rw [Fintype.card_coe,Module.card_eq_pow_finrank (K:=F),ZMod.card,L.finrank_range_dualMap_eq_finrank_range]
    at count
  have limit:=count.trans (P.roots.toFinset_card_le.trans P.card_roots')
  rw [deg] at limit
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp limit

end Green51FrobeniusPencil

#print axioms Green51FrobeniusPencil.projected_ceiling
#print axioms Green51FrobeniusPencil.exact_of_moves
#print axioms Green51FrobeniusPencil.moves_of_not_fixed
#print axioms Green51FrobeniusPencil.moves_of_dyadic
#print axioms Green51FrobeniusPencil.surjective_dyadic
#print axioms Green51FrobeniusPencil.scalars_in_subfield
#print axioms Green51FrobeniusPencil.rank_ceiling
