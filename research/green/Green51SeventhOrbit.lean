import Green51SeventhOrbitWords
import Green50Downsets
import Mathlib.FieldTheory.Finite.GaloisField
open Green50Downsets Polynomial
namespace Green51SeventhOrbit
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [Algebra F K]

private def pair (u v : Cube 3) : F := ∑ i, u i * v i

private theorem four_tests (v : Cube 3) :
    (∑ u : Cube 3, (decide (pair u v = 1)).toNat) = if v=0 then 0 else 4 := by
  exact (by decide +kernel : ∀ w : Cube 3, (∑ u : Cube 3, (decide (pair u w=1)).toNat) =
    if w=0 then 0 else 4) v

private theorem test_weight {b : K} (hb : b^9=b+1) (L : K →ₗ[F] Cube 3) (u : Cube 3) :
    ∑ i ∈ Finset.range 73, (decide (pair u (L (b^i))=1)).toNat ≤ 40 := by
  let s := fun i : ℕ => decide (pair u (L (b^i))=1)
  have shift (i : ℕ) : s (i+9)=(s i ^^ s (i+1)) := by
    have eq : b^(i+9)=b^i+b^(i+1) := by rw [pow_add,hb,pow_succ];ring
    have plus (x y : Cube 3) : pair u (x+y)=pair u x+pair u y := by
      simp [pair, mul_add,Finset.sum_add_distrib]
    dsimp [s]
    rw [eq,map_add,plus]
    exact (by decide +kernel : ∀ a b : F, decide (a+b=1) = (decide (a=1) ^^ decide (b=1))) _ _
  simpa [s] using recurrence_weight s shift 0

theorem orbit_hits {b : K} (hb : b^9=b+1) (L : K →ₗ[F] Cube 3) :
    3 ≤ ((Finset.range 73).filter fun i => L (b^i)=0).card := by
  classical
  let row := fun (u : Cube 3) (i : ℕ) => (decide (pair u (L (b^i))=1)).toNat
  have all (u : Cube 3) : ∑ i ∈ Finset.range 73,row u i ≤ if u=0 then 0 else 40 := by
    split_ifs with h
    · subst u;simp [row,pair]
    · exact test_weight hb L u
  have bound := Finset.sum_le_sum (s:=Finset.univ) (fun u _ => all u)
  have total : (∑ u : Cube 3, if u=0 then 0 else 40 : ℕ)=280 := by decide +kernel
  rw [total,Finset.sum_comm] at bound
  change ∑ i ∈ Finset.range 73,(∑ u : Cube 3, (decide (pair u (L (b^i))=1)).toNat) ≤ 280 at bound
  simp_rw [four_tests] at bound
  have identity : (∑ i ∈ Finset.range 73, if L (b^i)=0 then 0 else 4 : ℕ) =
      4*((Finset.range 73).filter fun i => L (b^i)≠0).card := by
    simp [Finset.sum_ite,Nat.mul_comm]
  rw [identity] at bound
  have count := Finset.card_filter_add_card_filter_not (s:=Finset.range 73) (fun i => L (b^i)=0)
  change ((Finset.range 73).filter fun i => L (b^i)=0).card +
    ((Finset.range 73).filter fun i => L (b^i)≠0).card = 73 at count
  omega
variable [CharP K 2] [Fintype K]

set_option maxRecDepth 10000 in
/-- A root of X⁹+X+1 in the field of order 512 has period 73. -/
theorem orbit_root (size : Fintype.card K = 512) :
    ∃ b : K, b^9=b+1 ∧ b^73=1 := by
  let f : K[X] := X^9+X+1
  have split : (X^512-X : K[X]).Splits := by
    simpa only [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,size] using FiniteField.splits_X_pow_card_sub_X (K:=K) 2
  have eighth (x y : K[X]) : (x+y)^8=x^8+y^8 := by
    simpa using add_pow_expChar_pow x y 2 3
  have identity : X^73-1=f*(X*f^7+1) := by
    calc X^73-1 = X*f^8+f := by
           simp only [f,eighth,one_pow,←pow_mul]
           rw [CharTwo.sub_eq_add]
           ring_nf
           simp [CharTwo.two_eq_zero]
         _ = _ := by ring
  have divisor : f ∣ X^512-X := by
    have d := sub_one_dvd_pow_sub_one (X^73:K[X]) 7
    rw [← pow_mul] at d
    have mul : (X^511-1 : K[X]) ∣ X^512-X := ⟨X,by ring⟩
    exact dvd_trans ⟨_,identity⟩ (dvd_trans d mul)
  have deg : f.natDegree=9 := by dsimp [f];compute_degree!
  obtain ⟨b,root⟩ := (split.of_dvd (by rw [← size]; exact FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card) divisor).exists_eval_eq_zero
    (by intro h; have hn := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h.le; omega)
  refine ⟨b,?_,?_⟩
  · have zero : b^9+(b+1)=0 := by simpa [f,add_assoc] using root
    exact CharTwo.add_eq_zero.mp zero
  · have eq := congrArg (Polynomial.eval b) identity
    simpa [root,sub_eq_zero] using eq

/-- Every binary subspace of codimension at most three in the field of
order 512 contains at least three distinct nonzero seventh powers. -/
theorem three_seventh_powers (L : K →ₗ[F] Cube 3) (dim : Module.finrank F K=9) :
    3 ≤ {x : K | x≠0 ∧ (∃ a : K, a^7=x) ∧ L x=0}.ncard := by
  classical
  have size : Fintype.card K=512 := by rw [Module.card_eq_pow_finrank (K:=F),ZMod.card,dim]; decide
  obtain ⟨b,rel,period⟩ := orbit_root (K:=K) size
  have nz : b≠0 := by intro z;simp [z] at period
  have : Fact (Nat.Prime 73) := ⟨by decide⟩
  have ord : orderOf b=73 := orderOf_eq_prime period (by rintro rfl; simp at rel)
  have h : (b^21)^7=b := by
    rw [←pow_mul, show 21*7=73*2+1 by decide,pow_succ,pow_mul,period,one_pow,one_mul]
  let S := (Finset.range 73).filter fun i => L (b^i)=0
  have inj : Set.InjOn (fun i : ℕ => b^i) (S : Set ℕ) :=
    pow_injOn_Iio_orderOf.mono (fun i hi => show i<orderOf b by
      rw [ord];exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
  have sub : (↑(S.image fun i => b^i) : Set K) ⊆
      {x : K | x≠0 ∧ (∃ a : K, a^7=x) ∧ L x=0} := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    refine ⟨pow_ne_zero _ nz,⟨(b^21)^i,?_⟩,(Finset.mem_filter.mp hi).2⟩
    rw [←pow_mul,Nat.mul_comm i 7,pow_mul,h]
  have bound := Set.ncard_le_ncard sub
  rw [Set.ncard_coe_finset,Finset.card_image_of_injOn inj] at bound
  exact (orbit_hits rel L).trans bound

theorem seventh_meets_nine (L : K →ₗ[F] Cube 3) (dim : Module.finrank F K=9) :
    ∃ a : K, a≠0 ∧ L (a^7)=0 := by
  have bound := three_seventh_powers L dim
  obtain ⟨x,nz,⟨a,rfl⟩,zero⟩ := (Set.ncard_pos (Set.toFinite _)).mp (lt_of_lt_of_le (by decide : 0<3) bound)
  exact ⟨a,fun h => nz (by simp [h]),zero⟩

end Green51SeventhOrbit

#print axioms Green51SeventhOrbit.orbit_hits
#print axioms Green51SeventhOrbit.orbit_root
#print axioms Green51SeventhOrbit.three_seventh_powers
#print axioms Green51SeventhOrbit.seventh_meets_nine
