import Green51GoldForms
import Green51LocalFlats

/-! # Rescaling odd-degree BCH flats and their forced coefficient vectors -/

open Green51GoldForms Green51BCHCompression
namespace Green51OddTrace
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

omit [CharP K 2] in
private theorem units_coprime_three (k : ℕ) (degK : Module.finrank F K = 2*k+1) :
    (Nat.card Kˣ).Coprime 3 := by
  rw [Nat.card_units,Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=F),ZMod.card,degK]
  rw [Nat.coprime_comm,(by decide : Nat.Prime 3).coprime_iff_not_dvd]
  intro dvd
  have h := (ZMod.natCast_eq_zero_iff _ 3).mpr dvd
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)) : 1 ≤ 2^(2*k+1)),Nat.cast_pow,Nat.cast_ofNat,
    Nat.cast_one,pow_succ,pow_mul,show (2:ZMod 3)^2=1 by decide,one_pow,one_mul] at h
  exact (by decide : (2:ZMod 3)-1≠0) h

omit [CharP K 2] [Algebra F K] in
private theorem cube_bijective (coprime : (Nat.card Kˣ).Coprime 3) : Function.Bijective (fun z : K => z^3) := by
  have surj : ∀ z : K, ∃ x : K, x^3=z := by
    intro z
    by_cases eq : z=0
    · exact ⟨0,by simp [eq]⟩
    obtain ⟨x,h⟩ := (powCoprime coprime).surjective (Units.mk0 z eq)
    exact ⟨x,congrArg (fun u : Kˣ => (u:K)) h⟩
  exact ⟨Finite.injective_iff_surjective.mpr surj,surj⟩

omit [CharP K 2] in
theorem odd_cube_bijective {k : ℕ} (degree : Module.finrank F K = 2*k+1) :
    Function.Bijective (fun z : K => z^3) :=
  cube_bijective (units_coprime_three k degree)

/-- Each member of a normalized polynomial chain belongs to every common isotropic space
of the largest possible dimension. -/
theorem forced (Q : K →ₗ[F] F) (nQ : Q ≠ 0) (sq : ∀ z,Q (z^2)=Q z)
    {k : ℕ} (degK : Module.finrank F K=2*k+1) (b : K) (u : ℕ → K)
    (start : u 0=1) (step : ∀ i<k, (u (i+1))^4+u (i+1)=b^2*(u i)^4+b*u i)
    (U : Submodule F K) (large : k+1 ≤ Module.finrank F U)
    (iso : ∀ x∈U,∀ y∈U,Q (bracket x y)=0)
    (iso' : ∀ x∈U,∀ y∈U,Q (b*bracket x y)=0) : ∀ i≤k, u i ∈ U := by
  let B := bracketForm Q 1
  have cube := (odd_cube_bijective degK).injective
  have rad : B.ker ≤ Submodule.span F {(1:K)} := by
    intro x hx
    by_cases nx : x=0
    · rw [nx]; exact Submodule.zero_mem _
    have cu : x^3=1 := by simpa using (radical_cube_iff Q nQ sq one_ne_zero nx).mp hx
    rw [show x=1 from cube (cu.trans (one_pow 3).symm)]
    exact Submodule.subset_span (Set.mem_singleton _)
  have rk:=Submodule.finrank_mono ((show U⊓B.ker ≤ B.ker from inf_le_right).trans rad)
  rw [finrank_span_singleton one_ne_zero] at rk
  have bound:=B.finrank_add_finrank_orthogonal' U
  have incl : U ≤ B.orthogonal U := by
    intro u hu x hx
    change Q (1 * bracket x u)=0
    simpa using iso x hx u hu
  have equals : U = B.orthogonal U := Submodule.eq_of_le_of_finrank_le incl (by omega)
  intro i
  induction i with
  | zero =>
    intro _
    rw [start,equals]
    intro x _
    change Q (1*bracket x 1)=0
    rw [one_mul,show bracket x 1=x^2+x by unfold bracket;ring,map_add,sq,CharTwo.add_self_eq_zero]
  | succ i ih =>
    intro hi
    have last := ih (by omega)
    rw [equals]
    intro x hx
    have symmBracket : bracket x (u (i+1))=bracket (u (i+1)) x := by unfold bracket;ring
    have coef (c y : K) : Q (c*bracket y x) = Q ((c^2*y^4+c*y)*x^2) :=
      bracketForm_apply_squared Q sq c y x
    change Q (1*bracket x (u (i+1)))=0
    rw [symmBracket,coef,one_pow,one_mul,one_mul,step i (by omega),←coef]
    exact iso' _ last x hx

open Green51BCH Green51BCHOptimality Green51LocalFlats
open scoped Pointwise

theorem scaled_flat_iff (Q : K →ₗ[F] F) (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z)
    {k : ℕ} (degree : Module.finrank F K=2*k+1) {d : ℕ} (hd : 3≤d)
    {a : K} (na : a ≠ 0) (b : K) :
    let L := twoTraces Q a (a*b)
    d ≤ maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)) ↔
    ∃ U : Submodule F K, Module.finrank F U=d ∧
      (∀ x∈U,∀ y∈U,Q (bracket x y)=0 ∧ Q (b*bracket x y)=0) ∧
      ∃ h : K, h≠0 ∧ ∀ x∈U,Q ((a^2*h^7)*x)=0 := by
  intro L
  have bracket_scale (s x y : K) : bracket (s*x) (s*y)=s^3*bracket x y := by
    unfold bracket
    ring
  rw [le_iff_coset (by omega : 0<d)]
  constructor
  · rintro ⟨W,p,wr,inside⟩
    obtain ⟨t,nt,A,dim,tr,iso⟩ := Green51BracketRank.trace_space_of_flat L p W inside (by omega)
    obtain ⟨s,cs⟩ := (odd_cube_bijective degree).surjective (a*t^7)
    change s^3=a*t^7 at cs
    have ns : s≠0 := by intro h; simp [h,na,nt] at cs
    let f:=LinearMap.mulLeft F s
    let U:=A.map f
    have size := (A.equivMapOfInjective f (fun _ _ e => mul_left_cancel₀ ns e)).finrank_eq
    change Module.finrank F A=Module.finrank F U at size
    refine ⟨U,by omega,?_,t^2*s⁻¹,mul_ne_zero (pow_ne_zero _ nt) (inv_ne_zero ns),?_⟩
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      change Q (bracket (s*x) (s*y))=0 ∧ Q (b*bracket (s*x) (s*y))=0
      rw [bracket_scale,cs]
      have one := congrArg Prod.fst (iso x hx y hy)
      have two := congrArg Prod.snd (iso x hx y hy)
      change Q (a*(t^7*bracket x y))=0 at one
      change Q ((a*b)*(t^7*bracket x y))=0 at two
      constructor
      · simpa only [mul_assoc] using one
      · simpa only [mul_left_comm,mul_comm,mul_assoc] using two
    · rintro _ ⟨x,hx,rfl⟩
      change Q ((a^2*(t^2*s⁻¹)^7)*(s*x))=0
      have pre : a^2*(t^2*s⁻¹)^7 = s⁻¹ := by
        calc
          _ = (a*t^7)^2 * (s⁻¹)^7 := by ring
          _ = s⁻¹ := by rw [←cs];field_simp
      rw [pre,←mul_assoc,inv_mul_cancel₀ ns,one_mul]
      exact (test x).mpr (tr hx)
  · rintro ⟨U,dim,iso,h,nh,trace⟩
    let u:=a^2*h^7
    let t:=(a*h^3)⁻¹
    have nu : u≠0 := mul_ne_zero (pow_ne_zero _ na) (pow_ne_zero _ nh)
    have nt : t≠0 := inv_ne_zero (mul_ne_zero na (pow_ne_zero _ nh))
    have cancel : a*t^7*u^3=1 := by
      dsimp [u,t]
      field_simp
    let f := LinearMap.mulLeft F u
    have size := (U.equivMapOfInjective f (fun _ _ e => mul_left_cancel₀ nu e)).finrank_eq
    change Module.finrank F U = Module.finrank F (U.map f) at size
    obtain ⟨p,W,r,sub⟩ := Green51BracketRank.flat_of_trace_space L t nt (U.map f)
      (by rintro _ ⟨x,hx,rfl⟩; exact (test _).mp (trace x hx)) (by
        rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
        have pair := iso x hx y hy
        apply Prod.ext
        · change Q (a*(t^7*bracket (u*x) (u*y)))=0
          rw [bracket_scale,show a*(t^7*(u^3*bracket x y))=(a*t^7*u^3)*bracket x y by ring,cancel,one_mul]
          exact pair.1
        · change Q ((a*b)*(t^7*bracket (u*x) (u*y)))=0
          rw [bracket_scale,show (a*b)*(t^7*(u^3*bracket x y))=(a*t^7*u^3)*(b*bracket x y) by ring,cancel,one_mul]
          exact pair.2)
    exact ⟨W,p,by omega,sub⟩

end Green51OddTrace

#print axioms Green51OddTrace.odd_cube_bijective
#print axioms Green51OddTrace.forced
#print axioms Green51OddTrace.scaled_flat_iff
