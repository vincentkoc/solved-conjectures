import Green51GoldForms
import Green51LocalFlats

/-! # Normalizing the coefficients of a simultaneous trace flat -/

namespace Green51TraceScaling
open Green51GoldForms Green51BCHCompression
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
open Green51BCH Green51BCHOptimality Green51LocalFlats
open scoped Pointwise

theorem scaled_flat_iff_of_cube (Q : K →ₗ[F] F) (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z)
    {d : ℕ} (hd : 3≤d)
    {a : K} (na : a ≠ 0) (b : K)
    (cube : ∀ t : K,t≠0 → ∀ A : Submodule F K, Module.finrank F A=d →
      (∀ x∈A,∀ y∈A,Q ((a*t^7)*bracket x y)=0) → ∃ s : K,s^3=a*t^7) :
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
    obtain ⟨s,cs⟩ := cube t nt A (by omega) (by
      intro x hx y hy
      have one := congrArg Prod.fst (iso x hx y hy)
      change Q (a*(t^7*bracket x y))=0 at one
      simpa only [mul_assoc] using one)
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


end Green51TraceScaling

#print axioms Green51TraceScaling.scaled_flat_iff_of_cube
