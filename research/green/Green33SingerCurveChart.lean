import Green33PrimeSingerIncidence
import Mathlib.LinearAlgebra.Dual.Lemmas
/-! Affine coordinates on the cyclic Singer plane, with the sign convention for an odd layer. -/
open Finset Green33PrimeSingerIncidence
open scoped Pointwise
namespace Green33SingerCurveChart
variable {F K G : Type*} [Field F] [Field K] [Algebra F K] [AddCommGroup G]
variable {D : Finset G}

/-- An affine chart in the opposite layer. A line of center c consists of the
labels z satisfying c-z∈D. The complement of the affine chart lies at infinity. -/
structure Chart (F G : Type*) [Field F] [AddCommGroup G] (D : Finset G) where
  point : F×F ↪ G
  infinity : G
  off : ∀ z,z∉Set.range point → infinity-z∈D
  vertical : F→G
  onVertical : ∀ a p,vertical a-point p∈D ↔ p.1=a
  oblique : F×F→G
  onOblique : ∀ l p,oblique l-point p∈D ↔ p.2=l.1*p.1+l.2
  equation : ∀ c:G,(∀ p,c-point p∉D) ∨
    (∃ a,∀ p,c-point p∈D → p.1=a) ∨ ∃ l:F×F,∀ p,c-point p∈D → p.2=l.1*p.1+l.2

private noncomputable def pairing (L : K→ₗ[F] F) : K→ₗ[F] Module.Dual F K where
  toFun u := L.comp (Algebra.lmul F K u)
  map_add' u v := by ext x;simp
  map_smul' a u := by ext x;simp

private theorem pairing_surj [FiniteDimensional F K] (L : K→ₗ[F] F) (onto : Function.Surjective L) :
    Function.Surjective (pairing L) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_contra nz
  obtain ⟨v,hv⟩:=onto 1
  have eq:=congrArg (fun R : Module.Dual F K => R (v/a)) ha
  change L (a*(v/a))=0 at eq
  rw [show a*(v/a)=v by field_simp,hv] at eq
  exact one_ne_zero eq

private theorem center_for [FiniteDimensional F K] (S : SingerMap F K D)
    (M : Module.Dual F K) (ne : M≠0) :
    ∃ c:G,∀ a:Kˣ,c+S.tag a∈D ↔ M a=0 := by
  obtain ⟨u,hu⟩:=pairing_surj S.form S.onto M
  have nz : u≠0 := fun z => ne (hu.symm.trans (z ▸ map_zero _))
  let w:=Units.mk0 u nz
  refine ⟨S.tag w,fun a => ?_⟩
  rw [←S.mul,S.mem,←hu]
  rfl

private def proj (e : K≃ₗ[F](Fin 3→F)) (i : Fin 3) : Module.Dual F K :=
  (LinearMap.proj i).comp e.toLinearMap

noncomputable def singerChart [FiniteDimensional F K] (S : SingerMap F K D) (e : K≃ₗ[F](Fin 3→F)) :
    Chart F G D := by
  classical
  let a (p : F×F) : K := e.symm ![1,p.1,p.2]
  have nz (p) : a p≠0 := by
    intro h;have hh:=congrArg (fun t:K => e t 0) h
    simp [a] at hh
  let U (p) := Units.mk0 (a p) (nz p)
  let pt (p) := -S.tag (U p)
  have inj : Function.Injective pt := by
    intro p q eq
    obtain ⟨r,hr⟩:=(S.same _ _).mp (neg_inj.mp eq)
    have he:=congrArg e hr
    change e (a p)=e (r • a q) at he
    simp only [a,map_smul,LinearEquiv.apply_symm_apply] at he
    have one:=congrFun he 0
    have rr:r=1 := by simpa using one.symm
    rw [rr,one_smul] at he
    exact Prod.ext (congrFun he 1) (congrFun he 2)
  let P (i : Fin 3) := proj e i
  let dual (u v w : F) := u • P 0 + v • P 1 + w • P 2
  have ev (u v w : F) (z : K) : dual u v w z=u*(e z 0)+v*(e z 1)+w*(e z 2) := rfl
  let M:=P 0
  have mn:M≠0 := by
    intro z;have h:=congrArg (fun f:Module.Dual F K => f (a (0,0))) z
    change e (a (0,0)) 0=0 at h; simp [a] at h
  let inf:=(center_for S M mn).choose
  have hinf:= (center_for S M mn).choose_spec
  have ve (b : F) : dual (-b) 1 0≠0 := by
    intro z;have h:=congrArg (fun f:Module.Dual F K => f (e.symm ![0,1,0])) z
    change dual _ _ _ _=0 at h; simp [ev] at h
  have oe (l : F×F) : dual (-l.2) (-l.1) 1≠0 := by
    intro z;have h:=congrArg (fun f:Module.Dual F K => f (e.symm ![0,0,1])) z
    change dual _ _ _ _=0 at h; simp [ev] at h
  choose vert hv using fun b => center_for S _ (ve b)
  choose obl ho using fun l => center_for S _ (oe l)
  refine ⟨⟨pt,inj⟩,inf,?_,vert,?_,obl,?_,?_⟩
  · intro z outside
    obtain ⟨k,hk⟩:=S.surj (-z)
    by_cases zero:e (k:K) 0=0
    · have eq : inf-z=inf+S.tag k := by rw [hk,sub_eq_add_neg]
      exact eq ▸ (hinf k).mpr zero
    · exfalso;apply outside
      let p:F×F := (e (k:K) 1/e (k:K) 0,e (k:K) 2/e (k:K) 0)
      refine ⟨p,?_⟩
      change -S.tag (U p)=z
      rw [neg_eq_iff_eq_neg,←hk]
      apply (S.same _ _).mpr
      refine ⟨(e (k:K) 0)⁻¹,?_⟩
      apply e.injective
      change e (a p)=_
      rw [map_smul]
      funext i;fin_cases i <;> simp [a,p,zero,div_eq_inv_mul]
  · intro b p
    change vert b-(-S.tag (U p))∈D ↔ _
    rw [sub_neg_eq_add,hv]
    change dual _ _ _ (a p)=0 ↔ _
    rw [ev];simp [a];constructor <;> intro e <;> linear_combination e
  · intro l p
    change obl l-(-S.tag (U p))∈D ↔ _
    rw [sub_neg_eq_add,ho]
    change dual _ _ _ (a p)=0 ↔ _
    rw [ev];simp [a];constructor <;> intro e <;> linear_combination e
  · intro c
    obtain ⟨r,hr⟩:=S.surj c
    let L:Module.Dual F K:=pairing S.form (r:K)
    let u:=L (e.symm ![1,0,0])
    let v:=L (e.symm ![0,1,0])
    let w:=L (e.symm ![0,0,1])
    have decomp (z:K) : z = (e z 0) • e.symm ![1,0,0]+(e z 1) • e.symm ![0,1,0]+(e z 2) • e.symm ![0,0,1] := by
      apply e.injective
      simp only [map_add,map_smul,LinearEquiv.apply_symm_apply]
      funext i;fin_cases i <;> simp
    have form (z:K) : L z=(e z 0)*u+(e z 1)*v+(e z 2)*w := by
      calc L z = _ := congrArg L (decomp z)
           _ = _ := by simp [u,v,w]
    have hi (p) : c-pt p∈D ↔ u+p.1*v+p.2*w=0 := by
      change c-(-S.tag (U p))∈D ↔ _
      rw [sub_neg_eq_add,←hr,←S.mul,S.mem]
      change L (a p)=0 ↔ _
      rw [form];simp [a]
    by_cases wn:w=0
    · by_cases vn:v=0
      · left;intro p hp
        have h:= (hi p).mp hp
        rw [wn,vn] at h
        have zu:u=0:=by simpa using h
        obtain ⟨k,hk⟩:=S.onto 1
        have zero:=form (k/(r:K))
        simp only [zu,vn,wn,mul_zero,add_zero] at zero
        change S.form ((r:K)*(k/(r:K)))=0 at zero
        rw [show (r:K)*(k/(r:K))=k by field_simp,hk] at zero
        exact one_ne_zero zero
      · right;left;refine ⟨-u/v,fun p hp => ?_⟩
        have eq:= (hi p).mp hp
        apply (eq_div_iff vn).mpr;rw [wn] at eq;linear_combination eq
    · right;right;refine ⟨(-v/w,-u/w),fun p hp => ?_⟩
      have eq:= (hi p).mp hp
      field_simp [wn];linear_combination eq

#print axioms singerChart
end Green33SingerCurveChart
