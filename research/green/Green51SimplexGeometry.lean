import Green51QuadraticDirections
import Green51SimplexModel

/-! # Linear actions on the fifteen-point binary configuration -/

open Finset Green50Downsets Green51SystematicChecks
open scoped Pointwise
open Green51SimplexDirections
namespace Green51SimplexGeometry
local notation "F" => ZMod 2
local notation "V" => Cube 10

theorem point_xor (v r : ℕ) : point 10 (v ^^^ r)=point 10 v+point 10 r := by
  funext i
  cases h:v.testBit i.val <;> cases j:r.testBit i.val <;>
    simp [point,Nat.testBit_xor,h,j,show (1:F)+1=0 by decide]

def columnMap (cs : List ℕ) : Cube cs.length →ₗ[F] V :=
  Fintype.linearCombination F (fun i => point 10 cs[i])

theorem columns_eval (cs : List ℕ) (x : ℕ) :
    columnMap cs (point cs.length x)=point 10 (matrix cs x) := by
  induction cs generalizing x with
  | nil =>
    ext i
    simp [columnMap,Fintype.linearCombination_apply,matrix,point]
  | cons a cs ih =>
    rw [matrix,point_xor]
    change (∑ i : Fin (cs.length+1), point (cs.length+1) x i • point 10 ((a::cs)[i])) = _
    rw [Fin.sum_univ_succ]
    have tail (i:Fin cs.length) : point (cs.length+1) x i.succ=point cs.length (x/2) i := by
      simp only [point,Fin.val_succ]
      rw [←Nat.shiftRight_one, Nat.testBit_shiftRight]
      rw [Nat.add_comm 1]
    simp only [tail]
    change point (cs.length+1) x 0 • point 10 a + columnMap cs (point cs.length (x/2)) = _
    rw [ih]
    by_cases odd : x%2=1
    · simp [point,Nat.testBit_zero,odd]
    · have pzero : point 10 0=0 := by funext i; simp [point]
      simp [point,Nat.testBit_zero,odd,pzero]


private theorem inj_of_units (L I : V →ₗ[F] V) (check : ∀ i : Fin 10,
    I (L (Pi.single i 1))=Pi.single i 1) : Function.Injective L := by
  have eq : I.comp L=LinearMap.id := (Pi.basisFun F (Fin 10)).ext (fun i => by
    simpa using check i)
  exact Function.LeftInverse.injective (fun x => LinearMap.congr_fun eq x)

def firstMap : V →ₗ[F] V := columnMap [18,66,258,2,3,6,10,34,130,514]
def secondMap : V →ₗ[F] V := columnMap [681,687,684,653,701,677,749,173,941,557]

theorem first_injective : Function.Injective firstMap :=
  inj_of_units firstMap (columnMap [24,8,40,72,9,136,10,264,12,520]) (by decide +kernel)

theorem second_injective : Function.Injective secondMap :=
  inj_of_units secondMap secondMap (by decide +kernel)

open Green51SimplexSection in
private theorem preserves_double (L : V →ₗ[F] V) (t:V)
    (perm : ∀ x∈model,L x+t∈model) {z : V} (hz : z∈model+model) : L z∈model+model := by
  obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hz
  exact mem_add.mpr ⟨_,perm x hx,_,perm y hy,by rw [map_add,add_add_add_comm (L x) t (L y) t,ZModModule.add_self,add_zero]⟩

open Green51SimplexSection in
private theorem in_model {x : V} : x∈model ↔ ∃ u∈units++extras, point 10 u=x := by
  simp only [model,mem_union,mem_rows,List.mem_append]
  aesop

open Green51SimplexSection in
private theorem preserves_list (L : V →ₗ[F] V) (f : ℕ→ℕ) (t : ℕ)
    (act : ∀ x, L (point 10 x)=point 10 (f x)) (check :
      (units++extras).all (fun x => (units++extras).contains (f x ^^^ t))=true) :
    ∀ x∈model, L x+point 10 t∈model := by
  intro x hx
  obtain ⟨u,hu,rfl⟩ := in_model.mp hx
  rw [act,←point_xor]
  exact in_model.mpr ⟨_,by simpa using List.all_eq_true.mp check u hu,rfl⟩

open Green51SimplexSection in
theorem first_double {z : V} (hz : z∈model+model) : firstMap z∈model+model :=
  preserves_double firstMap _ (preserves_list firstMap first 2 (columns_eval _) (by decide +kernel)) hz

open Green51SimplexSection in
theorem second_double {z : V} (hz : z∈model+model) : secondMap z∈model+model :=
  preserves_double secondMap _ (preserves_list secondMap second 685 (columns_eval _) (by decide +kernel)) hz

end Green51SimplexGeometry
#print axioms Green51SimplexGeometry.columns_eval

#print axioms Green51SimplexGeometry.first_injective
#print axioms Green51SimplexGeometry.second_injective
#print axioms Green51SimplexGeometry.first_double
#print axioms Green51SimplexGeometry.second_double
