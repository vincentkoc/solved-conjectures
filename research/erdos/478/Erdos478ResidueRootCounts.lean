import Erdos478LocalRootReduction
import Erdos478LocalFrobeniusLift

/-! # Equality of modular root counts and fixed-root counts for one Frobenius lift -/

namespace Erdos478.LocalWitness
open NumberField Ideal Polynomial Function
open scoped Classical
noncomputable section

theorem map_integer_poly {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (f : ℤ[X]) :
    (f.map (Int.castRingHom A)).map φ=f.map (Int.castRingHom B) := by
  rw [Polynomial.map_map,RingHom.ext_int (φ.comp (Int.castRingHom A)) (Int.castRingHom B)]

theorem map_integer_eval {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (f : ℤ[X]) (a : A) :
    φ ((f.map (Int.castRingHom A)).eval a)=(f.map (Int.castRingHom B)).eval (φ a) := by
  rw [← Polynomial.eval_map_apply,map_integer_poly]

/-- Among roots in an extension, Frobenius fixes exactly the roots from the prime field. -/
def primeFixedRoots {p : ℕ} [Fact p.Prime] {R : Type*} [Field R] (ι : ZMod p →+* R)
    (f : (ZMod p)[X]) (hm : f.Monic) :
    Roots f ≃ {x : Roots (f.map ι) // x.val^p=x.val} := by
  let F (a : Roots f) : {x : Roots (f.map ι) // x.val^p=x.val} :=
    ⟨⟨ι a.val,(mem_root_values (hm.map _) _).mpr (by
      rw [IsRoot.def,eval_map_apply,show f.eval a.val=0 from (mem_root_values hm _).mp a.prop,map_zero])⟩,
      (pow_fixed_iff ι _).mpr ⟨a.val,rfl⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro a b he
    have h := congrArg (fun z : {x : Roots (f.map ι) // x.val^p=x.val} => z.val.val) he
    exact Subtype.ext (ι.injective h)
  · rintro ⟨x,hx⟩
    obtain ⟨a,ha⟩ := (pow_fixed_iff ι _).mp hx
    have root := (mem_root_values (hm.map _) _).mp x.prop
    have rz : f.eval a=0 := ι.injective (by rw [← eval_map_apply,ha,map_zero]; exact root)
    exact ⟨⟨a,(mem_root_values hm _).mpr rz⟩,Subtype.ext (Subtype.ext ha)⟩

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- A lift inducing the p-th power bijects its fixed characteristic-zero roots with
the prime-field roots of *each* split monic polynomial of separable reduction. -/
theorem residue_fixed_count (J : Ideal (𝓞 K)) [J.IsMaximal] [J.LiesOver (span {(p:ℤ)})]
    (σ : K ≃ₐ[ℚ] K) (frob : ∀ z : 𝓞 K, Ideal.Quotient.mk J (σ • z)=(Ideal.Quotient.mk J z)^p)
    (f : ℤ[X]) (hm : f.Monic) (sep : (f.map (Int.castRingHom K)).Separable)
    (sp : (f.map (Int.castRingHom K)).Splits) (reg : (f.map (Int.castRingHom (ZMod p))).Separable) :
    Nat.card {x : Roots (f.map (Int.castRingHom K)) // σ x.val=x.val}=
      Nat.card (Roots (f.map (Int.castRingHom (ZMod p)))) := by
  let O := 𝓞 K
  let R := O ⧸ J
  let _ : Field R := Ideal.Quotient.field J
  let π := Ideal.Quotient.mk J
  let ι := residueEmbedding J (p:=p)
  let fo := f.map (Int.castRingHom O)
  let fp := f.map (Int.castRingHom (ZMod p))
  let fk := f.map (Int.castRingHom K)
  have poly : fo.map π=fp.map ι := (map_integer_poly π f).trans (map_integer_poly ι f).symm
  have sepR : (fo.map π).Separable := poly ▸ reg.map
  let red := reduceRoots π fo (hm.map _) (integral_root_count K f hm sep sp) sepR
  let inc := integralRootEquiv K f hm
  have atRed (z : Roots fo) : (red z).val=π z.val := rfl
  let φ := RingOfIntegers.mapRingHom σ.toRingHom
  have σroot (z : Roots fo) : φ z.val∈fo.roots.toFinset := by
    apply (mem_root_values (hm.map _) _).mpr
    change (f.map (Int.castRingHom O)).eval (φ z.val)=0
    rw [← map_integer_eval,show (f.map (Int.castRingHom O)).eval z.val=0 from (mem_root_values (hm.map _) _).mp z.prop,map_zero]
  have reduceFix (z : Roots fo) : φ z.val=z.val ↔ (red z).val^p=(red z).val := by
    have comm : π (φ z.val)=(π z.val)^p := frob z.val
    rw [atRed,← comm]
    refine ⟨congrArg π,fun he => ?_⟩
    let w : Roots fo := ⟨φ z.val,σroot z⟩
    exact congrArg Subtype.val (red.injective (show red w=red z from Subtype.ext he))
  have incFix (z : Roots fo) : φ z.val=z.val ↔ σ (inc z).val=(inc z).val :=
    ⟨fun eq => congrArg (fun u : O => (u:K)) eq,fun eq => Subtype.ext eq⟩
  calc
    Nat.card {x : Roots fk // σ x.val=x.val} = Nat.card {z : Roots fo // φ z.val=z.val} :=
      (Nat.card_congr (inc.subtypeEquiv incFix)).symm
    _ = Nat.card {x : Roots (fo.map π) // x.val^p=x.val} := Nat.card_congr (red.subtypeEquiv reduceFix)
    _ = Nat.card {x : Roots (fp.map ι) // x.val^p=x.val} := by rw [poly]
    _ = Nat.card (Roots fp) := (Nat.card_congr (primeFixedRoots ι fp (hm.map _))).symm

#print axioms map_integer_poly
#print axioms map_integer_eval
#print axioms primeFixedRoots
#print axioms residue_fixed_count
end
end Erdos478.LocalWitness
