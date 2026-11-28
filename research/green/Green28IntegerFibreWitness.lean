import Green28DeficientFibre
import Mathlib.LinearAlgebra.FreeModule.PID

/-! Simultaneous integral witnesses for the fibre equations of Green 28. -/

namespace Green28IntegerFibreWitness

open Finset Submodule Module Green28 Green28UniformSums Green28DeficientFibre
open scoped ENNReal

/-- A finite-rank integer lattice of real algebraic integers containing one
has an integer linear functional taking one to one. -/
theorem integer_retraction {E : Submodule ℤ ℝ} (fg : E.FG)
    (integers : ∀ x ∈ E, IsIntegral ℤ x) (one : (1:ℝ) ∈ E) :
    ∃ f : E →ₗ[ℤ] ℤ, f ⟨1,one⟩=1 := by
  classical
  let : Module.Finite ℤ E := Module.Finite.iff_fg.mpr fg
  obtain ⟨n,B⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := E)
  let e : E := ⟨1,one⟩
  let A : (E →ₗ[ℤ] ℤ) →ₗ[ℤ] ℤ := LinearMap.applyₗ e
  let J : Ideal ℤ := LinearMap.range A
  let g := Submodule.IsPrincipal.generator J
  have coord (i : Fin n) : g ∣ B.repr e i :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp ⟨B.coord i,rfl⟩
  choose k hk using coord
  let w : E := ∑ i, k i • B i
  have rel : g • w = e := by
    rw [←B.sum_repr e]
    dsimp only [w]
    rw [Finset.smul_sum]
    apply sum_congr rfl
    intro i _
    rw [hk,smul_smul]
  have mul : (g:ℝ)*(w:ℝ) = 1 := by simpa [e,zsmul_eq_mul] using congrArg Subtype.val rel
  have ne : g ≠ 0 := by intro eq; simp [eq] at mul
  have eq : (((1:ℚ)/g:ℚ):ℝ) = w := by push_cast; field_simp; linarith only [mul]
  have wi := integers (w:ℝ) w.property
  rw [←eq] at wi
  have qint := (isIntegral_algebraMap_iff (B := ℝ) (algebraMap ℚ ℝ).injective).mp wi
  obtain ⟨j,hj⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp qint
  have cast : (j:ℝ) = w := by rw [←eq,←hj]; norm_num
  have div : g ∣ 1 := ⟨j,by exact_mod_cast (show (1:ℝ) = g*j from by rw [cast,mul])⟩
  exact (Submodule.IsPrincipal.mem_iff_generator_dvd J).mpr div

/-- A system of integer linear equations in finitely many variables which
has a solution in real algebraic integers already has an integer solution.
The equations can be indexed by an arbitrary type. -/
theorem integer_model {I J : Type*} [Fintype I] (a : J → I → ℤ) (b : J → ℤ)
    (w : I → ℝ) (wi : ∀ i, IsIntegral ℤ (w i))
    (eq : ∀ j, ∑ i, (a j i:ℝ)*w i = (b j:ℝ)) :
    ∃ v : I → ℤ, ∀ j, ∑ i, a j i*v i = b j := by
  classical
  let W : Finset ℝ := insert 1 (Finset.univ.image w)
  let E := Submodule.span ℤ (W:Set ℝ)
  have fg : E.FG := Submodule.fg_span W.finite_toSet
  have one : (1:ℝ) ∈ E := Submodule.subset_span (Finset.mem_insert_self _ _ : (1:ℝ) ∈ W)
  have sub : E ≤ (integralClosure ℤ ℝ).toSubmodule := Submodule.span_le.mpr (by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|h
    · exact isIntegral_one
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h; exact wi i)
  obtain ⟨f,hf⟩ := integer_retraction fg (fun x hx => sub hx) one
  let e : E := ⟨1,one⟩
  let v (i : I) : E := ⟨w i,Submodule.subset_span (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem w (Finset.mem_univ i)) : w i ∈ W)⟩
  refine ⟨fun i => f (v i),fun j => ?_⟩
  have rel : ∑ i, a j i • v i = b j • e := by
    apply Subtype.ext; simpa [e,v,zsmul_eq_mul] using eq j
  have lift := congrArg f rel
  simp only [map_sum,map_smul,e,hf,zsmul_eq_mul,mul_one] at lift
  exact lift

/-- Normalized mass of an occupied cell in an integer convolution. -/
noncomputable def cell (P Q : PMF ℤ) (a b i j : ℤ) : ℝ := weight P a i*weight Q b j

/-- The occupied rows in one output fibre, grouped by the common product mass. -/
noncomputable def colourCount (P Q : PMF ℤ) (a b z : ℤ) (w : ℝ) : ℕ :=
  ({i | i ∈ P.support ∧ z-i ∈ Q.support ∧ cell P Q a b i (z-i) = w}:Set ℤ).ncard

/-- One signed integer per occurring product mass gives the correct fibre
equation simultaneously at every integer output. -/
theorem simultaneous_fibres {P Q : PMF ℤ} {S : Finset ℤ} (sn : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S sn) {a b : ℤ}
    (pa : IsGreatest P.support a) (qb : IsGreatest Q.support b)
    {A B : Finset ℤ} (ps : P.support = ↑A) (qs : Q.support = ↑B) :
    let W := (A×ˢB).image (fun ij => cell P Q a b ij.1 ij.2)
    ∃ v : W → ℤ, ∀ z : ℤ, ∑ w : W, (colourCount P Q a b z w:ℤ)*v w = if z ∈ S then 1 else 0 := by
  classical
  let W := (A×ˢB).image (fun ij => cell P Q a b ij.1 ij.2)
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,sn,sum⟩
  obtain ⟨pf,_⟩ := finite_of_uniform_sum flat
  have pA : pf.toFinset = A := Finset.coe_inj.mp (pf.coe_toFinset.trans ps)
  have integral {R : PMF ℤ} {r : ℤ} (ep : EndpointWeights R) (top : IsGreatest R.support r)
      (i : ℤ) : IsIntegral ℤ (weight R r i) := by
    obtain ⟨r',rm,rt,h⟩ := ep
    obtain rfl := top.unique (show IsGreatest R.support r' from ⟨rm,rt⟩)
    exact (h i).2.2.1
  have wi (w : W) : IsIntegral ℤ (w:ℝ) := by
    obtain ⟨⟨i,j⟩,_,eq⟩ := mem_image.mp w.property
    rw [←eq]
    exact (integral (endpoint_weights flat).1 pa i).mul (integral (endpoint_weights flat).2 qb j)
  apply integer_model (fun z (w:W) => (colourCount P Q a b z w:ℤ)) (fun z => if z ∈ S then 1 else 0)
    (fun w => (w:ℝ)) wi
  intro z
  let T := A.filter fun i => z-i ∈ B
  let c (i : ℤ) := cell P Q a b i (z-i)
  have incl (i : ℤ) (hi : i ∈ T) : c i ∈ W := mem_image.mpr
    ⟨(i,z-i),mem_product.mpr (mem_filter.mp hi),rfl⟩
  have cnt (w : ℝ) : colourCount P Q a b z w = (T.filter (fun i => c i = w)).card := by
    have seteq : {i | i ∈ P.support ∧ z-i ∈ Q.support ∧ cell P Q a b i (z-i) = w}=
        (T.filter (fun i => c i = w):Set ℤ) := by ext i; simp [ps,qs,T,c,and_assoc]
    rw [colourCount,seteq,Set.ncard_coe_finset]
  have group : (∑ w ∈ W, (colourCount P Q a b z w:ℝ)*w) = ∑ i ∈ T,c i := by
    apply Eq.trans _ (sum_fiberwise_of_maps_to incl c)
    apply sum_congr rfl
    intro w _
    rw [cnt]
    have eq : (∑ i ∈ T.filter (fun i => c i = w),c i) = ∑ _ ∈ T.filter (fun i => c i = w),w := by
      apply sum_congr rfl; exact fun i hi => (mem_filter.mp hi).2
    simpa only [sum_const,nsmul_eq_mul] using eq.symm
  simp only [Int.cast_natCast,Int.cast_ite,Int.cast_one,Int.cast_zero]
  rw [Finset.sum_coe_sort W (fun w : ℝ => (colourCount P Q a b z w:ℝ)*w),group]
  by_cases live : T.Nonempty
  · obtain ⟨i,hi⟩ := live
    obtain ⟨ai,bj⟩ := mem_filter.mp hi
    have pi : i ∈ P.support := ps ▸ ai
    have qj : z-i ∈ Q.support := qs ▸ bj
    have site : z ∈ (indepSum P Q).support := (PMF.mem_support_bind_iff _ _ _).mpr ⟨i,pi,
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨z-i,qj,(PMF.mem_support_pure_iff _ _).mpr (by omega)⟩⟩
    rw [sum,PMF.support_uniformOfFinset] at site
    rw [if_pos (show z ∈ S from site)]
    have h := sum_at_occupied flat pf pa qb (show ∃ x ∈ P.support, z-x ∈ Q.support from ⟨i,pi,qj⟩)
    rw [pA] at h
    have nz : (P a).toReal*(Q b).toReal ≠ 0 := mul_ne_zero
      (ENNReal.toReal_pos ((P.mem_support_iff _).mp pa.1) (P.apply_ne_top _)).ne'
      (ENNReal.toReal_pos ((Q.mem_support_iff _).mp qb.1) (Q.apply_ne_top _)).ne'
    have eq : (∑ i ∈ T,c i) = ∑ i ∈ A,c i := by
      apply sum_subset (filter_subset _ _)
      intro i hi off
      have miss : z-i ∉ Q.support := fun q => off (mem_filter.mpr ⟨hi,by simpa [qs] using q⟩)
      simp [c,cell,weight,(Q.apply_eq_zero_iff _).mpr miss]
    rw [eq]; simp only [c,cell,weight,div_mul_div_comm,←sum_div,h,div_self nz]
  · have off : z ∉ S := by
      intro mem
      have site : z ∈ (indepSum P Q).support := by simpa only [sum,PMF.support_uniformOfFinset,mem_coe] using mem
      obtain ⟨i,hi,h⟩ := (PMF.mem_support_bind_iff _ _ _).mp site
      obtain ⟨j,hj,eq⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
      have s := (PMF.mem_support_pure_iff _ _).mp eq
      exact live ⟨i,mem_filter.mpr ⟨by simpa [ps] using hi,by rw [show z-i = j by omega]; simpa [qs] using hj⟩⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp live,off]

/-- If a signed choice of outcomes counts every product class in multiples
of `d`, its total weight on the support must also be a multiple of `d`. -/
theorem outcome_congruence {P Q : PMF ℤ} {S : Finset ℤ} (sn : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S sn) {a b : ℤ}
    (pa : IsGreatest P.support a) (qb : IsGreatest Q.support b)
    {A B : Finset ℤ} (ps : P.support = ↑A) (qs : Q.support = ↑B)
    (T : Finset ℤ) (k : ℤ → ℤ) (d : ℤ)
    (div : ∀ w ∈ (A×ˢB).image (fun ij => cell P Q a b ij.1 ij.2),
      d ∣ ∑ z ∈ T,k z*(colourCount P Q a b z w:ℤ)) :
    d ∣ ∑ z ∈ T.filter (· ∈ S),k z := by
  classical
  let W := (A×ˢB).image (fun ij => cell P Q a b ij.1 ij.2)
  obtain ⟨v,eq⟩ := simultaneous_fibres sn sum pa qb ps qs
  have dv : d ∣ ∑ w : W, (∑ z ∈ T,k z*(colourCount P Q a b z w:ℤ))*v w :=
    dvd_sum fun w _ => dvd_mul_of_dvd_left (div w w.property) _
  simp_rw [sum_mul,mul_assoc] at dv
  rw [sum_comm] at dv
  have point (z : ℤ) : (∑ w : W,k z*((colourCount P Q a b z w:ℤ)*v w))=
      k z*(if z ∈ S then 1 else 0) := by
    rw [←mul_sum]
    exact congrArg (k z * ·) (eq z)
  simp_rw [point] at dv
  simpa only [mul_ite,mul_one,mul_zero,←sum_filter] using dv

#print axioms integer_retraction
#print axioms integer_model
#print axioms simultaneous_fibres
#print axioms outcome_congruence
end Green28IntegerFibreWitness
