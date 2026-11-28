import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic
/-! Affine plane curves split into a bounded number of lines and a set with bounded secants. -/
open Finset Polynomial
open scoped Polynomial
namespace Green33AffineCurves
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

noncomputable def graphPoly (l : F×F) : F[X] := C l.1*X+C l.2

noncomputable def verticals (f : F[X][X]) : Finset F := univ.filter fun a => f.map (evalRingHom a)=0

noncomputable def obliques (f : F[X][X]) : Finset (F×F) := univ.filter fun l => f.eval (graphPoly l)=0

omit [DecidableEq F] [Fintype F] in
private theorem graph_inj : Function.Injective (graphPoly (F:=F)) := by
  intro u v h
  apply Prod.ext
  · simpa [graphPoly,coeff_C_mul_X] using congrArg (fun p : F[X] => p.coeff 1) h
  · simpa [graphPoly,coeff_C_mul_X] using congrArg (fun p : F[X] => p.coeff 0) h

private theorem roots_bound {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (f : R[X]) : f.roots.toFinset.card≤f.natDegree :=
  f.roots.toFinset_card_le.trans f.card_roots'

theorem line_counts (f : F[X][X]) (ne : f≠0) {d : ℕ} (xdeg : ∀ i,(f.coeff i).natDegree≤d) :
    (verticals f).card≤d ∧ (obliques f).card≤f.natDegree := by
  constructor
  · have sub : verticals f⊆f.leadingCoeff.roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset,mem_roots (leadingCoeff_ne_zero.mpr ne)]
      have eq:=congrArg (fun p : F[X] => p.coeff f.natDegree) (mem_filter.mp hx).2
      simpa only [coeff_map,coeff_zero,leadingCoeff,coe_evalRingHom,IsRoot.def] using eq
    exact (card_le_card sub).trans ((roots_bound _).trans (xdeg _))
  · have h : Set.MapsTo graphPoly (↑(obliques f) : Set (F×F)) (↑f.roots.toFinset : Set F[X]) := by
      intro l hl
      exact Multiset.mem_toFinset.mpr ((mem_roots ne).mpr (mem_filter.mp hl).2)
    exact (card_le_card_of_injOn graphPoly h graph_inj.injOn).trans (roots_bound f)

#print axioms line_counts

omit [Fintype F] [DecidableEq F] in
theorem graph_degree (f : F[X][X]) {d : ℕ} (hx : ∀ i,(f.coeff i).natDegree≤d) (l : F×F) :
    (f.eval (graphPoly l)).natDegree≤d+f.natDegree := by
  have g : (graphPoly l).natDegree≤1 := by
    apply (natDegree_add_le ..).trans
    apply max_le
    · exact natDegree_mul_le.trans (by simp)
    · simp
  rw [eval_eq_sum,Polynomial.sum]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have v:=(natDegree_pow_le (p:=graphPoly l) (n:=i)).trans (by simpa using Nat.mul_le_mul_left i g)
  exact natDegree_mul_le.trans (Nat.add_le_add (hx i) (v.trans (f.le_natDegree_of_mem_supp i hi)))

#print axioms graph_degree

noncomputable def zeros (f : F[X][X]) : Finset (F×F) := univ.filter fun xy => (f.map (evalRingHom xy.1)).eval xy.2=0

noncomputable def residual (f : F[X][X]) : Finset (F×F) :=
  (zeros f).filter fun p => p.1∉verticals f ∧ ∀ l∈obliques f,p.2≠l.1*p.1+l.2

theorem residual_vertical (f : F[X][X]) (a : F) :
    ((residual f).filter (·.1=a)).card≤f.natDegree := by
  by_cases empty : f.map (evalRingHom a)=0
  · have eq : (residual f).filter (·.1=a)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have h:=mem_filter.mp hz
      exact (mem_filter.mp h.1).2.1 (mem_filter.mpr ⟨mem_univ _,by rwa [h.2]⟩)
    simp [eq]
  · let g:=f.map (evalRingHom a)
    have sub : Set.MapsTo Prod.snd (↑((residual f).filter (·.1=a)) : Set (F×F)) (↑g.roots.toFinset : Set F) := by
      intro z hz;have h:=mem_filter.mp hz
      have zero:=(mem_filter.mp (mem_filter.mp h.1).1).2
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots empty).mpr
      change (f.map (evalRingHom a)).eval z.2=0
      rwa [←h.2]
    have inj : Set.InjOn Prod.snd (↑((residual f).filter (·.1=a)) : Set (F×F)) := by
      intro x hx y hy eq
      exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) eq
    exact (card_le_card_of_injOn _ sub inj).trans ((roots_bound g).trans natDegree_map_le)

theorem residual_oblique (f : F[X][X]) {d : ℕ} (hx : ∀ i,(f.coeff i).natDegree≤d) (l : F×F) :
    ((residual f).filter (fun z => z.2=l.1*z.1+l.2)).card≤d+f.natDegree := by
  let g:=f.eval (graphPoly l)
  by_cases empty:g=0
  · have eq : (residual f).filter (fun z => z.2=l.1*z.1+l.2)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz;have h:=mem_filter.mp hz
      exact (mem_filter.mp h.1).2.2 l (mem_filter.mpr ⟨mem_univ _,empty⟩) h.2
    simp [eq]
  · have sub : Set.MapsTo Prod.fst (↑((residual f).filter fun z => z.2=l.1*z.1+l.2) : Set (F×F))
        (↑g.roots.toFinset : Set F) := by
      intro z hz;have h:=mem_filter.mp hz
      have zero:=(mem_filter.mp (mem_filter.mp h.1).1).2
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots empty).mpr
      have val : (evalRingHom z.1) (graphPoly l)=l.1*z.1+l.2 := by simp [graphPoly]
      change (evalRingHom z.1) (f.eval (graphPoly l))=0
      rw [←eval₂_at_apply,val,←h.2,←eval_map]
      exact zero
    have inj : Set.InjOn Prod.fst (↑((residual f).filter fun z => z.2=l.1*z.1+l.2) : Set (F×F)) := by
      intro x hx y hy eq
      exact Prod.ext eq (by rw [(mem_filter.mp hx).2,(mem_filter.mp hy).2,eq])
    exact (card_le_card_of_injOn _ sub inj).trans ((roots_bound g).trans (graph_degree _ hx l))

#print axioms residual_vertical
#print axioms residual_oblique
end Green33AffineCurves
