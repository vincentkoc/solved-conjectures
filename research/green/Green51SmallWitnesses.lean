import Green51SmallDimensions
import Green51TenDimensions
import Green51SparseBounds

/-! # Sharp cardinality witnesses for sparse binary sumsets -/

open Finset Green50Downsets Green50Sharp Green51SparseDimensions Green51SmallDimensions
open scoped Classical Pointwise
namespace Green51SmallWitnesses
local notation "F" => ZMod 2

private theorem weight_of_subset {n : ℕ} (T : Finset (Cube n)) (sub : T⊆ball n 1) :
    (supp (∑ x∈T,x)).card≤T.card := by
  have mem : (∑ x∈T,x)∈T.card • ball n 1 := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert x S hx ih =>
      rw [insert_subset_iff] at sub
      rw [sum_insert hx,card_insert_of_notMem hx,
        add_nsmul,one_nsmul,add_comm x]
      exact add_mem_add (ih sub.2) sub.1
  simpa using weight_of_mem_sum mem

private theorem unit_sum {n : ℕ} (T : Finset (Cube n)) (sub : T⊆ball n 1) (two : 2≤T.card) :
    (∑ x∈T,x)≠0 := by
  obtain ⟨u,hu,nonzero⟩ : ∃ u∈T,u≠0 := by
    by_contra! h
    have le := card_le_card (t:=({0}:Finset (Cube n))) (fun y hy => mem_singleton.mpr (h y hy))
    simp only [card_singleton] at le;omega
  have existsBit : ∃ j,u j≠0 := by
    by_contra! h
    exact nonzero (funext h)
  obtain ⟨j,hit⟩ := existsBit
  have single {v : Cube n} (hv : v∈T) (vj : v j≠0) : v=Pi.single j 1 := by
    have sz := (mem_filter.mp (sub hv)).2
    funext i
    by_cases eq : i=j
    · rw [eq,Pi.single_eq_same]
      exact (show ∀ y:F,y≠0 → y=1 from by decide) _ vj
    · rw [Pi.single_eq_of_ne eq]
      by_contra ne
      exact eq (card_le_one.mp sz i (mem_filter.mpr ⟨mem_univ _,ne⟩) j (mem_filter.mpr ⟨mem_univ _,vj⟩))
  intro zero
  have val := congrFun zero j
  rw [Finset.sum_apply,sum_eq_single u] at val
  · exact hit val
  · intro v hv ne
    by_contra nz
    exact ne ((single hv nz).trans (single hu hit).symm)
  · exact fun h => (h hu).elim

/-- A basis of any binary linear code of minimum weight six can be added
to the zero vector and coordinate units without a four- or six-point relation. -/
theorem add_heavy_labels {n : ℕ} (E : Finset (Cube n))
    (heavy : ∀ U⊆E, U.Nonempty → 6≤(supp (∑ u∈U,u)).card) :
    ∀ T⊆ball n 1∪E, T.card=4 ∨ T.card=6 → (∑ t∈T,t)≠0 := by
  intro T sub number zero
  let U := T∩E
  have ut : U⊆T := inter_subset_left
  have rest : T\U⊆ball n 1 := by
    intro x hx
    obtain ⟨ht,hout⟩ := mem_sdiff.mp hx
    rcases mem_union.mp (sub ht) with s|e
    · exact s
    · exact (hout (mem_inter.mpr ⟨ht,e⟩)).elim
  by_cases non : U.Nonempty
  · have high := heavy U inter_subset_right non
    have low := weight_of_subset (T\U) rest
    have eq : (∑ t∈T\U,t)=(∑ t∈U,t) :=
      add_right_cancel (((sum_sdiff ut (f:=id)).trans zero).trans (ZModModule.add_self _).symm)
    rw [eq,card_sdiff_of_subset ut] at low
    have pos := card_pos.mpr non
    omega
  · have empty := not_nonempty_iff_eq_empty.mp non
    rw [empty,sdiff_empty] at rest
    exact unit_sum T rest (by omega) zero

private def binaryPoint (n a : ℕ) : Cube n := fun i => if a.testBit i.val then 1 else 0

private def extras (n : ℕ) : Finset (Cube n) :=
  ((if 6≤n then [63] else []) ++ (if n=9 then [504] else []) : List ℕ).toFinset.image (binaryPoint n)

private theorem extra_properties {n : ℕ} (lo : 3≤n) (hi : n≤9) :
    n+1+(extras n).card=sparseCutoff n ∧
      ∀ U∈(extras n).powerset, U.Nonempty → 6≤(supp (∑ u∈U,u)).card := by
  constructor
  · interval_cases n <;> decide +kernel
  intro U hu non
  have sub := mem_powerset.mp hu
  by_cases six : 6≤n
  · by_cases nine : n=9
    · subst n
      let v := binaryPoint 9 63
      let w := binaryPoint 9 504
      have pair : extras 9={v,w} := by decide +kernel
      rw [pair] at sub
      have ne : v≠w := by decide +kernel
      have weights : 6≤(supp v).card ∧ 6≤(supp w).card ∧ 6≤(supp (v+w)).card := by decide +kernel
      have singletonCase (a : Cube 9) (h : U⊆{a}) : U={a} :=
        eq_singleton_iff_nonempty_unique_mem.mpr ⟨non,fun x hx => mem_singleton.mp (h hx)⟩
      by_cases a : v∈U <;> by_cases b : w∈U
      · have h : U={v,w} := Subset.antisymm sub (insert_subset_iff.mpr ⟨a,singleton_subset_iff.mpr b⟩)
        rw [h,sum_pair ne]; exact weights.2.2
      · have h : U⊆{v} := by
          intro x hx
          rcases mem_insert.mp (sub hx) with h|h
          · exact mem_singleton.mpr h
          · exact (b (mem_singleton.mp h ▸ hx)).elim
        rw [singletonCase _ h,sum_singleton];exact weights.1
      · have h : U⊆{w} := by
          intro x hx
          rcases mem_insert.mp (sub hx) with h|h
          · exact (a (h ▸ hx)).elim
          · exact h
        rw [singletonCase _ h,sum_singleton];exact weights.2.1
      · obtain ⟨x,hx⟩ := non
        rcases mem_insert.mp (sub hx) with h|h
        · exact (a (h ▸ hx)).elim
        · exact (b (mem_singleton.mp h ▸ hx)).elim
    · have eq : extras n={binaryPoint n 63} := by simp [extras,six,nine]
      rw [eq] at sub
      have h : U={binaryPoint n 63} :=
        eq_singleton_iff_nonempty_unique_mem.mpr ⟨non,fun x hx => mem_singleton.mp (sub hx)⟩
      rw [h,sum_singleton]
      have lt : n≤8 := by omega
      interval_cases n <;> decide +kernel
  · have nine : n≠9 := by omega
    have eq : extras n=∅ := by simp [extras,six,nine]
    obtain ⟨x,hx⟩ := non
    have bad := sub hx
    simp [eq] at bad

/-- When the double avoids linear three-spaces, the cardinality cost of
an affine flat bounds the actual maximum coset dimension. -/
theorem max_dim_of_avoiding {n d : ℕ} (A : Finset (Cube n)) (two : 2≤d)
    (avoid : ¬∃ W : Submodule F (Cube n), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A)
    (small : A.card<2^(d+2)) : maxCosetDim F (Cube n) ↑(A+A)≤d := by
  apply csSup_le
  · exact ⟨0,⊥,by simp,by simp⟩
  · rintro _ ⟨S,sub,rfl⟩
    by_contra! high
    have non : ∃ p,p∈S := by
      by_contra! empty
      have bot : S=⊥ := by
        ext x; simp only [AffineSubspace.notMem_bot,iff_false];exact empty x
      rw [bot,AffineSubspace.direction_bot] at high;simp at high
    obtain ⟨p,hp⟩ := non
    have cost := Green51AffineMatchings.affine_flat_cost A avoid S.direction p (by
      rintro _ ⟨w,hw,rfl⟩
      apply sub
      simpa [vadd_eq_add,add_comm] using AffineSubspace.vadd_mem_of_mem_direction hw hp) (by omega)
    have le := Nat.pow_le_pow_right (by decide : 0<2) (show d+2≤Module.finrank F S.direction+1 by omega)
    omega

/-- The Plotkin cutoffs are attained by coordinate units and at most two
additional words. The resulting double has no affine flat of rank three. -/
theorem cutoff_witness {n : ℕ} (lo : 3≤n) (hi : n≤9) :
    ∃ A : Finset (Cube n), A.card=sparseCutoff n ∧
      maxCosetDim F (Cube n) ↑(A+A)≤2 := by
  obtain ⟨size,he⟩ := extra_properties lo hi
  let E := extras n
  have heavy (U : Finset (Cube n)) (sub : U⊆E) (non : U.Nonempty) :
      6≤(supp (∑ u∈U,u)).card := he U (mem_powerset.mpr sub) non
  have dis : Disjoint (ball n 1) E := by
    rw [disjoint_left]; intro v h1 h2
    have high := heavy {v} (singleton_subset_iff.mpr h2) (singleton_nonempty _)
    rw [sum_singleton] at high
    have low := (mem_filter.mp h1).2; omega
  let A := ball n 1 ∪ E
  have count : A.card=sparseCutoff n := by
    dsimp only [A]; rw [card_union_of_disjoint dis,Green50HammingDensity.ball_count]
    simpa [sum_range_succ,Nat.add_comm 1 n] using size
  have free := add_heavy_labels E heavy
  have avoid : ¬∃ W : Submodule F (Cube n), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A := by
    rintro ⟨W,dim,inside⟩; have := rank_without_relation A free W inside;omega
  refine ⟨A,count,?_⟩
  apply max_dim_of_avoiding A le_rfl avoid
  rw [count]; interval_cases n <;> decide

private theorem density {n : ℕ} (A : Finset (Cube n)) :
    (A.dens : ℝ)=(A.card : ℝ)/2^n := by rw [nnratCast_dens];simp [Cube]

/-- For dimensions three through nine, this is the exact density at which
Green's affine guarantee first reaches three. -/
theorem three_iff {n : ℕ} (lo : 3≤n) (hi : n≤9) {α : ℝ} (one : α≤1) :
    3≤Green51.guaranteedMaxCosetDim n α ↔ (sparseCutoff n : ℝ)/2^n<α := by
  constructor
  · intro h
    by_contra! small
    obtain ⟨A,count,bound⟩ := cutoff_witness lo hi
    have admissible : α≤(A.dens : ℝ) := by rwa [density,count]
    have top : Green51.guaranteedMaxCosetDim n α ≤ maxCosetDim F (Cube n) ↑(A+A) :=
      csInf_le (OrderBot.bddBelow _) ⟨A,admissible,rfl⟩
    omega
  · intro h
    apply Green51SparseBounds.guarantee_of_linear one
    intro A ha
    have strict := h.trans_le ha
    rw [density,div_lt_div_iff_of_pos_right (by positivity)] at strict
    exact above_cutoff lo hi A (by exact_mod_cast strict)

/-- Above the two-point density and up to the first three-space threshold,
the original guaranteed dimension is exactly two. -/
theorem first_plateau {n : ℕ} (lo : 3≤n) (hi : n≤9) {α : ℝ}
    (two : 2/(2:ℝ)^n<α) (top : α≤(sparseCutoff n : ℝ)/2^n) :
    Green51.guaranteedMaxCosetDim n α=2 := by
  obtain ⟨A,count,_⟩ := cutoff_witness lo hi
  have admissible : α≤(A.dens : ℝ) := by rwa [density,count]
  have one : α≤1 := admissible.trans (by exact_mod_cast A.dens_le_one)
  have lower := Green51SparseBounds.two_above_two_points one two
  have upper := mt ((three_iff lo hi one).mp) (not_lt_of_ge top)
  omega

end Green51SmallWitnesses

#print axioms Green51SmallWitnesses.add_heavy_labels
#print axioms Green51SmallWitnesses.max_dim_of_avoiding
#print axioms Green51SmallWitnesses.cutoff_witness
#print axioms Green51SmallWitnesses.three_iff
#print axioms Green51SmallWitnesses.first_plateau
