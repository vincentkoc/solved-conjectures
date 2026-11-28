import Green51SparseDimensions

/-! # Binary Plotkin bounds for the first three-space in a double -/

open Finset Green50Downsets Green50Sharp
open scoped Classical Pointwise
namespace Green51SmallDimensions
local notation "F" => ZMod 2

/-- Summing the weights across the columns gives the binary Plotkin bound
for a linear code with minimum weight D, including inactive coordinates. -/
theorem linear_plotkin {k D : ℕ} (C : Submodule F (Cube k))
    (distance : ∀ x : C, x≠0 → D≤(supp x.val).card) :
    2*D*(2^(Module.finrank F C)-1) ≤ k*2^(Module.finrank F C) := by
  classical
  let ones (i : Fin k) := univ.filter fun x : C => x.val i≠0
  have column (i : Fin k) : 2*(ones i).card≤Fintype.card C := by
    by_cases active : (ones i).Nonempty
    · obtain ⟨a,ha⟩ := active
      have bit (u : F) : u≠0 → u=1 := (show ∀ u:F,u≠0 → u=1 from by decide) u
      let shift : C ↪ C := ⟨fun x => x+a,fun _ _ h => add_right_cancel h⟩
      have dis : Disjoint (ones i) ((ones i).map shift) := by
        rw [disjoint_left]; intro x hx hm
        obtain ⟨y,hy,rfl⟩ := mem_map.mp hm
        have p := (mem_filter.mp hx).2
        have b := bit _ (mem_filter.mp hy).2
        have c := bit _ (mem_filter.mp ha).2
        exact p (show y.val i+a.val i=0 by rw [b,c];decide)
      have bound := ((ones i) ∪ (ones i).map shift).card_le_univ
      rw [card_union_of_disjoint dis,card_map] at bound
      omega
    · rw [not_nonempty_iff_eq_empty.mp active];simp
  have incidence : ∑ x:C,(supp x.val).card=∑ i:Fin k,(ones i).card := by
    simp only [supp,ones,card_filter]
    rw [sum_comm]
  have lower : D*(Fintype.card C-1)≤∑ x:C,(supp x.val).card := by
    have first := sum_le_sum (s:=univ.erase (0:C)) (f:=fun _ => D) (g:=fun x => (supp x.val).card)
      (fun x hx => distance x (mem_erase.mp hx).1)
    rw [sum_const,nsmul_eq_mul,card_erase_of_mem (mem_univ _),card_univ] at first
    rw [mul_comm]
    exact first.trans (sum_le_sum_of_subset (erase_subset _ _))
  have upper : 2*(∑ i:Fin k,(ones i).card)≤k*Fintype.card C := by
    rw [mul_sum]
    simpa using sum_le_sum (s:=univ) (fun i _ => column i)
  rw [←incidence] at upper
  have count : Fintype.card C=2^(Module.finrank F C) := by rw [Module.card_eq_pow_finrank (K:=F),ZMod.card]
  rw [←count,mul_assoc]
  exact (Nat.mul_le_mul_left 2 lower).trans upper

/-- Plotkin's bound on the even kernel of the augmented labels. This is
effective even where counting triples leaves unused ambient syndromes. -/
theorem plotkin_obstruction {n : ℕ} (A : Finset (Cube n)) (large : 5≤A.card)
    (avoid : ¬∃ W : Submodule F (Cube n), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A) :
    (16-A.card)*2^(A.card-(n+1))≤16 := by
  classical
  have free : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ a∈T,a)≠0 := fun T sub sz zero =>
    avoid ((Green51SparseDimensions.linear_three_iff A large).mpr ⟨T,sub,sz,zero⟩)
  obtain ⟨P,parity,kernel,_⟩ := Green51SparseDimensions.even_pair_check A free
  let C := P.ker
  have distance (x : C) (nonzero : x≠0) : 8≤(supp x.val).card := by
    have even := parity x.val x.property
    by_contra! small
    exact nonzero (Subtype.ext (kernel x.val (by omega) x.property))
  have plot := linear_plotkin C distance
  have rank := P.finrank_range_add_finrank_ker
  have lim := Submodule.finrank_le P.range
  have source : Module.finrank F (Cube A.card)=A.card := by simp [Cube]
  have target : Module.finrank F (F×Cube n)=1+n := by simp [Module.finrank_prod,Cube]
  rw [source] at rank; rw [target] at lim
  have codim : A.card-(n+1)≤Module.finrank F C := by dsimp only [C];omega
  apply le_trans (Nat.mul_le_mul_left (16-A.card) (Nat.pow_le_pow_right (by decide : 0 < 2) codim))
  rw [Nat.sub_mul]
  change 16*(2^(Module.finrank F C)-1)≤_ at plot
  rw [Nat.mul_sub_left_distrib,Nat.mul_one] at plot
  omega

/-- Maximal avoiding sizes in dimensions three through nine. -/
def sparseCutoff : ℕ → ℕ
  | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 8 | 7 => 9 | 8 => 10 | 9 => 12
  | _ => 0

/-- Above the displayed cardinality threshold a linear three-space is
unavoidable in each dimension from three to nine. -/
theorem above_cutoff {n : ℕ} (lo : 3≤n) (hi : n≤9) (A : Finset (Cube n))
    (big : sparseCutoff n<A.card) :
    ∃ W : Submodule F (Cube n), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A := by
  obtain ⟨B,sub,count⟩ := exists_subset_card_eq (show sparseCutoff n+1≤A.card by omega)
  by_contra avoid
  have avoidB : ¬∃ W : Submodule F (Cube n), Module.finrank F W=3 ∧ ∀ w∈W,w∈B+B := by
    rintro ⟨W,d,inside⟩
    exact avoid ⟨W,d,fun w hw => add_subset_add sub sub (inside w hw)⟩
  have five : 5≤B.card := by rw [count];interval_cases n <;> decide
  have obstruction := plotkin_obstruction B five avoidB
  rw [count] at obstruction
  interval_cases n <;> norm_num [sparseCutoff] at obstruction

end Green51SmallDimensions

#print axioms Green51SmallDimensions.linear_plotkin
#print axioms Green51SmallDimensions.plotkin_obstruction
#print axioms Green51SmallDimensions.above_cutoff
