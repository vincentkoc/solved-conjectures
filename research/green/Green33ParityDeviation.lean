import Green33ParityConvolution
open Finset AddMonoidAlgebra Green33Multiplicity
open scoped Pointwise BigOperators
namespace Green33ParityConvolution
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def indicator (S : Finset G) : Measures G :=
  weights fun x => if x ∈ S then 1 else 0

private theorem indicator_coeff (S : Finset G) (g : G) :
    (indicator S).coeff g = if g∈S then 1 else 0 := rfl

private theorem mass_indicator (S : Finset G) : mass (indicator S) = S.card := by
  simp [mass,indicator,coeff_weights]

theorem indicator_product (A B : Finset G) (g : G) :
    (indicator A * indicator B).coeff g = A.addConvolution B g := by
  rw [coeff_product, ← card_inter_vadd_neg]
  have mem (i : G) : i ∈ g +ᵥ -B ↔ g-i ∈ B := by
    rw [mem_vadd_finset]
    simp only [mem_neg, vadd_eq_add]
    constructor
    · rintro ⟨_,⟨b,hb,rfl⟩,rfl⟩
      simpa using hb
    · intro h
      exact ⟨-(g-i),⟨_,h,rfl⟩,by abel⟩
  calc
    _ = ∑ i : G, if i ∈ A ∩ (g +ᵥ -B) then (1:ℝ) else 0 := by
      apply sum_congr rfl
      intro i _
      by_cases a : i ∈ A <;> by_cases b : g-i ∈ B <;>
        simp [indicator,coeff_weights,mem,a,b]
    _ = _ := by rw [sum_boole]; congr 2; ext; simp

private def diagonal (A : Finset G) (g : G) : ℕ := (A.filter fun x => x+x=g).card

private theorem diagonal_sum (A : Finset G) : (∑ g : G, (diagonal A g : ℝ))=A.card := by
  exact_mod_cast (show ∑ g : G, diagonal A g=A.card by
    simpa [diagonal] using sum_card_fiberwise_eq_card_filter A univ (fun a : G => a+a))

omit [Fintype G] in
private theorem diagonal_allowance (A : Finset G) (g : G) :
    2*(if g ∈ A+A then (1:ℝ) else 0) ≤ A.addConvolution A g + (diagonal A g:ℝ) := by
  by_cases hit : g ∈ A+A
  · rw [if_pos hit,mul_one]
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hit
    let P:=(A×ˢA).filter fun p => p.1+p.2=a+b
    have p:(a,b)∈P:=by simp [P,ha,hb]
    change 2≤(P.card:ℝ)+_
    suffices 2≤P.card+diagonal A (a+b) by exact_mod_cast this
    by_cases eq:a=b
    · subst b
      have d:0<diagonal A (a+a):=card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,rfl⟩⟩
      have h:=card_pos.mpr ⟨_,p⟩
      omega
    · have q:(b,a)∈P:=by simp [P,ha,hb,add_comm b a]
      have h:1<P.card := one_lt_card.mpr ⟨_,p,_,q,fun h => eq (congrArg Prod.fst h)⟩
      omega
  · simp only [if_neg hit,mul_zero]
    positivity

private theorem mass_self (A : Finset G) : mass (indicator A ^ 2) = (A.card:ℝ)^2 := by
  simp only [pow_two,mass_product,mass_indicator]

private theorem count_sum (A B : Finset G) :
    (∑ g : G,(A.addConvolution B g : ℝ))=(A.card:ℝ)*B.card := by
  have h := mass_product (indicator A) (indicator B)
  rw [mass_indicator,mass_indicator] at h
  simpa only [mass,indicator_product] using h

private theorem self_variation (A : Finset G) :
    totalVariation (2 • indicator (A+A) - indicator A^2) ≤
      (A.card:ℝ)^2-2*(A+A).card+2*A.card := by
  let u (g:G) : ℝ := if g∈A+A then 1 else 0
  have point (g:G) : |2*u g-(A.addConvolution A g:ℝ)| ≤
      A.addConvolution A g - 2*u g + 2*diagonal A g := by
    have h:=diagonal_allowance A g
    change 2*u g≤_ at h
    exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α:=ℝ) (diagonal A g)],by linarith⟩
  have b:=sum_le_sum (s:=univ) fun g _ => point g
  have us : ∑ g,u g=((A+A).card:ℝ) := by simp [u]
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,count_sum,diagonal_sum,us,←pow_two] at b
  simp only [totalVariation,coeff_sub,Finsupp.sub_apply,two_nsmul,coeff_add,Finsupp.add_apply,
    sq,indicator_product,indicator_coeff]
  simpa only [u,sq,←two_mul] using b


private theorem even_variation (A B : Finset G) (z : G)
    (full : ∀ g, g∈A+A ∨ -z+g∈B+B) :
    totalVariation (indicator A^2 + single z 1 * indicator B^2 - (2:ℝ) • ones) ≤
      (A.card:ℝ)^2 + (B.card:ℝ)^2 - 2*Fintype.card G + 2*(A.card+B.card) := by
  let r (g:G) : ℝ := A.addConvolution A g + (B.addConvolution B (-z+g):ℝ)
  let d (g:G) : ℝ := diagonal A g + (diagonal B (-z+g):ℝ)
  have pt (g:G) : |r g-2| ≤ r g-2+2*d g := by
    have ha:=diagonal_allowance A g
    have hb:=diagonal_allowance B (-z+g)
    have na:=Nat.cast_nonneg (α:=ℝ) (A.addConvolution A g)
    have nb:=Nat.cast_nonneg (α:=ℝ) (B.addConvolution B (-z+g))
    have da:=Nat.cast_nonneg (α:=ℝ) (diagonal A g)
    have db:=Nat.cast_nonneg (α:=ℝ) (diagonal B (-z+g))
    dsimp [r,d]
    apply abs_le.mpr
    rcases full g with h|h
    · rw [if_pos h] at ha
      constructor <;> linarith
    · rw [if_pos h] at hb
      constructor <;> linarith
  have shift (f:G→ℝ) : ∑ g,f (-z+g)=∑ g,f g := Equiv.sum_comp (Equiv.addLeft (-z)) f
  have h:=sum_le_sum (s:=univ) fun g _ => pt g
  simp only [r,d,sum_add_distrib,sum_sub_distrib,←mul_sum,count_sum,diagonal_sum,
    sum_const,card_univ,nsmul_eq_mul] at h
  rw [shift (fun g => (B.addConvolution B g : ℝ)),shift (fun g => (diagonal B g : ℝ)),count_sum,diagonal_sum] at h
  simp only [totalVariation,coeff_sub,Finsupp.sub_apply,coeff_add,Finsupp.add_apply,sq,
    coeff_single_mul_apply,one_mul,coeff_smul_apply,smul_eq_mul,ones,coeff_weights,mul_one,indicator_product]
  linarith only [h]

private theorem even_mass (A : Finset G) :
    totalVariation (indicator A^2)=(A.card:ℝ)^2 := by
  simp only [totalVariation,sq,indicator_product,Nat.abs_cast,count_sum]

private theorem support_mass (A : Finset G) :
    totalVariation (2 • indicator (A+A) + indicator A^2)=2*(A+A).card+(A.card:ℝ)^2 := by
  have dbl (g:G) : (2 • indicator (A+A)).coeff g = 2*(if g∈A+A then (1:ℝ) else 0) := by
    rw [coeff_smul_apply,nsmul_eq_mul,indicator_coeff];rfl
  simp only [totalVariation,coeff_add,Finsupp.add_apply,sq,indicator_product,dbl]
  have pos (g : G) : 0 ≤ 2*(if g ∈ A+A then (1:ℝ) else 0)+(A.addConvolution A g : ℝ) := by positivity
  simp_rw [abs_of_nonneg (pos _)]
  rw [sum_add_distrib,←mul_sum,count_sum]
  simp

private theorem mixed_variations (A B : Finset G) (full : A+B=univ) :
    totalVariation (indicator A*indicator B-ones)=(A.card:ℝ)*B.card-Fintype.card G ∧
    totalVariation (indicator A*indicator B+ones)=(A.card:ℝ)*B.card+Fintype.card G := by
  have lower (g : G) : (1:ℝ)≤A.addConvolution B g := by
    exact_mod_cast (show 0<A.addConvolution B g by rw [addConvolution_pos,full];simp)
  constructor
  · simp only [totalVariation,coeff_sub,Finsupp.sub_apply,indicator_product,ones,coeff_weights,
      abs_of_nonneg (sub_nonneg.mpr (lower _)),sum_sub_distrib,count_sum,sum_const,card_univ,nsmul_eq_mul,mul_one]
  · simp only [totalVariation,coeff_add,Finsupp.add_apply,indicator_product,ones,coeff_weights]
    have pos (g:G) : 0≤(A.addConvolution B g:ℝ)+1 := by positivity
    simp only [abs_of_nonneg (pos _),sum_add_distrib,count_sum,sum_const,card_univ,nsmul_eq_mul,mul_one]
/-- An explicit cardinality-only upper bound for the deviation of the
self-sum representation counts of the support A+A from quarter density. -/
def slideCost (a b u n : ℝ) : ℝ :=
  (a^2-2*u+2*a)*(2*u+a^2) +
    (a^2+b^2-2*n+2*(a+b))*a^2 + (a*b-n)*(a*b+n) + n*|2*a^2-2*n|

theorem support_deviation (A B : Finset G) (z : G) (mixed : A+B=univ)
    (full : ∀ g, g∈A+A ∨ -z+g∈B+B) :
    4 * ∑ g : G, |(reps (A+A) g:ℝ)-(Fintype.card G:ℝ)/4| ≤
      slideCost A.card B.card (A+A).card (Fintype.card G) := by
  let n : ℝ := Fintype.card G
  let a : ℝ := A.card
  let U := A+A
  have h:=even_support_bound (indicator A) (indicator B) (indicator U) z
  have m:=mixed_variations A B mixed
  rw [mass_self,support_mass,even_mass,m.1,m.2] at h
  have b₁:=mul_le_mul_of_nonneg_right (self_variation A)
    (show (0:ℝ)≤2*(A+A).card+(A.card:ℝ)^2 by positivity)
  have b₂:=mul_le_mul_of_nonneg_right (even_variation A B z full) (sq_nonneg (A.card:ℝ))
  replace h := h.trans (add_le_add (add_le_add b₁ b₂) le_rfl)
  have coeff (g:G) : ((2 • indicator U)^2).coeff g = 4*(reps U g:ℝ) := by
    rw [sq,smul_mul_assoc,mul_smul_comm,coeff_smul_apply,coeff_smul_apply,indicator_product]
    change (2:ℕ) • (2:ℕ) • (reps U g:ℝ) = _
    simp [nsmul_eq_mul]; ring
  simp only [totalVariation,coeff_sub,Finsupp.sub_apply,coeff,coeff_smul_apply,smul_eq_mul,
    ones,coeff_weights,mul_one] at h
  have p (g : G) : 4*|(reps U g:ℝ)-n/4| ≤
      |4*(reps U g:ℝ)-(2*a^2-n)|+|2*a^2-2*n| := by
    calc
      _ = |4*((reps U g:ℝ)-n/4)| := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
      _ = |(4*(reps U g:ℝ)-(2*a^2-n))+(2*a^2-2*n)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have q:=sum_le_sum (s:=univ) fun g _ => p g
  rw [←mul_sum,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul] at q
  dsimp only [a,n] at q
  unfold slideCost
  linarith only [q,h]

#print axioms support_deviation
end Green33ParityConvolution
