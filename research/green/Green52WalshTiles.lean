import Green52Complements
import Green50Sharp

/-! # Exact graph tilings with thin twofold sums

Binary affine words give the classical first-order Reed–Muller covering bound. Choosing
one representative per code coset inside the Hamming ball gives an exact tiling and an
exponential lower bound in the output dimension of the Green 52 graph formulation.
-/
open Finset
open scoped Classical Pointwise
namespace Green52WalshTiles
local notation "K" => ZMod 2

private def sign (z : K) : ℤ := if z=0 then 1 else -1
private theorem sign_add (a b : K) : sign (a+b) = sign a * sign b := by decide +revert
private theorem sign_sq (a : K) : sign a ^ 2 = 1 := by decide +revert

variable {D : Type*} [AddCommGroup D] [Module K D] [Fintype D]
  [Fintype (Module.Dual K D)]

/-- Orthogonality of the binary character table, with integer signs. -/
private theorem orthogonal (x y : D) :
    (∑ l : Module.Dual K D, sign (l x) * sign (l y)) =
      if x=y then (Fintype.card (Module.Dual K D):ℤ) else 0 := by
  classical
  by_cases h : x=y
  · subst y; simp [←sq,sign_sq]
  · rw [if_neg h]
    obtain ⟨u,h1⟩ := Module.Projective.exists_dual_eq_one K (sub_ne_zero.mpr h)
    have hs : sign (u x) * sign (u y) = -1 := by
      rw [map_sub] at h1
      exact (show ∀ a b : K, a-b=1 → sign a * sign b = -1 from by decide) _ _ h1
    let F (l : Module.Dual K D) := sign (l x) * sign (l y)
    have swap (l : Module.Dual K D) : F (u+l) = -F l := by
      simp only [F,LinearMap.add_apply,sign_add]
      rw [mul_mul_mul_comm,hs,neg_one_mul]
    have he := Equiv.sum_comp (Equiv.addLeft u) F
    change (∑ l, F (u+l)) = ∑ l, F l at he
    simp only [swap,sum_neg_distrib] at he
    change ∑ l, F l = 0
    omega

def correlation (w : D → K) (l : Module.Dual K D) : ℤ := ∑ x, sign (w x + l x)

/-- The squared correlations average to the word length. -/
theorem sum_correlation_sq (w : D → K) :
    (∑ l : Module.Dual K D, correlation w l ^ 2) =
      (Fintype.card D : ℤ) * Fintype.card (Module.Dual K D) := by
  classical
  have expand (l : Module.Dual K D) : correlation w l ^ 2 =
      ∑ x, ∑ y, (sign (w x)*sign (w y)) * (sign (l x)*sign (l y)) := by
    simp only [correlation,sq,sum_mul,mul_sum,sign_add]
    apply sum_congr rfl; intro x _
    apply sum_congr rfl; intro y _
    ring
  simp only [expand]
  rw [sum_comm]
  calc
    _ = ∑ x:D, ∑ y:D, (sign (w x)*sign (w y)) *
          (∑ l : Module.Dual K D, sign (l x)*sign (l y)) := by
        apply sum_congr rfl; intro x _
        rw [sum_comm]
        simp only [mul_sum]
    _ = _ := by simp [orthogonal, mul_ite, ←sq,sign_sq]

noncomputable def weight (v : D → K) : ℕ := (univ.filter fun x => v x ≠ 0).card

omit [AddCommGroup D] [Module K D] [Fintype (Module.Dual K D)] in
private theorem imbalance (v : D → K) :
    ∑ x, sign (v x) = (Fintype.card D:ℤ) - 2*weight v := by
  classical
  have pt (x : D) : sign (v x) = 1 - (if v x ≠ 0 then (2:ℤ) else 0) := by
    by_cases h : v x=0 <;> simp [sign,h]
  simp_rw [pt]
  simp [sum_sub_distrib, sum_ite, weight, mul_comm]

/-- Every binary word is within the stated Hamming radius of an affine word. -/
theorem close_affine_word (s : ℕ) (hn : s^2 ≤ Fintype.card D) (w : D → K) :
    ∃ (l : Module.Dual K D) (c : K), 2*weight (fun x => w x+l x+c)+s ≤ Fintype.card D := by
  classical
  have hlarge : ∃ l, (s:ℤ)^2 ≤ correlation w l ^ 2 := by
    by_contra! hh
    have ht := sum_lt_sum_of_nonempty (s := (univ : Finset (Module.Dual K D))) univ_nonempty (fun l _ => hh l)
    rw [sum_correlation_sq,sum_const,card_univ,nsmul_eq_mul,mul_comm] at ht
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (by positivity))) ht
  obtain ⟨l,hl⟩ := hlarge
  have bound (c : K) (hc : (s:ℤ) ≤ sign c * correlation w l) :
      2*weight (fun x => w x+l x+c)+s ≤ Fintype.card D := by
    have he := imbalance (fun x => w x+l x+c)
    simp_rw [sign_add (w _+l _) c] at he
    rw [←sum_mul] at he
    change correlation w l * sign c = _ at he
    rw [mul_comm] at he
    omega
  by_cases hpos : 0 ≤ correlation w l
  · refine ⟨l,0,bound 0 ?_⟩
    change (s:ℤ) ≤ 1*correlation w l
    nlinarith
  · refine ⟨l,1,bound 1 ?_⟩
    change (s:ℤ) ≤ (-1)*correlation w l
    nlinarith

abbrev Ambient (D : Type*) [Fintype D] := Fin (Fintype.card D) → K

/-- The linear encoding of all affine binary words, with the coordinates indexed by a finite vector space. -/
noncomputable def affineCode : (Module.Dual K D × K) →ₗ[K] Ambient D where
  toFun p := fun j => p.1 ((Fintype.equivFin D).symm j) + p.2
  map_add' := by rintro ⟨f,c⟩ ⟨g,b⟩; ext i; simp; abel
  map_smul' := by rintro c ⟨f,b⟩; ext i; simp [mul_add]

omit [Fintype (Module.Dual K D)] in
private theorem code_injective : Function.Injective (affineCode (D:=D)) := by
  rintro ⟨f,c⟩ ⟨g,b⟩ eq
  have he (x : D) : f x+c = g x+b := by
    simpa [affineCode] using congrFun eq (Fintype.equivFin D x)
  have hcb : c=b := by simpa using he 0
  subst b
  exact Prod.ext (LinearMap.ext fun x => add_right_cancel (he x)) rfl

omit [AddCommGroup D] [Module K D] [Fintype (Module.Dual K D)] in
private theorem reindex_weight (v : Ambient D) :
    weight (fun x : D => v (Fintype.equivFin D x)) = (Green50Sharp.supp v).card := by
  classical
  let e := Fintype.equivFin D
  let A := univ.filter (fun x : D => v (e x) ≠ 0)
  have he : A.map e.toEmbedding = Green50Sharp.supp v := by
    ext j
    simp [A,Green50Sharp.supp]
  simpa [A,weight,e] using congrArg Finset.card he

/-- The affine word space covers the cube at the radius given by the Walsh bound. -/
theorem affine_code_covers (s : ℕ) (hn : s^2 ≤ Fintype.card D) :
    (Green50Sharp.ball (Fintype.card D) ((Fintype.card D-s)/2) : Set (Ambient D)) +
      ((affineCode (D:=D)).range : Set (Ambient D)) = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun v => ?_
  obtain ⟨l,c,hc⟩ := close_affine_word s hn (fun x : D => v (Fintype.equivFin D x))
  let z := affineCode (l,c)
  have hz : weight (fun x : D => v (Fintype.equivFin D x)+l x+c) =
      (Green50Sharp.supp (v+z)).card := by
    rw [←reindex_weight]
    congr 1
    ext x
    simp [z,affineCode,add_assoc]
  rw [hz] at hc
  have hb : v+z ∈ Green50Sharp.ball (Fintype.card D) ((Fintype.card D-s)/2) :=
    mem_filter.mpr ⟨mem_univ _,by omega⟩
  refine ⟨v+z,hb,z,⟨(l,c),rfl⟩,?_⟩
  have ht : z+z=0 := by rw [←two_smul K,show (2:K)=0 by decide,zero_smul]
  change v+z+z=v
  rw [add_assoc,ht,add_zero]

/-- The exact tiling can be chosen inside the small ball.
Every affine subspace of the double of its tile then has codimension at least s. -/
theorem exact_bad_tile (s : ℕ) (hn : s^2 ≤ Fintype.card D) :
    ∃ (U V : Submodule K (Ambient D)), IsCompl U V ∧ Nat.card V = 2*Fintype.card D ∧
      ∃ f : U → V, ∀ P : AffineSubspace K (Ambient D),
        (P : Set (Ambient D)) ⊆ (Green50Graphs.graph U V f : Set (Ambient D)) +
          (Green50Graphs.graph U V f : Set (Ambient D)) →
        Module.finrank K P.direction + s ≤ Fintype.card D := by
  classical
  let V := (affineCode (D:=D)).range
  obtain ⟨U,hU⟩ := V.exists_isCompl
  obtain ⟨f,hf⟩ := Green52Complements.graph_of_subspace_cover
    _ U V (affine_code_covers s hn)
  have cD : Fintype.card (Module.Dual K D) = Fintype.card D := calc
    _ = Fintype.card K ^ Module.finrank K (Module.Dual K D) := Module.card_eq_pow_finrank
    _ = _ := by rw [Subspace.dual_finrank_eq]; exact Module.card_eq_pow_finrank.symm
  have cv : Nat.card V = 2*Fintype.card D := by
    have h := Nat.card_congr (LinearEquiv.ofInjective (affineCode (D:=D)) code_injective).toEquiv
    change Nat.card (Module.Dual K D × K) = Nat.card V at h
    rw [←h,Nat.card_eq_fintype_card,Fintype.card_prod,cD]
    simp [Nat.mul_comm]
  refine ⟨U,V,hU.symm,cv,f,?_⟩
  intro P hP
  have hs : s ≤ Fintype.card D := (Nat.le_self_pow (by decide : (2:ℕ) ≠ 0) _).trans hn
  by_cases empty : P=⊥
  · rw [empty,AffineSubspace.direction_bot,finrank_bot,zero_add]; exact hs
  obtain ⟨x,hx⟩ := (AffineSubspace.nonempty_iff_ne_bot P).mpr empty
  have ball : x +ᵥ (P.direction : Set (Ambient D)) ⊆
      ↑((2:ℕ) • Green50Sharp.ball (Fintype.card D) ((Fintype.card D-s)/2)) := by
    rintro _ ⟨v,hv,rfl⟩
    have hxv : x+v ∈ P := by simpa [add_comm] using AffineSubspace.vadd_mem_of_mem_direction hv hx
    obtain ⟨y,hy,z,hz,he⟩ := hP hxv
    rw [two_nsmul]
    exact mem_add.mpr ⟨y,hf hy,z,hf hz,he⟩
  have bd := Green50Sharp.ball_dimension P.direction x ball
  change Module.finrank K P.direction ≤ 2*((Fintype.card D-s)/2) at bd
  exact (Nat.add_le_add_right bd s).trans (by omega)

open Green52Complements

/-- A full graph with exactly m+1 output coordinates at word length 2^m,
together with the obstruction to every affine flat in its double. -/
theorem dyadic_bad_graph (m : ℕ) :
    ∃ (U V : Submodule K (Cube (2^m))), IsCompl U V ∧ Module.finrank K V = m+1 ∧
      Nat.card V = 2^(m+1) ∧ ∃ f : U → V, ∀ P : AffineSubspace K (Cube (2^m)),
        (P : Set (Cube (2^m))) ⊆ (Green50Graphs.graph U V f : Set (Cube (2^m))) +
          (Green50Graphs.graph U V f : Set (Cube (2^m))) →
        Module.finrank K P.direction + (2^m).sqrt ≤ 2^m := by
  classical
  let D := Fin m → K
  let _ : Fintype (Module.Dual K D) :=
    Fintype.ofInjective (fun l : Module.Dual K D => (l : D → K)) DFunLike.coe_injective
  have hn : Fintype.card D = 2^m := by simp [D]
  obtain ⟨U,V,hcomp,hcard,f,bad⟩ := exact_bad_tile (D:=D) (2^m).sqrt (by rw [hn]; exact Nat.sqrt_le' _)
  have hd : Module.finrank K V = m+1 := by
    apply Nat.pow_right_injective (a:=2) (by decide)
    have hc : 2^(Module.finrank K V) = Nat.card V := by
      rw [Nat.card_eq_fintype_card]
      simpa using (Module.card_eq_pow_finrank :
        Fintype.card V = Fintype.card K ^ Module.finrank K V).symm
    change 2^(Module.finrank K V) = 2^(m+1)
    rw [hc,hcard,hn,pow_succ,mul_comm]
  let assertion (n : ℕ) : Prop :=
    ∃ (U' V' : Submodule K (Cube n)), IsCompl U' V' ∧ Module.finrank K V' = m+1 ∧
      Nat.card V' = 2^(m+1) ∧ ∃ g : U' → V', ∀ P : AffineSubspace K (Cube n),
        (P : Set (Cube n)) ⊆ (Green50Graphs.graph U' V' g : Set (Cube n)) +
          (Green50Graphs.graph U' V' g : Set (Cube n)) →
        Module.finrank K P.direction + (2^m).sqrt ≤ n
  have witness : assertion (Fintype.card D) :=
    ⟨U,V,hcomp,hd,by rw [hcard,hn,pow_succ,Nat.mul_comm],f,bad⟩
  exact (congrArg assertion hn).mp witness

/-- Any codimension bound for full graphs, indexed by output dimension d,
is at least the integer square root of 2^(d−1) for every positive d. -/
theorem graph_bound_lower (b : ℕ → ℕ)
    (hb : ∀ n (U V : Submodule K (Cube n)), IsCompl U V → ∀ f : U → V,
      Flat n (b (Module.finrank K V)) (Green50Graphs.graph U V f : Set (Cube n))) (m : ℕ) :
    (2^m).sqrt ≤ b (m+1) := by
  obtain ⟨U,V,hcomp,hd,_,f,bad⟩ := dyadic_bad_graph m
  obtain ⟨P,hs,dim⟩ := hb _ U V hcomp f
  rw [hd] at dim
  have small := bad P hs
  omega

end Green52WalshTiles

#print axioms Green52WalshTiles.sum_correlation_sq
#print axioms Green52WalshTiles.close_affine_word
#print axioms Green52WalshTiles.affine_code_covers
#print axioms Green52WalshTiles.exact_bad_tile
#print axioms Green52WalshTiles.dyadic_bad_graph
#print axioms Green52WalshTiles.graph_bound_lower
