import Green51MoorePreimages
/-! # Dimension of the span of binary pair brackets -/
open Green51BCHCompression Finset
namespace Green51BracketRank
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K]
private def row (A : Submodule F K) (x : A) : A →ₗ[F] K where
  toFun y := bracket (x:K) (y:K)
  map_add' b c := by
    change bracket (x:K) ((b:K)+(c:K))=_
    unfold bracket
    ring_nf
    reduce_mod_char!
  map_smul' r y := by
    rcases (show ∀ i:F,i=0 ∨ i=1 from by decide) r with rfl|rfl <;> simp [bracket]

private theorem root_iff (A : Submodule F K) {x : A} (nx : x≠0) (y : A) :
    row A x y=0 ↔ y=0 ∨ y=x := by
  have nz : (x:K)≠0 := fun z => nx (Subtype.ext z)
  change (x:K)*(y:K)*((x:K)+(y:K))=0 ↔ _
  rw [mul_eq_zero,mul_eq_zero,CharTwo.add_eq_zero]
  constructor
  · rintro ((h|h)|h)
    · exact (nz h).elim
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h.symm)
  · rintro (rfl|rfl) <;> simp

private theorem row_product [DecidableEq K] (A : Submodule F K) [Fintype A] (x : A) (nx : x≠0)
    (size : 4≤Fintype.card A) :
    (∏ y : A, if row A x y=0 then 1 else row A x y)=
      (x:K)^(Fintype.card A-4)*(∏ y∈(univ.erase (0:A)),(y:K))^2 := by
  classical
  let s : Finset A := univ.erase 0
  let t := s.erase x
  have hx : x∈s := mem_erase.mpr ⟨nx,mem_univ _⟩
  have card : t.card=Fintype.card A-2 := by simp [t,card_erase_of_mem hx,s];omega
  have trans : (∏ y∈t,((x:K)+(y:K)))=∏ y∈t,(y:K) := by
    apply prod_bij (fun y _ => x+y)
    · intro y hy
      obtain ⟨ne,mem⟩ := mem_erase.mp hy
      have nz := (mem_erase.mp mem).1
      exact mem_erase.mpr ⟨fun h => nz (add_left_cancel (h.trans (add_zero x).symm)),
        mem_erase.mpr ⟨fun h => ne (by
          have q := congrArg (fun u : A => x+u) h
          simpa [←add_assoc,ZModModule.add_self] using q),mem_univ _⟩⟩
    · intro a _ b _ e;exact add_left_cancel e
    · intro y hy
      obtain ⟨ne,mem⟩ := mem_erase.mp hy
      have nz := (mem_erase.mp mem).1
      have twice : x+(x+y)=y := by rw [←add_assoc,ZModModule.add_self,zero_add]
      refine ⟨x+y,mem_erase.mpr ⟨fun e => nz (add_left_cancel (e.trans (add_zero x).symm)),
        mem_erase.mpr ⟨fun e => ne (by rw [←twice,e,add_zero]),mem_univ _⟩⟩,twice⟩
    · intro y _;rfl
  let g (y:A) : K := if row A x y=0 then 1 else row A x y
  have prod : (∏ y:A,g y)=∏ y∈t,bracket (x:K) (y:K) := by
    rw [←prod_erase univ (a:=0) (show g 0=1 by simp [g])]
    rw [←prod_erase s (a:=x) (show g x=1 by simp [g,root_iff A nx])]
    apply prod_congr rfl
    intro y hy
    have h := mem_erase.mp hy
    change (if row A x y=0 then 1 else row A x y)=row A x y
    rw [if_neg (fun z => ((root_iff A nx y).mp z).elim (mem_erase.mp h.2).1 h.1)]
  change (∏ y:A,g y)=_
  rw [prod]
  simp only [bracket,prod_mul_distrib,prod_const,card,trans]
  have old := prod_erase_mul s (fun v:A => (v:K)) hx
  change (∏ v∈t,(v:K))*(x:K)=∏ v∈s,(v:K) at old
  change _=(x:K)^(_-4)*(∏ v∈s,(v:K))^2
  rw [←old,show Fintype.card A-2=(Fintype.card A-4)+2 by omega,pow_add]
  ring

private theorem product_of_range [Fintype K] [DecidableEq K] (A : Submodule F K) [Fintype A] (x : A)
    (nx : x≠0) (S : Submodule F K) [DecidablePred (·∈S)] (im : (row A x).range=S) :
    (∏ y : A, if row A x y=0 then 1 else row A x y)=
      ∏ z : K, (if z=0 then 1 else z)^(if z∈S then 2 else 0 : ℕ) := by
  classical
  let f := row A x
  let g (u : K) : K := if u=0 then 1 else u
  have two : (univ.filter (fun y : A => f y=0)).card=2 := by
    have set : univ.filter (fun y : A => f y=0)={0,x} := by ext y;simp [f,root_iff A nx]
    rw [set,card_pair nx.symm]
  have fibre (z : K) : (univ.filter (fun y : A => f y=z)).card=if z∈S then 2 else 0 := by
    by_cases hz : z∈S
    · rw [if_pos hz]
      refine Eq.trans ?_ two
      apply AddMonoidHom.card_fiber_eq_of_mem_range f
      · change z∈(row A x).range
        rwa [im]
      · exact ⟨0,f.map_zero⟩
    · rw [if_neg hz,card_eq_zero,filter_eq_empty_iff]
      intro y _ eq
      apply hz
      rw [←im,←eq]
      exact ⟨y,rfl⟩
  have grouped := prod_fiberwise_eq_prod_filter' (univ : Finset A) (univ : Finset K) f g
  simp [prod_const] at grouped
  change (∏ y:A,g (f y))=_
  rw [←grouped]
  exact prod_congr rfl (fun z _ => by rw [fibre])

private theorem ker_row (A : Submodule F K) {x : A} (nx : x≠0) :
    (row A x).ker=Submodule.span F {x} := by
  apply le_antisymm
  · intro y hy
    rcases (root_iff A nx y).mp hy with rfl|rfl
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span (Set.mem_singleton _)
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ((root_iff A nx x).mpr (Or.inr rfl)))

/-- The pair brackets of a binary subspace of dimension at least three carry
at least as many independent dimensions as the input. -/
theorem bracket_rank [Fintype K] (A S : Submodule F K) (big : 3≤Module.finrank F A)
    (all : ∀ x∈A,∀ y∈A,bracket x y∈S) : Module.finrank F A≤Module.finrank F S := by
  classical
  by_contra! small
  let _ := Fintype.ofFinite A
  have im (x : A) (nx : x≠0) : (row A x).range=S := by
    have h := (row A x).finrank_range_add_finrank_ker
    rw [ker_row A nx,finrank_span_singleton nx] at h
    exact Submodule.eq_of_le_of_finrank_le (by rintro _ ⟨y,rfl⟩;exact all _ x.property _ y.property) (by omega)
  have card : 8≤Fintype.card A := by
    rw [Module.card_eq_pow_finrank (K:=F),ZMod.card]
    exact Nat.pow_le_pow_right (by decide : 0<2) big
  let D := Fintype.card A-4
  let P := ∏ y∈(univ.erase (0:A)),(y:K)
  have nP : P^2≠0 := pow_ne_zero _ (prod_ne_zero_iff.mpr (fun y hy eq =>
    (mem_erase.mp hy).1 (Subtype.ext eq)))
  obtain ⟨b,nb⟩ : ∃ b:A,b≠0 := by
    obtain ⟨x,hx,nx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show A≠⊥ by intro z;rw [z,finrank_bot] at big;omega)
    exact ⟨⟨x,hx⟩,fun z => nx (congrArg Subtype.val z)⟩
  have value (x:A) (nx:x≠0) : (x:K)^D=(b:K)^D := by
    apply mul_right_cancel₀ nP
    calc
      _ = _ := (row_product A x nx (by omega)).symm
      _ = _ := product_of_range A x nx S (im x nx)
      _ = _ := (product_of_range A b nb S (im b nb)).symm
      _ = _ := row_product A b nb (by omega)
  let E := (univ.erase (0:A)).image (fun x : A => (x:K))
  have bound := Polynomial.card_le_degree_of_subset_roots
    (p:=Polynomial.X^D-Polynomial.C ((b:K)^D)) (Z:=E) (by
      intro x hx
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
      rw [Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero (show 0<D by dsimp [D];omega) _)]
      simp [Polynomial.IsRoot,value v (mem_erase.mp hv).1])
  rw [Polynomial.natDegree_X_pow_sub_C] at bound
  have size : E.card=Fintype.card A-1 := by
    rw [card_image_of_injective _ Subtype.val_injective,card_erase_of_mem (mem_univ _),card_univ]
  dsimp only [D] at bound
  omega

end Green51BracketRank
#print axioms Green51BracketRank.bracket_rank