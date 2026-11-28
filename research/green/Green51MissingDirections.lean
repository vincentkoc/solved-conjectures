import Green51Hyperplane

/-! # Missing directions immediately below the hyperplane threshold -/
open Finset Green53ParityThreshold
open scoped Classical Pointwise
namespace Green51NearThreshold
private theorem even_direction_list {G : Type*} [AddCommGroup G] [Module F G]
    (D : Set G) (P : Finset G) (inside : (P:Set G)⊆D) (k : ℕ)
    (even : 2 ∣ P.card) (bound : P.card≤2*k) (hd : (∑ x∈P,x)∈D) :
    ∃ v : Fin (2*k) → G, (∀ i,v i∈D) ∧ (∑ i,v i)∈D := by
  classical
  let a : Fin P.card → G := fun i => (P.equivFin.symm i).val
  have atD (i) : a i∈D := inside (P.equivFin.symm i).property
  let d := ∑ x∈P,x
  have sum : ∑ i,a i=d := by
    calc
      _ = ∑ x : ↥P,x.val := Equiv.sum_comp P.equivFin.symm _
      _ = d := sum_coe_sort P id
  obtain ⟨s,hs⟩ := even
  have size : 2*k=P.card+2*(k-s) := by omega
  rw [size]
  let v := Fin.append a (fun _ : Fin (2*(k-s)) => d)
  refine ⟨v,Fin.addCases (fun i => by simpa [v] using atD i)
    (fun i => by simpa [v] using hd), ?_⟩
  rw [Fin.sum_univ_add]; simp only [v,Fin.append_left,Fin.append_right,sum,sum_const,
    card_univ,Fintype.card_fin,mul_comm 2 (k-s),mul_nsmul,two_nsmul,ZModModule.add_self,add_zero]
  exact hd

private theorem complement_sum {G : Type*} [AddCommGroup G] [Module F G]
    (B T : Finset G) (sub : T⊆B) :
    (∑ b∈B,b) + (∑ b∈B\T,b) = ∑ b∈T,b := by
  have e := sum_sdiff sub (f:=id)
  change (∑ b∈B\T,b)+(∑ b∈T,b)=∑ b∈B,b at e
  rw [← e,add_right_comm,ZModModule.add_self,zero_add]

private theorem subset_sum {G : Type*} [AddCommGroup G] [Module F G] (B : Finset G)
    (x : G) (hx : x∈Submodule.span F (↑B:Set G)) :
    ∃ S⊆B, ∑ b∈S,b=x := by
  classical
  have mem : x∈Submodule.span F (Set.range (fun b : ↥B => b.val)) := by
    rwa [Subtype.range_coe_subtype]
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp mem
  let T := (univ : Finset ↥B).filter (fun b => c b=1)
  let incl : ↥B ↪ G := ⟨Subtype.val,Subtype.val_injective⟩
  refine ⟨T.map incl,?_,?_⟩
  · intro b hb
    obtain ⟨y,_,rfl⟩ := mem_map.mp hb; exact y.property
  · rw [sum_map]; change ∑ b∈T,b.val=x
    rw [←hc]; simp only [T,sum_filter]; apply sum_congr rfl; intro b _
    have h (z:F) : z=0 ∨ z=1 := by fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl
    rcases h (c b) with h|h <;> simp [h]

/-- In even rank, a set of directions with maximal odd girth consists of a
basis and its total sum. -/
theorem frame_of_no_short {G : Type*} [AddCommGroup G] [Module F G] [Module.Finite F G]
    (k : ℕ) (rank : Module.finrank F G=2*k) (D : Set G)
    (odd : ¬ ∃ l : G →ₗ[F] F, ∀ x∈D,l x=1)
    (short : ∀ T : Finset G, (T:Set G)⊆D → 2∣T.card → T.card<2*k → (∑ x∈T,x)∉D) :
    ∃ B : Finset G, B.card=2*k ∧ LinearIndepOn F id (B:Set G) ∧
      D=(B:Set G)∪{∑ b∈B,b} := by
  classical
  obtain ⟨B,sub,card,span,ind⟩ := Submodule.exists_finset_span_eq_linearIndepOn F D
  obtain ⟨l,hl⟩ := Module.exists_dual_forall_apply_eq_one ind
  change ∀ x∈B,l x=1 at hl
  have fail : ¬∀ x∈D,l x=1 := fun h => odd ⟨l,h⟩
  push Not at fail
  obtain ⟨d,hd,bad⟩ := fail
  have bit (z:F) : z=0 ∨ z=1 := by fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl
  have ld := (bit (l d)).resolve_right bad
  have rep (x : G) (hx : x∈D) : ∃ T⊆B, ∑ b∈T,b=x := subset_sum B x (span.symm ▸ Submodule.subset_span hx)
  obtain ⟨P,pb,pd⟩ := rep d hd
  have pe : 2∣P.card := by
    have id := congrArg l pd
    change l (∑ x∈P,x)=l d at id
    rw [map_sum,ld,sum_eq_card_nsmul (fun x hx => hl x (pb hx))] at id
    simpa only [nsmul_eq_mul,mul_one,ZMod.natCast_eq_zero_iff] using id
  have dimB : B.card≤2*k := card.trans_le ((Submodule.finrank_le _).trans_eq rank)
  have psize : 2*k≤P.card := by
    by_contra! h
    exact short P (fun _ hx => sub (pb hx)) pe h (pd ▸ hd)
  have big := card_le_card pb
  have pB := eq_of_subset_of_card_le pb (by omega)
  have sb : B.card=2*k := by omega
  have sumd : ∑ x∈B,x=d := pB ▸ pd
  have nd : d∉B := fun h => bad (hl _ h)
  refine ⟨B,sb,ind,Set.Subset.antisymm ?_ (Set.union_subset sub (Set.singleton_subset_iff.mpr (sumd ▸ hd)))⟩
  intro x hx
  by_cases inside : x∈B
  · exact Or.inl inside
  by_cases same : x=d
  · exact Or.inr (same.trans sumd.symm)
  exfalso
  obtain ⟨T,tb,xt⟩ := rep x hx
  have tc := card_le_card tb
  by_cases even : 2∣T.card
  · have full : T.card=2*k := by
      by_contra! gap
      exact short T (fun _ hx => sub (tb hx)) even (by omega) (xt ▸ hx)
    have eq := eq_of_subset_of_card_le tb (by omega)
    exact same (xt.symm.trans (eq ▸ sumd))
  have low : 3≤T.card := by
    by_contra! h
    have one : T.card=1 := by omega
    obtain ⟨y,ty⟩ := card_eq_one.mp one
    rw [ty] at xt tb; simp only [sum_singleton] at xt
    exact inside (xt ▸ tb (mem_singleton_self y))
  let Q := insert d (B\T)
  have nq : d∉B\T := fun h => nd (mem_sdiff.mp h).1
  have count : Q.card=(B.card-T.card)+1 := by dsimp only [Q]; rw [card_insert_of_notMem nq,card_sdiff_of_subset tb]
  have qsub : (Q:Set G)⊆D := by
    intro y hy; rcases mem_insert.mp hy with rfl|h
    · exact hd
    · exact sub (mem_sdiff.mp h).1
  apply short Q qsub (by omega) (by omega)
  have sum := complement_sum B T tb
  rw [sumd,xt] at sum
  dsimp only [Q]; rw [sum_insert nq,sum]; exact hx


/-- Just below the sharp threshold, an even-dimensional double either contains
a linear hyperplane or its missing directions are a basis and their sum. -/
theorem even_missing_directions (s : ℕ) (A : Finset (Fin (2*(s+1)) → F))
    (large : 2^(2*(s+1)) < 2*A.card + 4*(2*s).choose s) :
    (∃ l : (Fin (2*(s+1)) → F) →ₗ[F] F, ∀ x∈l.ker,x∈A+A) ∨
    ∃ B : Finset (Fin (2*(s+1)) → F), B.card=2*(s+1) ∧ LinearIndepOn F id (B:Set (Fin (2*(s+1)) → F)) ∧
      (((A+A : Finset _) : Set (Fin (2*(s+1)) → F))ᶜ) = (B:Set (Fin (2*(s+1)) → F)) ∪ {∑ x∈B,x} := by
  classical
  let D := (((A+A : Finset _) : Set (Fin (2*(s+1)) → F))ᶜ)
  by_cases ok : ∃ l : (Fin (2*(s+1)) → F) →ₗ[F] F, ∀ x∈l.ker,x∈A+A
  · exact Or.inl ok
  right
  apply frame_of_no_short (s+1) (by simp) D
  · rintro ⟨l,h⟩
    apply ok
    refine ⟨l,?_⟩
    intro x hx
    by_contra no
    exact zero_ne_one ((LinearMap.mem_ker.mp hx).symm.trans (h x no))
  · intro P sub parity length sumD
    obtain ⟨v,miss,last⟩ := even_direction_list D P sub s parity (by omega) sumD
    have bound := Green51Hyperplane.folded_pullback A s v
      (fun i => by simpa only [D,Set.mem_compl_iff,mem_coe,mem_add] using miss i)
      (by simpa only [D,Set.mem_compl_iff,mem_coe,mem_add] using last)
    simp only [F,Fintype.card_fun,Fintype.card_fin,ZMod.card] at bound
    have size : (2:ℕ)^(2*(s+1))=4*2^(2*s) := by rw [Nat.mul_add,pow_add]; ring
    have contradiction := Nat.mul_lt_mul_of_pos_right large (by positivity : 0<(2:ℕ)^(2*s))
    rw [size] at bound contradiction
    nlinarith only [bound,contradiction]

/-- In the exceptional case the number of missing directions exceeds the
ambient dimension by exactly one. -/
theorem even_missing_count (s : ℕ) (A : Finset (Fin (2*(s+1)) → F))
    (large : 2^(2*(s+1)) < 2*A.card + 4*(2*s).choose s)
    (no : ¬∃ l : (Fin (2*(s+1)) → F) →ₗ[F] F, ∀ x∈l.ker,x∈A+A) :
    (A+A)ᶜ.card=2*(s+1)+1 := by
  classical
  obtain ⟨B,size,ind,missing⟩ := (even_missing_directions s A large).resolve_left no
  obtain ⟨l,hl⟩ := Module.exists_dual_forall_apply_eq_one ind
  change ∀ x∈B,l x=1 at hl
  have off : (∑ b∈B,b)∉B := by
    intro h
    have one := hl _ h
    rw [map_sum,sum_eq_card_nsmul hl,size,mul_comm 2 _,mul_nsmul,two_nsmul,ZModModule.add_self] at one
    exact zero_ne_one one
  have eq : (A+A)ᶜ=insert (∑ b∈B,b) B := by
    ext x
    rw [Finset.mem_compl]
    change x∈(((A+A : Finset _) : Set (Fin (2*(s+1)) → F))ᶜ) ↔ _
    rw [missing]; simp [or_comm]
  rw [eq,card_insert_of_notMem off,size]

end Green51NearThreshold
#print axioms Green51NearThreshold.frame_of_no_short
#print axioms Green51NearThreshold.even_missing_directions

#print axioms Green51NearThreshold.even_missing_count
