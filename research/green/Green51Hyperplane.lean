import Green53FoldedCube

/-! # Hyperplanes in binary sumsets at density near one half -/

open Finset Green53Threshold Green53ParityThreshold Green53FoldedCube
open scoped Classical Pointwise
namespace Green51Hyperplane

private theorem bits (a : F) : a=0 ∨ a=1 := by fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- Either one linear functional is one on all prescribed directions, or an
even list of them has its sum among the prescribed directions as well. -/
theorem direction_alternative {G : Type*} [AddCommGroup G] [Module F G]
    [Module.Finite F G] (D : Set G) :
    (∃ l : G →ₗ[F] F, ∀ x∈D,l x=1) ∨
    ∃ v : Fin (2*(Module.finrank F G/2)) → G, (∀ i,v i∈D) ∧ (∑ i,v i)∈D := by
  classical
  obtain ⟨B,sub,card,span,ind⟩ := Submodule.exists_finset_span_eq_linearIndepOn F D
  obtain ⟨l,hl⟩ := Module.exists_dual_forall_apply_eq_one ind
  by_cases all : ∀ x∈D,l x=1
  · exact Or.inl ⟨l,all⟩
  right
  push Not at all
  obtain ⟨d,hd,bad⟩ := all
  have zero := (bits (l d)).resolve_right bad
  have mem : d∈Submodule.span F (Set.range (fun b : ↥B => b.val)) := by
    rw [Subtype.range_coe_subtype]; exact span.symm ▸ Submodule.subset_span hd
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp mem
  let S := (univ : Finset ↥B).filter (fun b => c b=1)
  have total : ∑ b∈S,b.val=d := by
    rw [←hc]; simp only [S,sum_filter]
    apply sum_congr rfl; intro b _
    rcases bits (c b) with h|h <;> simp [h]
  have one (b : ↥B) : l b.val=1 := hl b.val b.property
  have parity : 2 ∣ S.card := by
    have e := congrArg l total
    simp only [map_sum,one,sum_const,nsmul_eq_mul,mul_one,zero] at e
    exact (ZMod.natCast_eq_zero_iff _ _).mp e
  have len : S.card ≤ Module.finrank F G := by
    calc
      S.card ≤ Fintype.card ↥B := S.card_le_univ
      _ = Module.finrank F (Submodule.span F D) := by simpa using card
      _ ≤ _ := Submodule.finrank_le _
  let a : Fin S.card → G := fun i => (S.equivFin.symm i).val.val
  have inD (i) : a i∈D := sub (S.equivFin.symm i).val.property
  have asum : ∑ i,a i=d := by
    calc
      _ = ∑ b : ↥S,b.val.val := Equiv.sum_comp S.equivFin.symm _
      _ = d := by rwa [sum_coe_sort]
  obtain ⟨u,hu⟩ := parity
  let pad := Module.finrank F G/2-u
  have dim : 2*(Module.finrank F G/2)=S.card+2*pad := by dsimp [pad]; omega
  rw [dim]
  let v := Fin.append a (fun _ : Fin (2*pad) => d)
  refine ⟨v,Fin.addCases (fun i => by simpa [v] using inD i)
      (fun i => by simpa [v] using hd), ?_⟩
  rw [Fin.sum_univ_add]; simp only [v,Fin.append_left,Fin.append_right,asum,sum_const,
    card_univ,Fintype.card_fin,mul_comm 2 pad,mul_nsmul,two_nsmul,ZModModule.add_self,
    add_zero]
  exact hd


/-- Averaging an independent folded-cube preimage over all its translates bounds the density. -/
theorem folded_pullback {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
    (A : Finset G) (k : ℕ) (v : Fin (2*k) → G)
    (miss : ∀ i,v i∉A+A) (last : (∑ i,v i)∉A+A) :
    (2*A.card)*2^(2*k) + Fintype.card G*(2*k).choose k ≤ Fintype.card G*2^(2*k) := by
  classical
  let L (x : Fin (2*k) → F) := ∑ i,x i • v i
  have step (x y : Fin (2*k) → F) : L (x+y)=L x+L y := by
    simp [L,add_smul,sum_add_distrib]
  have unit (i : Fin (2*k)) : L (Pi.single i 1)=v i := by
    simp [L]
  have ones : L (fun _ => 1)=∑ i,v i := by simp [L]
  let row (a : G) := univ.filter (fun x => a+L x∈A)
  have dis (x d : G) (hx : x∈A) (hd : d∉A+A) : x+d∉A := by
    intro h
    apply hd
    have eq : x+(x+d)=d := by rw [←add_assoc,ZModModule.add_self,zero_add]
    exact eq ▸ add_mem_add hx h
  have edges (a : G) (x) (hx : x∈row a) :
      (∀ i,x+Pi.single i 1∉row a) ∧ x+(fun _ => 1)∉row a := by
    have ax := (mem_filter.mp hx).2
    constructor
    · intro i
      simpa [row,step,unit,←add_assoc] using dis (a+L x) (v i) ax (miss i)
    · simpa [row,step,ones,←add_assoc] using dis (a+L x) _ ax last
  have per (a : G) := folded_independent_bound k (Fintype.card_fin _) (row a) (edges a)
  have tot : ∑ a,(row a).card=2^(2*k)*A.card := by
    simp only [row,card_filter]
    rw [sum_comm]
    have shift (x : Fin (2*k) → F) :
        (∑ a : G,if a+L x∈A then 1 else 0)=A.card := by
      calc
        _ = ∑ a : G,if a∈A then 1 else 0 := Equiv.sum_comp (Equiv.addRight (L x)) _
        _ = A.card := by simp
    simp [shift,F,ZMod.card]
  have combined := sum_le_sum (s:=univ) (fun a _ => per a)
  simp only [sum_add_distrib,←mul_sum,tot,sum_const,card_univ,nsmul_eq_mul] at combined
  simpa [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using combined

/-- Above the central-binomial threshold the double contains the kernel of a
linear functional, a subspace of codimension at most one. -/
theorem hyperplane_above {n : ℕ} (A : Finset (Fin n → F))
    (large : 2^n < 2*A.card+2^(n%2)*(2*(n/2)).choose (n/2)) :
    ∃ l : (Fin n → F) →ₗ[F] F, (l.ker : Set (Fin n → F)) ⊆ ((A+A : Finset _) : Set _) := by
  classical
  let D : Set (Fin n → F) := ((A+A : Finset _) : Set _)ᶜ
  have alt := direction_alternative D
  have dm : Module.finrank F (Fin n → F)=n := by simp
  rw [dm] at alt
  rcases alt with ⟨l,ones⟩|⟨v,miss,last⟩
  · refine ⟨l,?_⟩
    intro x hx
    by_contra out
    have := ones x out
    exact zero_ne_one ((LinearMap.mem_ker.mp hx).symm.trans this)
  · have b := folded_pullback A (n/2) v (fun i => by simpa only [D,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_add] using miss i) (by simpa only [D,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_add] using last)
    simp only [F,Fintype.card_fun,Fintype.card_fin,ZMod.card] at b
    have split : (2:ℕ)^n=2^(n%2)*2^(2*(n/2)) := by rw [←pow_add,Nat.mod_add_div]
    let w := 2^(2*(n/2))
    have b' : (2*A.card+2^(n%2)*(2*(n/2)).choose (n/2))*w≤2^n*w := by
      calc
        _ = 2*A.card*w+2^n*(2*(n/2)).choose (n/2) := by rw [split]; dsimp [w]; ring
        _ ≤ _ := b
    exact False.elim ((Nat.not_lt_of_ge b') (Nat.mul_lt_mul_of_pos_right large (by dsimp [w]; positivity)))

end Green51Hyperplane
#print axioms Green51Hyperplane.direction_alternative
#print axioms Green51Hyperplane.hyperplane_above
#print axioms Green51Hyperplane.folded_pullback
