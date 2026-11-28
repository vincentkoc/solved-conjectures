import Green53ParityOscillation

/-! # Simultaneous threshold margins from independent coordinate blocks -/
open Finset Green53ParityThreshold Green53Threshold
open scoped Classical Pointwise
namespace Green53ParityOscillation

/-- One forbidden choice per coordinate line cannot cover an n-dimensional grid
when each side has more than n points. -/
theorem avoid_grid {I T : Type*} [Fintype I] [Fintype T] (big : Fintype.card I<Fintype.card T)
    (bad : I → (I → T) → Prop)
    (unique : ∀ i x y, bad i x → bad i y → (∀ j,j≠i → x j=y j) → x=y) :
    ∃ x,∀ i,¬bad i x := by
  classical
  let B i := univ.filter (bad i)
  have cap (i : I) : Fintype.card T*(B i).card≤Fintype.card (I → T) := by
    let put (z : T × B i) := Function.update z.2.val i z.1
    have inj : Function.Injective put := by
      rintro ⟨v,x⟩ ⟨w,y⟩ eq
      have vw := congrFun eq i
      have xy : x.val=y.val := unique i x.val y.val (mem_filter.mp x.property).2
        (mem_filter.mp y.property).2 (fun j hj => by
          simpa only [put,Function.update_of_ne hj] using congrFun eq j)
      exact Prod.ext (by simpa only [put,Function.update_self] using vw) (Subtype.ext xy)
    simpa only [Fintype.card_prod,Fintype.card_coe] using Fintype.card_le_of_injective put inj
  have bound : Fintype.card T*(univ.biUnion B).card≤Fintype.card I*Fintype.card (I → T) := calc
    _ ≤ Fintype.card T*∑ i,(B i).card := Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ i,Fintype.card T*(B i).card := mul_sum _ _ _
    _ ≤ ∑ _i : I,Fintype.card (I → T) := sum_le_sum (fun i _ => cap i)
    _ = _ := by simp
  have pos : 0<Fintype.card (I → T) := by rw [Fintype.card_fun]; exact pow_pos (by omega) _
  have strict : (univ.biUnion B).card<(univ : Finset (I → T)).card := by
    rw [card_univ]
    by_contra! contra
    have e := (Nat.mul_le_mul_left (Fintype.card T) contra).trans bound
    exact (Nat.mul_lt_mul_of_pos_right big pos).not_ge e
  obtain ⟨x,hx⟩ := exists_mem_notMem_of_card_lt_card strict
  exact ⟨x,fun i h => hx.2 (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,h⟩⟩)⟩
private theorem select_blocks {J : Type*} [Fintype J] (d : ℕ) :
    ∀ n (A : Fin n → J → ℝ) (S : Finset J), n*d≤S.card →
    ∃ t : Fin n → Finset J, (∀ i,t i⊆S ∧ (t i).card=d) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      ∀ i j,j∈t i → ∀ l∈S,(∀ p,l∉t p) → A i l≤A i j := by
  classical
  intro n
  induction n with
  | zero => intro A S h; exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | succ n ih =>
    intro A S h
    obtain ⟨u,us,uc,order⟩ := largest (A 0) S d
    have cnt : u.card=d := uc.trans (min_eq_left (by rw [Nat.succ_mul] at h; omega))
    have rem : n*d≤(S\u).card := by rw [card_sdiff_of_subset us,cnt,Nat.succ_mul] at *; omega
    obtain ⟨v,vs,vp,vo⟩ := ih (fun i => A i.succ) (S\u) rem
    let t : Fin (n+1) → Finset J := Fin.cases u v
    refine ⟨t,Fin.cases ⟨us,cnt⟩ (fun i => ⟨(vs i).1.trans sdiff_subset,(vs i).2⟩),?_,?_⟩
    · have dis (i : Fin n) : Disjoint u (v i) := Finset.disjoint_left.mpr
        (fun j hj hp => (mem_sdiff.mp ((vs i).1 hp)).2 hj)
      intro i k
      refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) k
      · intro h'; exact (h' rfl).elim
      · intro _; exact dis b
      · intro _; exact (dis a).symm
      · intro ne; exact vp (fun eq => ne (congrArg Fin.succ eq))
    · intro i
      refine Fin.cases ?_ (fun p => ?_) i
      · intro j hj l hl out
        exact order j hj l hl (out 0)
      · intro j hj l hl out
        exact vo p j hj l (mem_sdiff.mpr ⟨hl,out 0⟩) (fun a => out a.succ)

end Green53ParityOscillation
#print axioms Green53ParityOscillation.avoid_grid
