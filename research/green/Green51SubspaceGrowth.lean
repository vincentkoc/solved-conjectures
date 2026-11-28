import Mathlib

/-! # Counting binary subspaces by ordered bases -/

namespace Green51SubspaceGrowth
local notation "F" => ZMod 2
variable (V : Type*) [AddCommGroup V] [Module F V] [Finite V]
abbrev Planes (d : ℕ) := {U : Submodule F V // Module.finrank F U=d}
abbrev Frames (d : ℕ) := {v : Fin d → V // LinearIndependent F v}

private def forget {d : ℕ} (s : Σ U : Planes V d, Frames U.val d) : Frames V d :=
  ⟨s.1.val.subtype ∘ s.2.val,s.2.property.map' _ (Submodule.ker_subtype _)⟩

private theorem forget_span {d : ℕ} (s : Σ U : Planes V d, Frames U.val d) :
    Submodule.span F (Set.range (forget V s).val)=s.1.val := by
  apply Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr ?_)
  · rw [s.1.property,finrank_span_eq_card (forget V s).property,Fintype.card_fin]
  · rintro _ ⟨i,rfl⟩; exact (s.2.val i).property

private theorem forget_bijective (d : ℕ) : Function.Bijective (forget V (d := d)) := by
  constructor
  · rintro ⟨⟨U,hU⟩,a⟩ ⟨⟨W,hW⟩,b⟩ eq
    have same : U=W := (forget_span V ⟨⟨U,hU⟩,a⟩).symm.trans
      ((congrArg (fun v : Frames V d => Submodule.span F (Set.range v.val)) eq).trans
      (forget_span V ⟨⟨W,hW⟩,b⟩))
    subst W
    congr 1
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun (congrArg Subtype.val eq) i)
  · intro v
    let U := Submodule.span F (Set.range v.val)
    have rank : Module.finrank F U=d := by simpa [U] using finrank_span_eq_card v.property
    let a : Fin d → U := fun i => ⟨v.val i,Submodule.subset_span ⟨i,rfl⟩⟩
    have li : LinearIndependent F a := (U.subtype.linearIndependent_iff U.ker_subtype).mp v.property
    exact ⟨⟨⟨U,rank⟩,⟨a,li⟩⟩,rfl⟩

theorem frame_count {d : ℕ} (dim : d≤Module.finrank F V) :
    Nat.card (Planes V d)*(∏ i : Fin d, (2^d-2^i.val)) =
      ∏ i : Fin d,(2^(Module.finrank F V)-2^i.val) := by
  classical
  let _ := Fintype.ofFinite (Planes V d)
  have count := Nat.card_congr (Equiv.ofBijective (forget V) (forget_bijective V d))
  have frames (U : Planes V d) : Nat.card (Frames U.val d)=∏ i : Fin d, (2^d-2^i.val) := by
    rw [card_linearIndependent (by rw [U.property]),U.property,ZMod.card]
  rw [Nat.card_sigma,card_linearIndependent dim,ZMod.card] at count
  simpa only [frames,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id] using count

theorem rank_count_le {d n : ℕ} (dim : Module.finrank F V=n) (hd : d≤n) :
    Nat.card (Planes V d) ≤ 2^(d*(n-d)+d) := by
  classical
  have hf := frame_count V (d := d) (dim.symm ▸ hd)
  rw [dim] at hf
  have upper : (∏ i : Fin d, (2^n-2^i.val)) ≤ (2^n)^d := by
    calc
      _ ≤ ∏ _ : Fin d, 2^n := Finset.prod_le_prod' fun i _ => Nat.sub_le _ _
      _ = _ := by simp
  have lower : (2^(d-1))^d ≤ ∏ i : Fin d,(2^d-2^i.val) := by
    calc
      _ = ∏ _ : Fin d, 2^(d-1) := by simp
      _ ≤ _ := Finset.prod_le_prod' fun i _ => by
        obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d≠0 by have := i.isLt;omega)
        have hle : 2^i.val≤2^k := Nat.pow_le_pow_right (by decide) (by have := i.isLt;omega)
        simp only [Nat.add_one_sub_one,pow_succ]
        omega
  have budget := ((Nat.mul_le_mul_left (Nat.card (Planes V d)) lower).trans_eq hf).trans upper
  rw [←pow_mul,←pow_mul] at budget
  have split : n*d≤d*(n-d)+d+(d-1)*d := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hd
    cases d with
    | zero => simp
    | succ d => simp;nlinarith only []
  have bnd := budget.trans (Nat.pow_le_pow_right (by decide : 0<2) split)
  rw [pow_add] at bnd
  exact Nat.le_of_mul_le_mul_right bnd (by positivity)

private theorem quarter_product (a n : ℕ) (ha : a≤n) : a*(n-a) ≤ n*n/4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ha
  simp only [Nat.add_sub_cancel_left]
  have nonneg : 0≤((k:ℤ)-(a:ℤ))^2 := sq_nonneg _
  zify
  nlinarith

theorem all_subspaces_le {n : ℕ} (dim : Module.finrank F V=n) :
    Nat.card (Submodule F V) ≤ (n+1)*2^(n*n/4+n) := by
  classical
  let tag (P : Submodule F V) : Fin (n+1) :=
    ⟨Module.finrank F P,Nat.lt_succ_of_le (dim ▸ P.finrank_le)⟩
  let code (P : Submodule F V) : Σ i : Fin (n+1),Planes V i.val :=
    ⟨tag P,⟨P,rfl⟩⟩
  have inj : Function.Injective code := by
    intro x y e
    exact congrArg (fun s : Σ i : Fin (n+1),Planes V i.val => s.2.val) e
  have bound (i : Fin (n+1)) : Nat.card (Planes V i.val) ≤ 2^(n*n/4+n) := by
    have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have sq := quarter_product i.val n hi
    exact (rank_count_le V dim hi).trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add sq hi))
  have hh := Nat.card_le_card_of_injective code inj
  rw [Nat.card_sigma] at hh
  exact hh.trans ((Finset.sum_le_sum (fun i _ => bound i)).trans_eq (by simp))

end Green51SubspaceGrowth
#print axioms Green51SubspaceGrowth.frame_count
#print axioms Green51SubspaceGrowth.rank_count_le

#print axioms Green51SubspaceGrowth.all_subspaces_le
