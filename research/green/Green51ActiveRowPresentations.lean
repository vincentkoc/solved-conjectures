import Green51RestoreEmptyRows
import Green51SubspaceGrowth

/-! # Uniform counting of distinguishable words on active rows in arbitrary ambient spaces -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

private theorem live_labelled_rows {I J H : Type*} [AddCommGroup H] [Module F H]
    (A B : I → Finset H) (a b : J → H) (row : J → I) (u : H ≃ₗ[F] H)
    (hu : ∀ i,u (a i)=b i)
    (ma : ∀ j x,x∈A j ↔ ∃ i,row i=j ∧ a i=x)
    (mb : ∀ j x,x∈B j ↔ ∃ i,row i=j ∧ b i=x) :
    ∀ j,(A j).map u.toEquiv.toEmbedding=B j := by
  intro j
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
    obtain ⟨i,hi,rfl⟩ := (ma j x).mp hx
    exact (mb j _).mpr ⟨i,hi,(hu i).symm⟩
  · intro hy
    obtain ⟨i,hi,rfl⟩ := (mb j y).mp hy
    exact mem_map.mpr ⟨a i,(ma j _).mpr ⟨i,hi,rfl⟩,hu i⟩

theorem active_core_labels {Q H : Type*} [AddCommGroup H] (h b : ℕ) (A : Q → Fin b → Finset H)
    (total : ∀ q,∑ i,(A q i).card=h) (live : ∀ q i,(A q i).Nonempty) :
    ∃ (row : Q → Fin (h-b) → Fin b) (v : Q → Fin (h-b) → H),
      ∀ q j x,x∈rowCore (A q j) ↔ ∃ i,row q i=j ∧ v q i=x := by
  classical
  have sum_core (q : Q) : ∑ i,(rowCore (A q i)).card=h-b := by
    have eq : (∑ i,(rowCore (A q i)).card) + ∑ _ : Fin b,1 = h := by
      apply Eq.trans _ (total q)
      rw [←sum_add_distrib]
      exact sum_congr rfl fun i _ => by simpa only [if_pos (live q i)] using core_occupancy (A q i)
    simpa using congrArg (fun n => n-b) eq
  let sites (q : Q) : Fin (h-b) ≃ ((i : Fin b) × ↥(rowCore (A q i))) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_sigma,sum_core])
  let row (q : Q) (i : Fin (h-b)) := (sites q i).1
  let v (q : Q) (i : Fin (h-b)) : H := (sites q i).2.val
  have mem_core (q : Q) (j : Fin b) (x : H) :
      x∈rowCore (A q j) ↔ ∃ i,row q i=j ∧ v q i=x := by
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := (sites q).surjective ⟨j,⟨x,hx⟩⟩
      exact ⟨i,congrArg Sigma.fst hi,congrArg (fun z => z.2.val) hi⟩
    · rintro ⟨i,rfl,rfl⟩
      exact (sites q i).2.property
  exact ⟨row,v,mem_core⟩

theorem match_labelled_cores {I J H : Type*} [AddCommGroup H] [Module F H]
    {A B : I → Finset H} {a b : J → H} {row : J → I} (u : H ≃ₗ[F] H)
    (live : ∀ i,(A i).Nonempty ↔ (B i).Nonempty) (hu : ∀ j,u (a j)=b j)
    (ma : ∀ j x,x∈rowCore (A j) ↔ ∃ i,row i=j ∧ a i=x)
    (mb : ∀ j x,x∈rowCore (B j) ↔ ∃ i,row i=j ∧ b i=x) : WordMatch A B :=
  match_of_cores _ _ u live (live_labelled_rows _ _ a b row u hu ma mb)

theorem count_active_presentations {Q H : Type*} [Finite Q] [AddCommGroup H] [Module F H]
    [FiniteDimensional F H] (h b : ℕ) (A : Q → Fin b → Finset H)
    (total : ∀ q,∑ i,(A q i).card=h) (live : ∀ q i,(A q i).Nonempty)
    (separate : ∀ p q,WordMatch (A p) (A q) → p=q) :
    Nat.card Q ≤ b^(h-b)*((h-b+1)*2^((h-b)*(h-b)/4+(h-b))) := by
  classical
  obtain ⟨row,v,mem_core⟩ := active_core_labels h b A total live
  let code (q : Q) : (Fin (h-b) → Fin b) × Submodule F (Fin (h-b) →₀ F) :=
    (row q, LinearMap.ker (Finsupp.linearCombination F (v q)))
  have inj : Function.Injective code := by
    intro p q eq
    have sr : row p = row q := congrArg Prod.fst eq
    obtain ⟨u,hu⟩ := (tuple_ker_iff (v p) (v q)).mp (congrArg Prod.snd eq)
    apply separate p q
    apply match_labelled_cores u (fun i => ⟨fun _ => live q i,fun _ => live p i⟩) hu (mem_core p)
    rw [sr]
    exact mem_core q
  have size := Nat.card_le_card_of_injective code inj
  rw [Nat.card_prod,Nat.card_fun,Nat.card_fin,Nat.card_fin] at size
  exact size.trans (Nat.mul_le_mul_left _ (Green51SubspaceGrowth.all_subspaces_le (Fin (h-b) →₀ F) (n := h-b) (by simp)))

theorem count_distinguished_presentations {Q H I : Type*} [Finite Q] [Fintype I]
    [AddCommGroup H] [Module F H] [FiniteDimensional F H] (h b : ℕ) (A : Q → I → Finset H)
    (total : ∀ q,∑ i,(A q i).card=h) (occ : ∀ q,(occupiedRows (A q)).card=b)
    (separate : ∀ p q,WordMatch (A p) (A q) → p=q) :
    Nat.card Q ≤ b^(h-b)*((h-b+1)*2^((h-b)*(h-b)/4+(h-b))) := by
  classical
  let e (q : Q) : Fin b ≃ ↥(occupiedRows (A q)) := Fintype.equivOfCardEq (by simp [occ])
  let C (q : Q) (j : Fin b) := A q (e q j)
  apply count_active_presentations h b C
  · intro q
    exact ((e q).sum_comp (fun i => (A q i.val).card)).trans ((occupied_sum (A q)).trans (total q))
  · intro q i
    exact (mem_filter.mp (e q i).property).2
  · intro p q m
    exact separate p q (restore_empty_rows _ _ (e p) (e q) m)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.active_core_labels
#print axioms Green51FrameIsomorphisms.match_labelled_cores
#print axioms Green51FrameIsomorphisms.count_active_presentations
#print axioms Green51FrameIsomorphisms.count_distinguished_presentations
