import Green51AffineTranslationOrigins

/-! # Affine-rank counts from adjoining one fresh point -/

namespace Green51AffineTranslation
open Finset Green53ParityThreshold
open scoped Classical
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

noncomputable def affineRank (D : Finset G) := Module.finrank F (vectorSpan F (D : Set G))

/-- Inserting one point raises affine rank exactly when it lies outside the old affine span. -/
theorem affineRank_insert {D : Finset G} (live : D.Nonempty) (x : G) :
    affineRank (insert x D) = affineRank D + (if x∈affineSpan F (D : Set G) then 0 else 1) := by
  classical
  let W := affineSpan F (D : Set G)
  have c : affineSpan F (D : Set G) ≤ affineSpan F ((insert x D : Finset G) : Set G) :=
    affineSpan_mono F (by simpa only [coe_insert] using Set.subset_insert x (D : Set G))
  have dx : (affineSpan F (D : Set G)).direction=vectorSpan F (D : Set G) := direction_affineSpan ..
  have dx' : (affineSpan F ((insert x D : Finset G) : Set G)).direction=
      vectorSpan F ((insert x D : Finset G) : Set G) := direction_affineSpan ..
  by_cases h : x∈W
  · rw [if_pos h,add_zero]
    have eq : affineSpan F ((insert x D : Finset G) : Set G)=W := by
      apply le_antisymm _ c
      apply affineSpan_le.mpr
      rw [coe_insert]
      exact Set.insert_subset h (subset_affineSpan F (D : Set G))
    unfold affineRank
    rw [←dx',eq]
    exact congrArg (fun V : Submodule F G => Module.finrank F V) dx
  · rw [if_neg h]
    have strict : affineSpan F (D : Set G) < affineSpan F ((insert x D : Finset G) : Set G) := by
      refine lt_of_le_of_ne c (fun eq => h ?_)
      change x∈affineSpan F (D : Set G)
      rw [eq]
      exact mem_affineSpan F (show x∈((insert x D : Finset G) : Set G) from mem_insert_self ..)
    have lt := Submodule.finrank_lt_finrank_of_lt (AffineSubspace.direction_lt_of_nonempty strict (live.to_set.affineSpan F))
    rw [dx,dx'] at lt
    have upper := finrank_vectorSpan_insert_le_set (k := F) (D : Set G) x
    unfold affineRank
    rw [coe_insert] at lt ⊢
    omega

/-- Subsets of a prescribed size and affine rank. -/
noncomputable def rankLayer (G : Type*) [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
    (k j : ℕ) := ((univ : Finset G).powersetCard k).filter fun D => affineRank D=j

omit [DecidableEq G] in
theorem affine_span_card {D : Finset G} (live : D.Nonempty) :
    ((affineSpan F (D : Set G) : AffineSubspace F G) : Set G).toFinset.card=2^affineRank D := by
  classical
  obtain ⟨a,ha⟩ := live
  let W := affineSpan F (D : Set G)
  let v : W := ⟨a,mem_affineSpan F (show a∈(D : Set G) from ha)⟩
  let : Nonempty W := ⟨v⟩
  rw [Set.toFinset_card]
  change Fintype.card W=_
  rw [←Fintype.card_congr (Equiv.vaddConst v : W.direction ≃ W),Module.card_eq_pow_finrank (K := F),ZMod.card]
  exact congrArg (fun j : ℕ => 2^j) (congrArg (fun U : Submodule F G => Module.finrank F U) (direction_affineSpan F (D : Set G)))

private theorem insertion_options {D : Finset G} (live : D.Nonempty) (j : ℕ) :
    (Dᶜ.filter fun x => affineRank (insert x D)=j).card =
      (if affineRank D=j then 2^j-D.card else 0) +
      (if affineRank D+1=j then Fintype.card G-2^(j-1) else 0) := by
  classical
  let W := ((affineSpan F (D : Set G)) : Set G).toFinset
  have sub : D ⊆ W := fun x hx => Set.mem_toFinset.mpr (mem_affineSpan F (show x∈(D : Set G) from hx))
  have wsize : W.card=2^affineRank D := affine_span_card live
  have eq : (Dᶜ.filter fun x => affineRank (insert x D)=j) =
      (if affineRank D=j then W \ D else ∅) ∪ (if affineRank D+1=j then Wᶜ else ∅) := by
    ext x
    by_cases hx : x∈W
    · have h : x∈affineSpan F (D : Set G) := Set.mem_toFinset.mp hx
      by_cases same : affineRank D=j <;> by_cases raised : affineRank D+1=j <;>
        simp [affineRank_insert live,h,same,raised,hx]
    · have h : x∉affineSpan F (D : Set G) := fun hh => hx (Set.mem_toFinset.mpr hh)
      have out : x∉D := fun hh => hx (sub hh)
      by_cases same : affineRank D=j <;> by_cases raised : affineRank D+1=j <;>
        simp [affineRank_insert live,h,same,raised,hx,out]
  rw [eq]
  by_cases h : affineRank D=j
  · simp [h,card_sdiff_of_subset sub,wsize]
  · by_cases h' : affineRank D+1=j
    · have rank : affineRank D=j-1 := by omega
      simp only [if_neg h,if_pos h',empty_union,zero_add,card_compl]
      rw [wsize,rank]
    · simp [h,h']

private theorem marked_insertions (k j : ℕ) :
    (k+1)*(rankLayer G (k+1) j).card =
      ∑ D∈(univ : Finset G).powersetCard k, (Dᶜ.filter fun x => affineRank (insert x D)=j).card := by
  classical
  let K := (univ : Finset G).powersetCard k
  let L := rankLayer G (k+1) j
  let X := K.sigma fun D => Dᶜ.filter fun x => affineRank (insert x D)=j
  let Y := L.sigma fun T => T
  have bij : X.card=Y.card := by
    apply card_bij (fun a _ => ⟨insert a.2 a.1,a.2⟩)
    · rintro ⟨D,x⟩ hx
      obtain ⟨kD,xD⟩ := mem_sigma.mp hx
      obtain ⟨fresh,rank⟩ := mem_filter.mp xD
      have size := (mem_powersetCard.mp kD).2
      exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,(card_insert_of_notMem (mem_compl.mp fresh)).trans (by omega)⟩,
        rank⟩,mem_insert_self ..⟩
    · rintro ⟨D,x⟩ ha ⟨E,y⟩ hb eq
      have xy : x=y := congrArg (fun z : Σ _ : Finset G, G => z.2) eq
      subst y
      have u := mem_compl.mp (mem_filter.mp (mem_sigma.mp ha).2).1
      have v := mem_compl.mp (mem_filter.mp (mem_sigma.mp hb).2).1
      have DE := congrArg (fun z : Σ _ : Finset G, G => z.1.erase x) eq
      have same : D=E := by simpa only [erase_insert u,erase_insert v] using DE
      subst E
      rfl
    · rintro ⟨T,x⟩ hx
      obtain ⟨hT,hx⟩ := mem_sigma.mp hx
      obtain ⟨size,rank⟩ := mem_filter.mp hT
      have num := (mem_powersetCard.mp size).2
      have back := insert_erase hx
      refine ⟨⟨T.erase x,x⟩,mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,by rw [card_erase_of_mem hx,num];omega⟩,
        mem_filter.mpr ⟨mem_compl.mpr (notMem_erase x T),by rwa [back]⟩⟩,?_⟩
      simp only [back]
  have counts (T : Finset G) (hT : T∈L) : T.card=k+1 := (mem_powersetCard.mp (mem_filter.mp hT).1).2
  change (K.sigma _).card=(L.sigma _).card at bij
  rw [card_sigma,card_sigma,sum_congr rfl counts,sum_const,smul_eq_mul] at bij
  exact (Nat.mul_comm _ _).trans bij.symm

/-- Adding a marked point counts sets of size `k+1` by the dimension of their affine span. -/
theorem rank_count_step (k : ℕ) (pos : 0<k) (j : ℕ) :
    (k+1)*(rankLayer G (k+1) j).card =
      (rankLayer G k j).card*(2^j-k) +
        (if j=0 then 0 else (rankLayer G k (j-1)).card*(Fintype.card G-2^(j-1))) := by
  classical
  let K := (univ : Finset G).powersetCard k
  have opts (D : Finset G) (mem : D∈K) :
      (Dᶜ.filter fun x => affineRank (insert x D)=j).card =
      (if affineRank D=j then 2^j-k else 0) +
      (if affineRank D+1=j then Fintype.card G-2^(j-1) else 0) := by
    have sz := (mem_powersetCard.mp mem).2
    have live := card_pos.mp (show 0<D.card by omega)
    simpa only [sz] using insertion_options live j
  rw [marked_insertions, sum_congr rfl opts,sum_add_distrib,←sum_filter,sum_const,smul_eq_mul]
  apply congrArg₂ (·+·) rfl
  cases j with
  | zero => simp
  | succ j =>
    simp only [Nat.add_one_inj, Nat.succ_sub_one,Nat.succ_ne_zero,if_false]
    rw [←sum_filter,sum_const,smul_eq_mul]
    rfl

end Green51AffineTranslation
#print axioms Green51AffineTranslation.affineRank_insert
#print axioms Green51AffineTranslation.affine_span_card
#print axioms Green51AffineTranslation.rank_count_step
