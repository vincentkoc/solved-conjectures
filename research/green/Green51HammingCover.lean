import Green51DeletionRadius

/-! # Three translates meeting every missing Hamming direction -/

namespace Green51MissingMasks
open Finset
open scoped Classical symmDiff
private abbrev Point (t : ℕ) := Fin 2 ⊕ (Fin (t+1) ⊕ (Fin 3 ⊕ (Fin (t+4) ⊕ Fin 2)))

private def templates (t : ℕ) : Fin 3 → Finset (Point t) :=
  ![univ.disjSum (univ.disjSum (univ.disjSum (Finset.disjSum ∅ ∅))),
    univ.disjSum (Finset.disjSum ∅ (Finset.disjSum ∅ (univ.disjSum ∅))),
    univ.disjSum (univ.disjSum (Finset.disjSum ∅ (Finset.disjSum ∅ univ)))]

private theorem disjSum_flip {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a c : Finset α) (b d : Finset β) :
    a.disjSum b ∆ c.disjSum d = (a ∆ c).disjSum (b ∆ d) := by
  ext x
  cases x <;> simp [mem_symmDiff]

private theorem template_sizes (t : ℕ) (i : Fin 3) :
    (templates t i).card = 5+t ∨ (templates t i).card = 5+t+1 := by
  fin_cases i <;> simp [templates,card_disjSum] <;> omega

private theorem flip_empty {α : Type*} [DecidableEq α] (a : Finset α) : a ∆ ∅ = a := symmDiff_bot _
private theorem empty_flip {α : Type*} [DecidableEq α] (a : Finset α) : ∅ ∆ a = a := bot_symmDiff _

private theorem template_dist (t : ℕ) (i j : Fin 3) (ne : i ≠ j) :
    3 ≤ (templates t i ∆ templates t j).card ∧ (templates t i ∆ templates t j).card ≤ 2*(5+t) := by
  fin_cases i <;> fin_cases j <;> simp_all [templates,disjSum_flip,card_disjSum,flip_empty,empty_flip,-Finset.empty_disjSum,-Finset.disjSum_empty,-Finset.univ_disjSum_univ] <;> omega

private theorem template_cover (t : ℕ) (x : Point t) : ∃ i, x ∈ templates t i := by
  rcases x with x | x
  · exact ⟨0, by simp [templates]⟩
  rcases x with x | x
  · exact ⟨0, by simp [templates]⟩
  rcases x with x | x
  · exact ⟨0, by simp [templates]⟩
  rcases x with x | x
  · exact ⟨1, by simp [templates]⟩
  · exact ⟨2, by fin_cases x <;> simp [templates]⟩

theorem three_supports {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ}
    (hs : 5 ≤ s) (n : Fintype.card ι = 2*s+2) :
    ∃ T : Fin 3 → Finset ι, (∀ i, (T i).card = s ∨ (T i).card = s+1) ∧
      (∃ i, (T i).card = s) ∧ (∀ a, ∃ i, a ∈ T i) ∧
      ∀ i j, i ≠ j → 3 ≤ (T i ∆ T j).card ∧ (T i ∆ T j).card ≤ 2*s := by
  classical
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hs
  let e : Point t ≃ ι := Fintype.equivOfCardEq (by simp [Point,n,Fintype.card_sum]; omega)
  let T (i : Fin 3) := (templates t i).map e.toEmbedding
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro i; simpa [T] using template_sizes t i
  · exact ⟨2, by simp [T,templates,card_disjSum]; omega⟩
  · intro a
    obtain ⟨x,rfl⟩ := e.surjective a
    obtain ⟨i,hi⟩ := template_cover t x
    exact ⟨i,mem_map.mpr ⟨x,hi,rfl⟩⟩
  · intro i j ne
    have flip : T i ∆ T j = (templates t i ∆ templates t j).map e.toEmbedding := by
      ext a; obtain ⟨x,rfl⟩ := e.surjective a
      simp [T, mem_symmDiff]
    rw [flip,card_map]
    exact template_dist t i j ne

end Green51MissingMasks
#print axioms Green51MissingMasks.three_supports

namespace Green51MissingMasks
open Finset Green53ParityThreshold Green51Hyperplane Green51GirthFrame
open scoped Classical Pointwise symmDiff

theorem centres_of_supports {s r : ℕ} (T : Fin 3 → Finset (Fin (2*(s+1))))
    (sizes : ∀ i, (T i).card = s ∨ (T i).card = s+1)
    (last : ∃ i, (T i).card = s) (coverT : ∀ a, ∃ i, a ∈ T i)
    (dist : ∀ i j, i ≠ j → 3 ≤ (T i ∆ T j).card ∧ (T i ∆ T j).card ≤ 2*s) :
    let H := ball (s+1) r
    ∃ X : Finset (𝔽₂ (2*(s+1)+r)), X.card ≤ 3 ∧ X+X ⊆ H+H ∧
      (∀ z ∈ (H+H)ᶜ, ∃ x ∈ X, x+z ∈ H) ∧
      ∀ x ∈ X, ∀ z ∈ (H+H)ᶜ, ∀ y ∈ X, ∀ w ∈ (H+H)ᶜ, x+z = y+w → z=w := by
  classical
  let d := 2*(s+1)
  let G := 𝔽₂ (d+r)
  let H := ball (s+1) r
  let active (z : G) := (splitSupport d r z).1
  let W (z : G) := (active z)ᶜ
  let point (i : Fin 3) : G := (splitSupport d r).symm ((T i)ᶜ,0)
  have ai (i : Fin 3) : active (point i) = (T i)ᶜ := by simp [active,point]
  have add (z w : G) : active (z+w) = active z ∆ active w := support_add z w
  have ww (z w : G) : active (z+w) = W z ∆ W w := (add z w).trans (compl_symmDiff_compl (active z) (active w)).symm
  have two (i j : Fin 3) : active (point i+point j) = T i ∆ T j := by rw [add,ai,ai,compl_symmDiff_compl]
  have oddOne (i : Fin 3) (z : G) : active (point i+z) = T i ∆ W z := by
    rw [ww]; simp [W,ai]
  have few (z : G) (hz : z ∈ (H+H)ᶜ) : (W z).card ≤ 1 := by
    have out := mem_compl.mp hz
    have n := card_add_card_compl (active z)
    have too : ¬(active z).card + 2 ≤ d := fun h => out ((ball_sum_iff z).mpr h)
    simp only [Fintype.card_fin] at n
    change (active z)ᶜ.card ≤ 1
    omega
  let X := univ.image point
  have covered (z : G) (hz : z ∈ (H+H)ᶜ) : ∃ i, point i+z ∈ H := by
    have lim := few z hz
    by_cases zero : (W z).card = 0
    · obtain ⟨i,hi⟩ := last
      refine ⟨i, ball_mem.mpr ?_⟩
      change (active (point i+z)).card < s+1
      rw [oddOne, card_eq_zero.mp zero, show T i ∆ ∅ = T i from symmDiff_bot _, hi]; omega
    · obtain ⟨a,ha⟩ := card_eq_one.mp (show (W z).card = 1 by omega)
      obtain ⟨i,hi⟩ := coverT a
      refine ⟨i,ball_mem.mpr ?_⟩
      change (active (point i+z)).card < s+1
      rw [oddOne,ha,symmDiff_of_ge (singleton_subset_iff.mpr hi),sdiff_singleton_eq_erase,card_erase_of_mem hi]
      rcases sizes i with h | h <;> omega
  refine ⟨X,card_image_le.trans (by simp),?_,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := mem_image.mp hy
    apply (ball_sum_iff _).mpr
    change (active (point i+point j)).card + 2 ≤ d
    rw [two]; dsimp only [d]
    by_cases eq : i=j
    · simp [eq]
    · have := (dist i j eq).2; omega
  · intro z hz
    obtain ⟨i,hi⟩ := covered z hz
    exact ⟨point i,mem_image_of_mem _ (mem_univ _),hi⟩
  · intro x hx z hz y hy w hw eq
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := mem_image.mp hy
    by_cases ij : i=j
    · subst j; exact add_left_cancel eq
    have same : point i+point j = z+w := by
      calc
        _ = ((point i+z)+z)+point j := by rw [add_assoc (point i) z z, ZModModule.add_self, add_zero]
        _ = (point i+z)+(z+point j) := add_assoc _ _ _
        _ = z+w := by rw [eq, add_comm z (point j), add_add_add_comm, ZModModule.add_self, zero_add, add_comm w z]
    have sizesEq := congrArg (fun v => (active v).card) same
    change (active (point i+point j)).card = (active (z+w)).card at sizesEq
    rw [two,ww] at sizesEq
    have lo := (dist i j ij).1
    have hi := (card_symmDiff_parts (W z) (W w)).2
    have h1 := few z hz
    have h2 := few w hw
    omega

end Green51MissingMasks
#print axioms Green51MissingMasks.centres_of_supports
