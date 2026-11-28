import Green33StrictReduction
import Green33ReflectionRigidity

/-! Energy tests on the projected cardinalities of strict sum covers. -/

open Finset Green33StrictReduction Green33Multiplicity Green33TailEnergy

open scoped Pointwise

namespace Green33CyclicSeedFibers

variable {G H K : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    [AddCommGroup H] [DecidableEq H] [Fintype H]
    [AddCommGroup K] [DecidableEq K] [Fintype K]

/-- Number of selected points above a quotient residue. -/
def weight (A : Finset (H × K)) (i : H) := (A.filter fun a => a.1 = i).card

private abbrev diagCount (A : Finset G) (s : G) := Green33ReflectionRigidity.diagonalReps A s

/-- Ordered excess above two distinct witnesses and the diagonal witnesses. -/
private def extra (A : Finset G) (s : G) := reps A s - (2 + diagCount A s)

omit [Fintype G] in
private lemma strict_split (A : Finset G) (hA : StrictCover A) (s : G) :
    reps A s = 2 + diagCount A s + extra A s := by
  classical
  let P := (A ×ˢ A).filter fun t => t.1+t.2=s
  have hd : P.filter (fun t => t.1=t.2) = (A.filter fun a => a+a=s).diag := by
    ext t; rcases t with ⟨a,b⟩
    simp only [P,mem_filter,mem_product,mem_diag]; grind
  obtain ⟨a,ha,b,hb,hab,he⟩ := hA s
  have h₂ : 1 < (P.filter fun t => t.1≠t.2).card := by
    apply one_lt_card.mpr
    exact ⟨(a,b),by simp [P,ha,hb,hab,he],(b,a),by simp [P,ha,hb,hab.symm,add_comm b a,he],
      fun h => hab (congrArg Prod.fst h)⟩
  have ht := card_filter_add_card_filter_not (s := P) (fun t => t.1=t.2)
  rw [hd,diag_card] at ht
  change reps A s = 2+diagCount A s+(reps A s-(2+diagCount A s))
  change 1 < (P.filter fun t => ¬ t.1=t.2).card at h₂
  change diagCount A s + (P.filter fun t => ¬ t.1=t.2).card = reps A s at ht
  omega

omit [Fintype G] in
private lemma diag_one (A : Finset G) (hd : Function.Injective (fun a : G => a+a)) (s : G) :
    diagCount A s ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  exact hd ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)

private lemma quadratic_floor (A : Finset G) :
    ((A.card : ℝ)-2)*(A.card-3 : ℝ) ≤ ∑ s, ((reps A s : ℝ)-2)*(reps A s-3 : ℝ) := by
  let P (x : ℝ) := (x-2)*(x-3)
  have eqP (x : ℝ) : P x = (x-5/2)^2-1/4 := by dsimp [P]; ring
  have hn (n : ℕ) : 0 ≤ P n := by
    by_cases h : 3 ≤ n
    · have h' : (3:ℝ) ≤ n := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
    · interval_cases n <;> norm_num [P]
  have he : ∑ s, P (reps A s) = ∑ s, P (diffReps A s) := by
    simp only [eqP,sum_sub_distrib,centered_energy_eq]
  have hz : diffReps A 0 = A.card := by simp [diffReps,sub_eq_zero,← diag_eq_filter]
  change P A.card ≤ ∑ s, P (reps A s)
  rw [he,← hz]
  exact single_le_sum (fun s _ => hn (diffReps A s)) (mem_univ 0)

private lemma sum_extra (A : Finset G) (hA : StrictCover A) :
    A.card^2 = 2*Fintype.card G + A.card + ∑ s, extra A s := by
  have hr : ∑ s, reps A s = A.card^2 := by
    simpa [reps,sq] using sum_card_fiberwise_eq_card_filter (A ×ˢ A) univ
      (fun t => t.1+t.2)
  have hb : ∑ s, diagCount A s = A.card := by
    simpa [diagCount,Green33ReflectionRigidity.diagonalReps] using sum_card_fiberwise_eq_card_filter A univ (fun a => a+a)
  have ht : ∑ s, reps A s = 2*Fintype.card G + A.card + ∑ s, extra A s := by
    simp only [strict_split A hA,sum_add_distrib,hb,sum_const,card_univ,smul_eq_mul]
    omega
  exact hr.symm.trans ht

private lemma extra_energy (A : Finset G) (hA : StrictCover A)
    (hd : Function.Injective (fun a : G => a+a)) :
    2*Fintype.card G+6 ≤ (∑ s, extra A s ^ 2)+4*A.card := by
  have pt (s : G) : ((reps A s : ℝ)-2)*(reps A s-3 : ℝ) ≤
      (extra A s : ℝ)^2+extra A s := by
    have h := diag_one A hd s
    have eq := strict_split A hA s
    interval_cases hval : diagCount A s <;> rw [eq] <;> push_cast <;>
      nlinarith [Nat.cast_nonneg (α := ℝ) (extra A s)]
  have bound := (quadratic_floor A).trans (sum_le_sum (s := univ) fun s _ => pt s)
  rw [sum_add_distrib] at bound
  change 2*Fintype.card G+6 ≤ (∑ s, extra A s ^ 2)+4*A.card
  have hr' : (A.card : ℝ)^2 = 2*Fintype.card G + A.card + ∑ s, (extra A s : ℝ) := by
    exact_mod_cast sum_extra A hA
  have b : 2*(Fintype.card G : ℝ)+6 ≤ (∑ s, (extra A s : ℝ)^2)+4*A.card := by nlinarith
  exact_mod_cast b

private lemma sum_sq_le_sq_sum {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    ∑ i, f i ^ 2 ≤ (∑ i, f i)^2 := by
  rw [sq,sum_mul]
  apply sum_le_sum
  intro i _
  simpa only [sq] using Nat.mul_le_mul_left (f i)
    (single_le_sum (s := (univ : Finset ι)) (f := f) (fun _ _ => Nat.zero_le _) (mem_univ i))

/-- Counting unordered pairs with the diagonal omitted loses at least
(k-3)/2 additional slots in a group with injective doubling. -/
theorem strict_order (A : Finset G) (hA : StrictCover A)
    (hd : Function.Injective (fun x : G => x+x)) :
    2*Fintype.card G + 2*A.card ≤ A.card^2+3 := by
  let E := ∑ s, extra A s
  have hm : A.card^2 = 2*Fintype.card G+A.card+E := sum_extra A hA
  have h : 2*Fintype.card G+6 ≤ E^2+4*A.card :=
    (extra_energy A hA hd).trans (Nat.add_le_add_right (sum_sq_le_sq_sum _) _)
  suffices hk : A.card ≤ E+3 by omega
  by_contra! hn
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le (show E+4 ≤ A.card by omega)
  rw [hv] at hm h
  nlinarith only [hm,h,Nat.zero_le (E*v),Nat.zero_le (v^2),Nat.zero_le v,Nat.zero_le E]

/-- The additive constant is attained by a five-point strict cover modulo nine. -/
theorem sharp_nine : ∃ A : Finset (ZMod 9), A.card=5 ∧ StrictCover A := by
  refine ⟨{0,1,2,3,6},by decide,?_⟩
  intro x
  fin_cases x
  · exact ⟨3,by decide,6,by decide,by decide,rfl⟩
  · exact ⟨0,by decide,1,by decide,by decide,rfl⟩
  · exact ⟨0,by decide,2,by decide,by decide,rfl⟩
  · exact ⟨0,by decide,3,by decide,by decide,rfl⟩
  · exact ⟨1,by decide,3,by decide,by decide,rfl⟩
  · exact ⟨2,by decide,3,by decide,by decide,rfl⟩
  · exact ⟨0,by decide,6,by decide,by decide,rfl⟩
  · exact ⟨1,by decide,6,by decide,by decide,rfl⟩
  · exact ⟨2,by decide,6,by decide,by decide,rfl⟩

private lemma cyclic_diag_two (n : ℕ+) (A : Finset (ZMod n)) (s : ZMod n) :
    diagCount A s ≤ 2 := by
  let B := A.filter fun a => a+a=s
  have hsub : B.image ZMod.val ⊆ {s.val/2,(s.val+n)/2} := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
    have he : a+a=s := (mem_filter.mp ha).2
    simp only [mem_insert,mem_singleton]
    by_cases small : a.val+a.val < n
    · have h := ZMod.val_add_of_lt small
      rw [he] at h
      omega
    · have h := ZMod.val_add_val_of_le (Nat.le_of_not_gt small)
      rw [he] at h
      omega
  have hcard := (card_le_card hsub).trans card_le_two
  simpa [B,diagCount,Green33ReflectionRigidity.diagonalReps,
    card_image_of_injective _ (ZMod.val_injective n)] using hcard

/-- Every positive cyclic order satisfies the strict bound, including even
orders where a sum may have two diagonal witnesses. -/
theorem cyclic_strict_order (n : ℕ+) (A : Finset (ZMod n)) (hA : StrictCover A) :
    2*n.val+2*A.card ≤ A.card^2+4 := by
  let E := ∑ s, extra A s
  have hm := sum_extra A hA
  rw [ZMod.card] at hm
  change A.card^2 = 2*n.val+A.card+E at hm
  have pt (x : ZMod n) : ((reps A x : ℝ)-2)*(reps A x-3 : ℝ) ≤
      (extra A x : ℝ)^2+3*extra A x+diagCount A x := by
    have h := cyclic_diag_two n A x
    have eq := strict_split A hA x
    interval_cases v : diagCount A x <;> rw [eq] <;> push_cast <;>
      nlinarith [Nat.cast_nonneg (α := ℝ) (extra A x)]
  have h := (quadratic_floor A).trans (sum_le_sum (s := univ) fun x _ => pt x)
  simp only [sum_add_distrib,← mul_sum] at h
  have hs : (∑ x, (extra A x : ℝ)^2) ≤ (E : ℝ)^2 := by exact_mod_cast sum_sq_le_sq_sum _
  have hb : ∑ x, diagCount A x = A.card := by
    simpa [diagCount,Green33ReflectionRigidity.diagonalReps] using
      sum_card_fiberwise_eq_card_filter A univ (fun a => a+a)
  have hd : ∑ x, (diagCount A x : ℝ) = A.card := by exact_mod_cast hb
  have he : ∑ x, (extra A x : ℝ) = E := by dsimp [E]; norm_cast
  have hk : A.card^2+6 ≤ E^2+3*E+6*A.card := by
    have : (A.card : ℝ)^2+6 ≤ (E : ℝ)^2+3*E+6*A.card := by nlinarith
    exact_mod_cast this
  suffices A.card ≤ E+4 by omega
  by_contra! hn
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le (show E+5 ≤ A.card by omega)
  rw [hv] at hk
  nlinarith only [hk,Nat.zero_le (E*v),Nat.zero_le (v^2),Nat.zero_le v,Nat.zero_le E]

/-- Four points give equality at even order six. -/
theorem sharp_six : ∃ A : Finset (ZMod 6), A.card=4 ∧ StrictCover A := by
  refine ⟨{0,1,2,4},by decide,?_⟩
  intro x
  fin_cases x
  · exact ⟨2,by decide,4,by decide,by decide,rfl⟩
  · exact ⟨0,by decide,1,by decide,by decide,rfl⟩
  · exact ⟨0,by decide,2,by decide,by decide,rfl⟩
  · exact ⟨1,by decide,2,by decide,by decide,rfl⟩
  · exact ⟨0,by decide,4,by decide,by decide,rfl⟩
  · exact ⟨1,by decide,4,by decide,by decide,rfl⟩

/-- Excess of the projected ordered pair count over the required two witnesses
per color and the diagonal pairs. Everything here is computed from the weights. -/
def rowExcess (q : ℕ) (a : H → ℕ) (r : H) : ℕ :=
  (∑ i, a i * a (r-i)) - (2*q + ∑ i ∈ univ.filter (fun i : H => i+i=r), a i)

private lemma project_reps (A : Finset (H × K)) (r : H) :
    (∑ z : K, reps A (r,z)) = ∑ i, weight A i * weight A (r-i) := by
  classical
  let Q := (A ×ˢ A).filter fun t => t.1.1+t.2.1=r
  have hpair (i : H) : Q.filter (fun t => t.1.1=i) =
      (A.filter fun a => a.1=i) ×ˢ (A.filter fun b => b.1=r-i) := by
    ext t; rcases t with ⟨a,b⟩
    simp only [Q,mem_filter,mem_product]; constructor
    · rintro ⟨⟨⟨ha,hb⟩,hr⟩,hi⟩
      exact ⟨⟨ha,hi⟩,hb,by rw [← hi,← hr]; abel⟩
    · rintro ⟨⟨ha,hi⟩,hb,hb'⟩
      exact ⟨⟨⟨ha,hb⟩,by rw [hi,hb']; abel⟩,hi⟩
  have hsum := sum_card_fiberwise_eq_card_filter Q (univ : Finset H) (fun t => t.1.1)
  have hc (z : K) : Q.filter (fun t => t.1.2+t.2.2=z) =
      (A ×ˢ A).filter (fun t => t.1+t.2=(r,z)) := by
    ext t; simp only [Q,mem_filter,Prod.ext_iff,Prod.fst_add,Prod.snd_add]; tauto
  have hz := sum_card_fiberwise_eq_card_filter Q (univ : Finset K) (fun t => t.1.2+t.2.2)
  have hz' : (∑ z : K, reps A (r,z)) = Q.card := by simpa [hc,reps] using hz
  exact hz'.trans (by simpa [hpair,weight] using hsum.symm)

private lemma project_diag (A : Finset (H × K)) (r : H) :
    (∑ z : K, diagCount A (r,z)) = ∑ i ∈ univ.filter (fun i : H => i+i=r), weight A i := by
  classical
  let B := A.filter fun a => a.1+a.1=r
  have hh (z : K) : B.filter (fun a => a.2+a.2=z) = A.filter (fun a => a+a=(r,z)) := by
    ext a; simp only [B,mem_filter,Prod.ext_iff,Prod.fst_add,Prod.snd_add]; tauto
  have hz := sum_card_fiberwise_eq_card_filter B (univ : Finset K) (fun a => a.2+a.2)
  have hi := sum_card_fiberwise_eq_card_filter A (univ.filter fun i : H => i+i=r) Prod.fst
  have hz' : (∑ z : K, diagCount A (r,z)) = B.card := by simpa [hh,diagCount,Green33ReflectionRigidity.diagonalReps] using hz
  exact hz'.trans (by simpa [weight,B] using hi.symm)

theorem quotient_capacity (A : Finset (H × K)) (hA : StrictCover A) (r : H) :
    2*Fintype.card K + (∑ i ∈ univ.filter (fun i : H => i+i=r), weight A i) ≤
    ∑ i, weight A i * weight A (r-i) := by
  rw [← project_reps,← project_diag]
  simp only [strict_split A hA,sum_add_distrib,sum_const,card_univ,smul_eq_mul]
  omega

private lemma project_extra (A : Finset (H × K)) (hA : StrictCover A) (r : H) :
    ∑ z : K, extra A (r,z) = rowExcess (Fintype.card K) (weight A) r := by
  rw [rowExcess,← project_reps,← project_diag]
  simp only [strict_split A hA,sum_add_distrib,sum_const,card_univ,smul_eq_mul]
  omega

/-- The sum of squared row excesses is at least twice the whole group order
minus four times the seed size plus six, when doubling is injective. -/
theorem projected_energy (A : Finset (H × K)) (hA : StrictCover A)
    (hd : Function.Injective (fun x : H × K => x+x)) :
    2*(Fintype.card H*Fintype.card K)+6 ≤
      (∑ r, rowExcess (Fintype.card K) (weight A) r ^ 2)+4*A.card := by
  have he := extra_energy A hA hd
  rw [Fintype.card_prod,Fintype.sum_prod_type] at he
  apply he.trans (Nat.add_le_add_right _ _)
  apply sum_le_sum
  intro r _
  rw [← project_extra A hA r]
  exact sum_sq_le_sq_sum _

/-- Twice the ordinary unordered-pair excess in one projected row. -/
def ordinaryRowExcess (q : ℕ) (a : H → ℕ) (r : H) : ℕ :=
  (∑ i, a i * a (r-i)) + (∑ i ∈ univ.filter (fun i : H => i+i=r), a i) - 2*q

/-- The corresponding row obstruction under the ordinary sumset hypothesis
used in Green 33. The diagonal pairs now contribute to coverage. -/
theorem projected_ordinary (A : Finset (H × K)) (hA : A + A = univ)
    (hd : Function.Injective (fun x : H × K => x+x)) :
    2*A.card^2+6 ≤ (∑ r, ordinaryRowExcess (Fintype.card K) (weight A) r ^ 2) +
      2*(Fintype.card H*Fintype.card K)+6*A.card := by
  let W (x : H × K) := reps A x + diagCount A x - 2
  have split (x) : W x + 2 = reps A x + diagCount A x :=
    Nat.sub_add_cancel (Green33ReflectionRigidity.cover_counts_le A hA x).2
  have row (r : H) : (∑ z : K, W (r,z)) = ordinaryRowExcess (Fintype.card K) (weight A) r := by
    have he := sum_congr (s₁ := (univ : Finset K)) rfl (fun z _ => split (r,z))
    simp only [sum_add_distrib,sum_const,card_univ,smul_eq_mul,project_reps,project_diag] at he
    unfold ordinaryRowExcess
    omega
  have hr : ∑ x, reps A x = A.card^2 := by
    simpa [reps,sq] using sum_card_fiberwise_eq_card_filter (A ×ˢ A) univ
      (fun t => t.1+t.2)
  have hb : ∑ x, diagCount A x = A.card := by
    simpa [diagCount,Green33ReflectionRigidity.diagonalReps] using
      sum_card_fiberwise_eq_card_filter A univ (fun a => a+a)
  have ht := sum_congr (s₁ := univ) rfl (fun x _ => split x)
  simp only [sum_add_distrib,sum_const,card_univ,smul_eq_mul,hr,hb,Fintype.card_prod] at ht
  have pt (x : H × K) : ((reps A x : ℝ)-2)*(reps A x-3 : ℝ) ≤
      (W x : ℝ)^2-W x+2*diagCount A x := by
    have h := diag_one A hd x
    have eq : (W x : ℝ)+2 = reps A x+diagCount A x := by exact_mod_cast split x
    interval_cases v : diagCount A x <;> push_cast at eq ⊢ <;>
      nlinarith [Nat.cast_nonneg (α := ℝ) (W x)]
  have bound := (quadratic_floor A).trans (sum_le_sum (s := univ) fun x _ => pt x)
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum] at bound
  have sumd : (∑ x, (diagCount A x : ℝ)) = A.card := by exact_mod_cast hb
  have sumw : (∑ x, (W x : ℝ)) + (Fintype.card H : ℝ)*Fintype.card K*2 =
      (A.card : ℝ)^2+A.card := by exact_mod_cast ht
  have en : 2*A.card^2+6 ≤ (∑ x, W x^2)+2*(Fintype.card H*Fintype.card K)+6*A.card := by
    have he : 2*(A.card : ℝ)^2+6 ≤ (∑ x, (W x : ℝ)^2)+
        2*(Fintype.card H*Fintype.card K : ℝ)+6*A.card := by nlinarith
    exact_mod_cast he
  rw [Fintype.sum_prod_type] at en
  exact en.trans (by gcongr with i; rw [← row]; exact sum_sq_le_sq_sum _)

omit [AddCommGroup H] [AddCommGroup K] [DecidableEq K] [Fintype K] in
private lemma sum_weight (A : Finset (H × K)) : ∑ i, weight A i = A.card := by
  simpa [weight] using sum_card_fiberwise_eq_card_filter A (univ : Finset H) Prod.fst

/-- If each quotient fiber contains exactly h labels, the same excess occurs
in every row. Its square is at least 2q-4h+1 for a nonempty quotient. -/
theorem uniform_fibers (A : Finset (H × K)) (hA : StrictCover A)
    (hd : Function.Injective (fun x : H × K => x+x)) (h : ℕ)
    (hw : ∀ i, weight A i = h) :
    2*Fintype.card K+1 ≤
      (Fintype.card H*h^2-(2*Fintype.card K+h))^2+4*h := by
  classical
  have hh : Function.Injective (fun i : H => i+i) := by
    intro i j hij
    have he : (i,(0:K))+(i,0) = (j,0)+(j,0) := Prod.ext hij rfl
    exact congrArg Prod.fst (hd he)
  have hf (r : H) : (univ.filter fun i : H => i+i=r).card = 1 := by
    obtain ⟨i,hi⟩ := Finite.surjective_of_injective hh r
    have eq : (univ.filter fun j : H => j+j=r) = {i} := by
      ext j; simp only [mem_filter,mem_univ,true_and,mem_singleton,← hi]
      exact hh.eq_iff
    simp [eq]
  have row (r : H) : rowExcess (Fintype.card K) (weight A) r =
      Fintype.card H*h^2-(2*Fintype.card K+h) := by simp [rowExcess,hw,hf,sq]
  have ha := sum_weight A
  simp [hw] at ha
  have en := projected_energy A hA hd
  simp only [row,sum_const,card_univ,smul_eq_mul,← ha] at en
  by_contra! contra
  have t := Nat.mul_le_mul_left (Fintype.card H) (show
    (Fintype.card H*h^2-(2*Fintype.card K+h))^2+4*h ≤ 2*Fintype.card K by omega)
  nlinarith only [t,en]

private def profile117 (c i : ZMod 9) : ℕ := if i=c then 1 else 2

/-- A 17-label strict seed modulo 117 cannot split into one singleton and
eight doubletons modulo 9. The two factors give the canonical CRT model. -/
theorem no_balanced_117 (A : Finset (ZMod 9 × ZMod 13)) (c : ZMod 9)
    (hw : ∀ i, weight A i = if i=c then 1 else 2) : ¬ StrictCover A := by
  intro hA
  have hd : Function.Injective (fun x : ZMod 9 × ZMod 13 => x+x) := by
    intro a b e
    apply Prod.ext
    · have inj : Function.Injective (fun x : ZMod 9 => x+x) := by decide
      exact inj (congrArg Prod.fst e)
    · have inj : Function.Injective (fun x : ZMod 13 => x+x) := by decide
      exact inj (congrArg Prod.snd e)
  have hprof : weight A = profile117 c := funext hw
  have hs : ∀ j, (∑ i, profile117 j i)=17 := by decide +kernel
  have ht : ∀ j, (∑ r, rowExcess 13 (profile117 j) r ^ 2)=164 := by decide +kernel
  have hk := sum_weight A
  rw [hprof,hs] at hk
  have he := projected_energy A hA hd
  rw [ZMod.card,ZMod.card,hprof,ht,← hk] at he
  omega

/-- Written directly in the cyclic group, with fibers given by ordinary
natural representatives modulo nine. -/
theorem cyclic_117 (A : Finset (ZMod 117)) (c : ZMod 9)
    (hw : ∀ i : ZMod 9, (A.filter fun x => (x.val : ZMod 9)=i).card =
      if i=c then 1 else 2) : ¬ StrictCover A := by
  let f : ZMod 117 ≃+ ZMod 9 × ZMod 13 :=
    (ZMod.chineseRemainder (m := 9) (n := 13) (by decide)).toAddEquiv
  have hf (x : ZMod 117) : (f x).1 = (x.val : ZMod 9) := rfl
  have hw' (i) : weight (A.map f.toEmbedding) i = if i=c then 1 else 2 := by
    simpa [weight,filter_map,hf,Function.comp_def] using hw i
  intro h
  apply no_balanced_117 _ c hw'
  intro x
  obtain ⟨a,ha,b,hb,hab,he⟩ := h (f.symm x)
  exact ⟨f a,mem_map.mpr ⟨a,ha,rfl⟩,f b,mem_map.mpr ⟨b,hb,rfl⟩,
    fun e => hab (f.injective e),by rw [← map_add,he,f.apply_symm_apply]⟩

#print axioms cyclic_strict_order
#print axioms sharp_six
#print axioms cyclic_117
#print axioms projected_ordinary
#print axioms strict_order
#print axioms sharp_nine
#print axioms quotient_capacity
#print axioms projected_energy
#print axioms uniform_fibers
#print axioms no_balanced_117

end Green33CyclicSeedFibers
