import Green33SidonProfile
import Green33ReflectionRigidity

/-! Translation overlaps and excess unordered sum representations. -/

open Finset Filter Green33SidonProfile Green33TailEnergy Green33ReflectionRigidity
open scoped Pointwise Topology

namespace Green33TranslateOverlap

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Labels whose translate by t is again a label. -/
def starts (A : Finset G) (t : G) := A.filter fun x => x + t ∈ A

/-- Unordered pairs beyond one witness for each occupied sum. -/
def sumExcess (A : Finset G) := (A.card + 1).choose 2 - (A + A).card

private def pairSum : Sym2 G → G := Sym2.lift ⟨(· + ·), add_comm⟩

private lemma image_sum (A : Finset G) : A.sym2.image pairSum = A + A := by
  ext s
  constructor
  · intro hs
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := mem_image.mp hs
    obtain ⟨hx,hy⟩ := mk_mem_sym2_iff.mp hxy
    exact add_mem_add hx hy
  · intro hs
    obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hs
    exact mem_image.mpr ⟨Sym2.mk x y, mk_mem_sym2_iff.mpr ⟨hx,hy⟩, rfl⟩

private lemma ambiguous_card {P H : Type*} [DecidableEq H] (S : Finset P) (f : P → H) :
    (S.filter (fun x => 1 < (S.filter (fun y => f y = f x)).card)).card ≤
      2 * (S.card - (S.image f).card) := by
  classical
  let n (s : H) := (S.filter (fun x => f x = s)).card
  let B := S.filter (fun x => 1 < n (f x))
  let T := S.image f
  have point (s : H) (hs : s ∈ T) : (B.filter (fun x => f x = s)).card + 2 ≤ 2 * n s := by
    have hp : 0 < n s := card_pos.mpr (fiber_nonempty_iff_mem_image.mpr hs)
    by_cases hn : 1 < n s
    · have hle : (B.filter (fun x => f x = s)).card ≤ n s :=
        card_le_card (filter_subset_filter _ (filter_subset _ _))
      omega
    · have he : B.filter (fun x => f x = s) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨hb,hx'⟩ := mem_filter.mp hx
        exact hn (hx' ▸ (mem_filter.mp hb).2)
      rw [he,card_empty]
      omega
  have h := sum_le_sum point
  have hB : B.card = ∑ s ∈ T, (B.filter (fun x => f x = s)).card :=
    card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem _ (mem_filter.mp hx).1)
  have hS : S.card = ∑ s ∈ T, n s := card_eq_sum_card_image f S
  rw [sum_add_distrib, ← hB, sum_const, nsmul_eq_mul, ← mul_sum, ← hS] at h
  change B.card + T.card * 2 ≤ 2 * S.card at h
  change B.card ≤ 2 * (S.card - T.card)
  omega

/-- Every repeated nonzero difference forces collisions of unordered sums.
The excess counts each diagonal pair once. -/
theorem translate_bound (A : Finset G) {t : G} (ht : t ≠ 0) :
    (starts A t).card * ((starts A t).card - 1) ≤ 4 * sumExcess A := by
  classical
  let B := starts A t
  let S := A.sym2
  let bad := S.filter (fun u => 1 < (S.filter (fun v => pairSum v = pairSum u)).card)
  let f (p : G × G) := Sym2.mk (p.1 + t) p.2
  have maps (p : G × G) (hp : p ∈ B.offDiag) : f p ∈ bad := by
    obtain ⟨x,y⟩ := p
    obtain ⟨hx,hy,hne⟩ := mem_offDiag.mp hp
    obtain ⟨hx,hxt⟩ := mem_filter.mp hx
    obtain ⟨hy,hyt⟩ := mem_filter.mp hy
    let u := Sym2.mk (x+t) y
    let v := Sym2.mk x (y+t)
    have hu : u ∈ S := mk_mem_sym2_iff.mpr ⟨hxt,hy⟩
    have hv : v ∈ S := mk_mem_sym2_iff.mpr ⟨hx,hyt⟩
    refine mem_filter.mpr ⟨hu,one_lt_card.mpr ?_⟩
    refine ⟨u,mem_filter.mpr ⟨hu,rfl⟩,v,mem_filter.mpr ⟨hv,?_⟩,?_⟩
    · change x+(y+t)=(x+t)+y
      abel
    · intro h
      rcases Sym2.eq_iff.mp h with h | h
      · exact ht (by simpa using h.1)
      · exact hne (add_right_cancel h.1)
  have hcap (u : Sym2 G) (_ : u ∈ bad) : (B.offDiag.filter (fun v => f v = u)).card ≤ 2 := by
    obtain ⟨a,b⟩ := u
    apply (card_le_card (t := {(a-t,b),(b-t,a)}) ?_).trans card_le_two
    rintro ⟨x,y⟩ h
    rcases Sym2.eq_iff.mp (mem_filter.mp h).2 with ⟨he,rfl⟩ | ⟨he,rfl⟩
    · exact mem_insert.mpr (Or.inl (Prod.ext (eq_sub_of_add_eq he) rfl))
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (Prod.ext (eq_sub_of_add_eq he) rfl)))
  have h := card_le_mul_card_image_of_maps_to maps 2 hcap
  have hbad := ambiguous_card S pairSum
  change bad.card ≤ 2 * (S.card - (A.sym2.image pairSum).card) at hbad
  rw [image_sum] at hbad
  change bad.card ≤ 2 * (A.sym2.card - (A+A).card) at hbad
  rw [card_sym2] at hbad
  rw [offDiag_card, ← Nat.mul_sub_one] at h
  change B.card * (B.card - 1) ≤ 4 * ((A.card+1).choose 2 - (A+A).card)
  omega

private lemma starts_card (A : Finset G) (t : G) : (starts A t).card = diffReps A t := by
  apply card_bij (fun x _ => (x+t,x))
  · intro x hx
    obtain ⟨hx,hxt⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hxt,hx⟩,by simp⟩
  · intro x _ y _ h
    exact congrArg Prod.snd h
  · rintro ⟨x,y⟩ hp
    obtain ⟨hxy,he⟩ := mem_filter.mp hp
    have h : y+t=x := by rw [← he]; abel
    exact ⟨y,mem_filter.mpr ⟨(mem_product.mp hxy).2, h ▸ (mem_product.mp hxy).1⟩,Prod.ext h rfl⟩

/-- Largest multiplicity of an ordered nonzero difference, with value zero in
the trivial group. -/
def maxDifference [Fintype G] (A : Finset G) :=
  (univ.erase (0 : G)).sup fun t => diffReps A t

private lemma max_sq [Fintype G] (A : Finset G) :
    (maxDifference A)^2 ≤ 4 * sumExcess A + A.card := by
  by_cases h : (univ.erase (0 : G)).Nonempty
  · obtain ⟨t,ht,hm⟩ := exists_mem_eq_sup _ h (fun t => diffReps A t)
    have hb := translate_bound A (mem_erase.mp ht).1
    have hle : (starts A t).card ≤ A.card := card_filter_le ..
    unfold maxDifference
    rw [hm, ← starts_card]
    rw [Nat.mul_sub_one] at hb
    rw [sq]
    omega
  · simp [maxDifference,not_nonempty_iff_eq_empty.mp h]

/-- Near-optimal size and coverage of a 1−o(1) fraction force every nonzero
difference multiplicity to be o(√M), uniformly in the shift. -/
theorem vanishing_max_difference {ι : Type*} {l : Filter ι} (M : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (M i)))
    (hM : Tendsto (fun i => (M i).val) l atTop)
    (hk : Tendsto (fun i => ((A i).card : ℝ)/Real.sqrt (M i)) l (𝓝 (Real.sqrt 2)))
    (hs : Tendsto (fun i => (((A i)+(A i)).card : ℝ)/(M i : ℝ)) l (𝓝 1)) :
    Tendsto (fun i => (maxDifference (A i) : ℝ)/Real.sqrt (M i)) l (𝓝 0) := by
  obtain ⟨hk₁,hk₂⟩ := card_limits M (fun i => (A i).card) hM hk
  have hE : Tendsto (fun i => (sumExcess (A i) : ℝ)/(M i : ℝ)) l (𝓝 0) := by
    have ht := (((hk₂.add hk₁).div_const 2).sub hs)
    norm_num at ht
    apply ht.congr
    intro i
    have hle : ((A i)+(A i)).card ≤ ((A i).card+1).choose 2 := by
      rw [← image_sum,← card_sym2]
      exact card_image_le
    rw [sumExcess,Nat.cast_sub hle,Nat.cast_choose_two,Nat.cast_add_one]
    ring
  have hsq : Tendsto (fun i => (maxDifference (A i) : ℝ)^2/(M i : ℝ)) l (𝓝 0) := by
    have hu := ((tendsto_const_nhds (x := (4:ℝ))).mul hE).add hk₁
    norm_num at hu
    apply squeeze_zero (fun i => by positivity) _ hu
    intro i
    have h : (maxDifference (A i) : ℝ)^2 ≤ 4 * (sumExcess (A i) : ℝ) + (A i).card :=
      by exact_mod_cast max_sq (A i)
    have hm : 0 < (M i : ℝ) := by exact_mod_cast (M i).pos
    calc
      _ ≤ (4 * (sumExcess (A i) : ℝ) + (A i).card)/(M i : ℝ) := (div_le_div_iff_of_pos_right hm).mpr h
      _ = _ := by ring
  simpa only [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _),Real.sqrt_zero]
    using hsq.sqrt

/-- The full cyclic coverage hypothesis of Green 33 specializes the preceding
density-one sumset obstruction. -/
theorem green_max_difference {ι : Type*} {l : Filter ι} (M : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (M i)))
    (hM : Tendsto (fun i => (M i).val) l atTop)
    (hk : Tendsto (fun i => ((A i).card : ℝ)/Real.sqrt (M i)) l (𝓝 (Real.sqrt 2)))
    (hA : ∀ i, A i + A i = univ) :
    Tendsto (fun i => (maxDifference (A i) : ℝ)/Real.sqrt (M i)) l (𝓝 0) := by
  apply vanishing_max_difference M A hM hk
  refine tendsto_const_nhds.congr (fun i => ?_)
  rw [hA,card_univ,ZMod.card,div_self (by exact_mod_cast (M i).ne_zero)]

private def liftSet (M : ℕ+) (S : Finset (ZMod M)) :=
  univ.filter fun x => projection M x ∈ S

private lemma lift_card (M : ℕ+) (S : Finset (ZMod M)) : (liftSet M S).card = 2 * S.card := by
  let f := projection M
  have surj : Function.Surjective f := ZMod.castHom_surjective (dvd_mul_left M.val 2)
  let n (y : ZMod M) := (univ.filter fun x => f x = y).card
  have heq (y : ZMod M) : n y = n 0 := by
    obtain ⟨a,ha⟩ := surj y
    apply card_equiv (Equiv.subRight a)
    intro x
    simp only [mem_filter,mem_univ,true_and,Equiv.subRight_apply,map_sub,ha,sub_eq_zero]
  have h := sum_card_fiberwise_eq_card_filter univ (univ : Finset (ZMod M)) f
  change (∑ y, n y) = _ at h
  simp only [heq,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mem_univ,filter_true,ZMod.card] at h
  have hn : n 0 = 2 := by nlinarith [M.pos]
  have hs := sum_card_fiberwise_eq_card_filter univ S f
  change (∑ y ∈ S, n y) = (liftSet M S).card at hs
  rw [← hs]
  simp only [heq,hn,sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm]

private lemma lift_sum (M : ℕ+) (S : Finset (ZMod M)) :
    liftSet M S + liftSet M S = liftSet M (S+S) := by
  let f := projection M
  have surj : Function.Surjective f := ZMod.castHom_surjective (dvd_mul_left M.val 2)
  ext z
  constructor
  · intro hz
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hz
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    rw [map_add]
    exact add_mem_add (mem_filter.mp ha).2 (mem_filter.mp hb).2
  · intro hz
    obtain ⟨a,ha,b,hb,he⟩ := Finset.mem_add.mp (mem_filter.mp hz).2
    obtain ⟨u,hu⟩ := surj a
    have huv : f (z-u) = b := by rw [map_sub,hu,← he]; abel
    exact Finset.mem_add.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,hu ▸ ha⟩,
      z-u,mem_filter.mpr ⟨mem_univ _,huv ▸ hb⟩,by abel⟩

/-- Taking both lifts of every Sidon label gives an overlap of size 2k and
exactly k² excess pairs. Thus the leading factor four in translate_bound
is approached along cyclic examples. -/
theorem sidon_double_lift (M : ℕ+) (S : Finset (ZMod M)) (hS : IsSidon (S : Set (ZMod M))) :
    ∃ (A : Finset (ZMod (2*M.val))) (t : ZMod (2*M.val)), t ≠ 0 ∧
      A.card = 2*S.card ∧ (starts A t).card = 2*S.card ∧ sumExcess A = S.card^2 := by
  let A := liftSet M S
  let t : ZMod (2*M.val) := M.val
  have ht : t ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    change ((M.val : ZMod (2*M.val))).val = (0 : ZMod (2*M.val)).val at hv
    rw [ZMod.val_natCast_of_lt (by have := M.pos; omega),ZMod.val_zero] at hv
    exact M.ne_zero hv
  have hz : projection M t = 0 := by
    change (ZMod.castHom (dvd_mul_left M.val 2) (ZMod M)) (M.val : ZMod (2*M.val)) = 0
    rw [map_natCast,ZMod.natCast_self]
  have hper : starts A t = A := by
    apply filter_eq_self.mpr
    intro x hx
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    simpa only [map_add,hz,add_zero] using (mem_filter.mp hx).2
  have hcard : (S+S).card = (S.card+1).choose 2 := by
    rw [← image_sum,← card_sym2]
    apply card_image_of_injOn
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := mk_mem_sym2_iff.mp hab
    obtain ⟨hc,hd⟩ := mk_mem_sym2_iff.mp hcd
    exact Sym2.eq_iff.mpr (hS a ha c hc b hb d hd he)
  refine ⟨A,t,ht,lift_card M S,(congrArg Finset.card hper).trans (lift_card M S),?_⟩
  change (sumExcess (liftSet M S)) = _
  rw [sumExcess,lift_card,lift_sum,lift_card,hcard]
  have hn : (2*S.card+1).choose 2 = 2*(S.card+1).choose 2 + S.card^2 := by
    apply Nat.cast_injective (R := ℚ)
    push_cast [Nat.cast_choose_two]
    ring
  omega

/-- No real coefficient below four works uniformly, even for cyclic groups. -/
theorem optimal_coefficient {c : ℝ} (hc : c < 4) (L : ℕ) :
    ∃ (N : ℕ+) (A : Finset (ZMod N)) (t : ZMod N), L ≤ N.val ∧ t ≠ 0 ∧
      c * (sumExcess A : ℝ) < ((starts A t).card : ℝ) * ((starts A t).card - 1 : ℕ) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (2/(4-c))
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (L+n+3)
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨S,hs,hSidon⟩ := cyclic_sidon_seed p
  let M : ℕ+ := ⟨(p-1)*p,Nat.mul_pos (by omega) hprime.pos⟩
  obtain ⟨A,t,ht,_,hb,hE⟩ := sidon_double_lift M S hSidon
  have hL : L ≤ 2*M.val := by
    change L ≤ 2*((p-1)*p)
    have hh := Nat.mul_le_mul_right p (show 1≤p-1 by omega)
    omega
  have strict : c * (sumExcess A : ℝ) < ((starts A t).card : ℝ) * ((starts A t).card - 1 : ℕ) := by
    rw [hb,hE]
    change c * ((S.card ^ 2 : ℕ) : ℝ) < ((2*S.card : ℕ) : ℝ) * ((2*S.card - 1 : ℕ) : ℝ)
    have hk : 0 < S.card := by omega
    have hk' : 0 < (S.card : ℝ) := by exact_mod_cast hk
    have hg : 2 / (4-c) < (S.card : ℝ) := hn.trans_le (by exact_mod_cast (show n≤S.card by omega))
    have hh := (div_lt_iff₀ (sub_pos.mpr hc)).mp hg
    rw [Nat.cast_sub (by omega : 1≤2*S.card)]
    push_cast
    nlinarith [mul_lt_mul_of_pos_right hh hk']
  exact ⟨⟨2*M.val,by positivity⟩,A,t,hL,ht,strict⟩

private lemma partners_inter [Fintype G] (A : Finset G) {s t : G} (hne : s ≠ t) :
    ((reflectedPart A s) ∩ (reflectedPart A t)).card ≤ maxDifference A := by
  have h : ((reflectedPart A s) ∩ (reflectedPart A t)).card ≤ (starts A (t-s)).card := by
    apply card_le_card_of_injOn (fun x => s-x)
    · intro x hx
      obtain ⟨hs,ht⟩ := mem_inter.mp hx
      exact mem_filter.mpr ⟨(mem_filter.mp hs).2,by
        rw [show s-x+(t-s)=t-x by abel]; exact (mem_filter.mp ht).2⟩
    · intro x _ y _ he
      exact sub_right_injective he
  rw [starts_card] at h
  exact h.trans (Finset.le_sup (f := fun t => diffReps A t) (mem_erase.mpr ⟨sub_ne_zero.mpr hne.symm,mem_univ _⟩))

/-- Reflection centers share very few labels when all nonzero translates have
small overlap. The ordered mass at any set of centers obeys a finite bound. -/
theorem reflection_mass [Fintype G] (A : Finset G) (C : Finset G) :
    ∑ s ∈ C, Green33Multiplicity.reps A s ≤ A.card + C.card.choose 2 * maxDifference A := by
  let P := reflectedPart A
  let D := maxDifference A
  have bound (T : Finset G) :
      ∑ s ∈ T, (P s).card ≤ (T.biUnion P).card + T.card.choose 2 * D := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert s T hs ih =>
      have hsub : P s ∩ T.biUnion P ⊆ T.biUnion (fun t => P s ∩ P t) := by
        intro x hx
        obtain ⟨hx,ht⟩ := mem_inter.mp hx
        obtain ⟨t,ht,hxt⟩ := mem_biUnion.mp ht
        exact mem_biUnion.mpr ⟨t,ht,mem_inter.mpr ⟨hx,hxt⟩⟩
      have hcap : (P s ∩ T.biUnion P).card ≤ T.card * D := by
        apply ((card_le_card hsub).trans card_biUnion_le).trans
        calc
          _ ≤ ∑ _t ∈ T, D := sum_le_sum (fun t ht => partners_inter A (by rintro rfl; exact hs ht))
          _ = _ := by simp
      have hu := card_union_add_card_inter (P s) (T.biUnion P)
      rw [sum_insert hs,biUnion_insert,card_insert_of_notMem hs,Nat.choose_succ_succ,
        Nat.choose_one_right,add_mul]
      change (P s).card + (∑ u ∈ T, (P u).card) ≤
        (P s ∪ T.biUnion P).card + (T.card * D + T.card.choose 2 * D)
      omega
  have hle : (C.biUnion P).card ≤ A.card := card_le_card (by
    intro x hx
    obtain ⟨s,_,hp⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hp).1)
  simpa only [P,card_reflectedPart] using (bound C).trans (Nat.add_le_add_right hle _)

/-- Uniformly over every set of at most r reflection centers, the normalized
total ordered mass has asymptotic upper bound √2. -/
theorem bounded_center_mass {ι : Type*} {l : Filter ι} (M : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (M i))) (r : ℕ)
    (hM : Tendsto (fun i => (M i).val) l atTop)
    (hk : Tendsto (fun i => ((A i).card : ℝ)/Real.sqrt (M i)) l (𝓝 (Real.sqrt 2)))
    (hs : Tendsto (fun i => (((A i)+(A i)).card : ℝ)/(M i : ℝ)) l (𝓝 1))
    {c : ℝ} (hc : Real.sqrt 2 < c) :
    ∀ᶠ i in l, ∀ C : Finset (ZMod (M i)), C.card ≤ r →
      (∑ s ∈ C, (Green33Multiplicity.reps (A i) s : ℝ))/Real.sqrt (M i) < c := by
  have hd := vanishing_max_difference M A hM hk hs
  have hu := hk.add ((tendsto_const_nhds (x := (r.choose 2 : ℝ))).mul hd)
  rw [mul_zero,add_zero] at hu
  filter_upwards [hu.eventually_lt_const hc] with i hi
  intro C hC
  have hle := (reflection_mass (A i) C).trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hC)) _)
  have h : (∑ s ∈ C, (Green33Multiplicity.reps (A i) s : ℝ)) ≤
      (A i).card + (r.choose 2 : ℝ) * maxDifference (A i) := by exact_mod_cast hle
  have hm : 0 < Real.sqrt (M i) := Real.sqrt_pos.mpr (by exact_mod_cast (M i).pos)
  apply lt_of_le_of_lt ((div_le_div_iff_of_pos_right hm).mpr h)
  convert hi using 1; ring

#print axioms translate_bound
#print axioms vanishing_max_difference
#print axioms green_max_difference
#print axioms sidon_double_lift
#print axioms optimal_coefficient
#print axioms reflection_mass
#print axioms bounded_center_mass

end Green33TranslateOverlap
