import Green33StrictReduction

/-! Extremal orders of cyclic sum covers as a function of the size budget. -/

open Finset Filter Green33StrictReduction
open scoped Pointwise Topology

namespace Green33MaximalOrders

/-- A strict cover requires distinct summands in every representation. -/
def Covers {N : ℕ+} (strict : Bool) (A : Finset (ZMod N)) : Prop :=
  ∀ x, ∃ a ∈ A, ∃ b ∈ A, (strict = true → a ≠ b) ∧ a + b = x

theorem covers_true_iff {N : ℕ+} {A : Finset (ZMod N)} :
    Covers true A ↔ StrictCover A := by simp [Covers, StrictCover]

theorem covers_false_iff {N : ℕ+} {A : Finset (ZMod N)} :
    Covers false A ↔ A + A = univ := by
  constructor
  · intro h
    apply eq_univ_of_forall
    intro x
    obtain ⟨a, ha, b, hb, _, e⟩ := h x
    exact mem_add.mpr ⟨a, ha, b, hb, e⟩
  · intro h x
    obtain ⟨a, ha, b, hb, e⟩ := mem_add.mp (show x ∈ A + A by simp [h])
    exact ⟨a, ha, b, hb, by simp, e⟩

private lemma ordinary_of_covers {N : ℕ+} {s : Bool} {A : Finset (ZMod N)} (h : Covers s A) :
    A + A = univ := by
  apply covers_false_iff.mp
  intro x
  obtain ⟨a, ha, b, hb, _, e⟩ := h x
  exact ⟨a, ha, b, hb, by simp, e⟩

private lemma card_bound {N : ℕ+} {s : Bool} {A : Finset (ZMod N)} (h : Covers s A) :
    N.val ≤ A.card ^ 2 := by
  have hc : (A + A).card ≤ A.card * A.card := card_add_le
  simpa [ordinary_of_covers h, ZMod.card, sq] using hc

private def Feasible (s : Bool) (k n : ℕ) : Prop :=
  n = 0 ∨ ∃ N : ℕ+, N.val = n ∧ ∃ A : Finset (ZMod N), A.card ≤ k ∧ Covers s A

/-- Largest positive modulus admitting a cover with at most k elements. Use zero
when the feasible set is empty. -/
noncomputable def maxOrder (s : Bool) (k : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Feasible s k) (k ^ 2)

private lemma feasible_max (s : Bool) (k : ℕ) : Feasible s k (maxOrder s k) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (show Feasible s k 0 from Or.inl rfl)

theorem le_maxOrder {s : Bool} {k : ℕ} {N : ℕ+} {A : Finset (ZMod N)}
    (hk : A.card ≤ k) (h : Covers s A) : N.val ≤ maxOrder s k := by
  classical
  exact Nat.le_findGreatest ((card_bound h).trans (Nat.pow_le_pow_left hk 2))
    (show Feasible s k N.val from Or.inr ⟨N, rfl, A, hk, h⟩)

theorem strict_le_ordinary (k : ℕ) : maxOrder true k ≤ maxOrder false k := by
  rcases feasible_max true k with hz | ⟨N, hN, A, hk, h⟩
  · simp [hz]
  · rw [← hN]
    exact le_maxOrder hk (covers_false_iff.mpr (ordinary_of_covers h))

/-- Replicate every label of a finite strict seed by a short progression. The
coprime moduli Q form an entire arithmetic progression. -/
theorem strict_seed_lifts {M : ℕ+} {A : Finset (ZMod M)} (hA : StrictCover A) :
    ∃ s : ℕ, 0 < s ∧ ∀ l : ℕ, let Q := s*l+1
      Q^2*M.val ≤ maxOrder true (A.card*(s+Q)) := by
  classical
  let k := A.card
  let s := k.factorial * M.val
  have hs : 0 < s := Nat.mul_pos k.factorial_pos M.pos
  refine ⟨s, hs, ?_⟩
  intro l
  let Q := s*l+1
  have hQ : s*l+1 = Q := rfl
  let : NeZero Q := ⟨Nat.succ_ne_zero _⟩
  have hc : (Q^2).Coprime M.val := by
    apply Nat.Coprime.pow_left
    have h : Q = M.val * (k.factorial * l) + 1 := by dsimp [Q,s]; ring
    rw [h, Nat.coprime_mul_left_add_left]; simp
  let N : ℕ+ := ⟨Q^2*M.val, Nat.mul_pos (pow_pos (NeZero.pos Q) _) M.pos⟩
  let e : ZMod N ≃+ ZMod (Q^2) × ZMod M := (ZMod.chineseRemainder hc).toAddEquiv
  let lab (i : Fin k) : ZMod M := (A.equivFin.symm i).val
  have lab_inj : Function.Injective lab := fun _ _ h =>
    A.equivFin.symm.injective (Subtype.ext h)
  let arm (p : Fin k × Fin (s+Q)) : ZMod N :=
    e.symm (((s + p.1.val * Q : ℕ) : ZMod (Q^2)) * (p.2.val : ZMod (Q^2)), lab p.1)
  let B := univ.image arm
  have arm_mem (i : Fin k) (t : Fin (s+Q)) : arm (i,t) ∈ B :=
    mem_image_of_mem _ (mem_univ _)
  have hcard : B.card ≤ k * (s+Q) := by
    simpa [B, Fintype.card_prod] using (card_image_le (s := univ) (f := arm))
  apply le_maxOrder (N := N) hcard
  apply covers_true_iff.mpr
  intro x
  obtain ⟨a, ha, b, hb, hab, habx⟩ := hA (e x).2
  let i := A.equivFin ⟨a,ha⟩
  let j := A.equivFin ⟨b,hb⟩
  have hi : lab i = a := by simp [lab,i]
  have hj : lab j = b := by simp [lab,j]
  have hij : i ≠ j := fun h => hab (by simpa only [hi, hj] using congrArg lab h)
  have hit {u v : Fin k} (huv : u < v) (he : lab u + lab v = (e x).2) :
      ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ a+b=x := by
    have hd : v.val-u.val ∣ s := dvd_mul_of_dvd_left
      (Nat.dvd_factorial (Nat.sub_pos_of_lt huv) ((Nat.sub_le _ _).trans v.isLt.le)) M.val
    obtain ⟨t, ht, w, hw, htw⟩ := Green33StrictCoverLift.progression_pair hs huv hd hQ (e x).1
    let T : Fin (s+Q) := ⟨t,ht⟩
    let W : Fin (s+Q) := ⟨w,hw⟩
    refine ⟨_, arm_mem u T, _, arm_mem v W, ?_, ?_⟩
    · intro heq
      have hh := congrArg (fun z : ZMod N => (e z).2) heq
      exact huv.ne (lab_inj (by simpa [arm] using hh))
    · apply e.injective
      rw [map_add]
      simp only [arm, AddEquiv.apply_symm_apply]
      exact Prod.ext htw he
  rcases lt_or_gt_of_ne hij with h | h
  · exact hit h (by simpa [hi,hj] using habx)
  · exact hit h (by simpa [hi,hj,add_comm] using habx)

theorem maxOrder_mono (s : Bool) : Monotone (maxOrder s) := by
  intro k K h
  rcases feasible_max s k with hz | ⟨N, hN, A, hk, hA⟩
  · simp [hz]
  · rw [← hN]
    exact le_maxOrder (hk.trans h) hA

/-- Every sufficiently large budget retains the seed's quadratic efficiency
up to a fixed additive loss in the budget. -/
theorem strict_seed_all_budgets {M : ℕ+} {A : Finset (ZMod M)} (hA : StrictCover A) :
    ∃ C : ℕ, ∀ K ≥ C, M.val*(K-C)^2 ≤ A.card^2*maxOrder true K := by
  let k := A.card
  have hk : 0 < k := by
    obtain ⟨a,ha,_,_,_,_⟩ := hA 0
    exact card_pos.mpr ⟨a,ha⟩
  obtain ⟨s,hs,H⟩ := strict_seed_lifts hA
  let d := k*s
  have hd : 0 < d := Nat.mul_pos hk hs
  refine ⟨3*d, ?_⟩
  intro K hK
  let n := K/d
  have hn : 2 ≤ n := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  let Q := s*(n-2)+1
  have hlow := Nat.div_mul_le_self K d
  have hhigh := Nat.lt_mul_div_succ K hd
  have hsplit : k*s*(n-2) + 2*d = d*n := by
    rw [show d*n = d*((n-2)+2) from congrArg (d*·) (by omega), Nat.mul_add]
    dsimp [d]; ring
  have hkS : k ≤ d := Nat.le_mul_of_pos_right _ hs
  have hbudget : k*(s+Q) ≤ K := by
    change n*d ≤ K at hlow
    dsimp only [Q]
    change k*s*(n-2) + 2*(k*s) = k*s*n at hsplit
    change k ≤ k*s at hkS
    change n*(k*s) ≤ K at hlow
    nlinarith only [hlow,hsplit,hkS]
  have hnear : K-3*d ≤ k*Q := by
    change K < d*(n+1) at hhigh
    have hsub := Nat.sub_add_cancel hK
    dsimp only [Q]
    change k*s*(n-2) + 2*d = d*n at hsplit
    nlinarith only [hhigh,hsplit,hsub]
  have hmax := (H (n-2)).trans (maxOrder_mono true hbudget)
  calc
    M.val*(K-3*d)^2 ≤ M.val*(k*Q)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnear 2)
    _ = k^2*(Q^2*M.val) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hmax

/-- Order per quadratic size of a finite cyclic strict sum cover. -/
def strictDensities : Set ℝ :=
  {z | ∃ N : ℕ+, ∃ A : Finset (ZMod N), StrictCover A ∧ z = (N : ℝ) / (A.card : ℝ)^2}

noncomputable def orderConstant : ℝ := sSup strictDensities

private lemma card_pos_of_strict {N : ℕ+} {A : Finset (ZMod N)} (hA : StrictCover A) :
    0 < A.card := by
  obtain ⟨a,ha,_,_,_,_⟩ := hA 0
  exact card_pos.mpr ⟨a,ha⟩

private lemma density_le_half {N : ℕ+} {A : Finset (ZMod N)} (hA : StrictCover A) :
    (N : ℝ) / (A.card : ℝ)^2 ≤ 1/2 := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast N.pos
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast card_pos_of_strict hA
  have h := strict_size_gap hA
  rw [← Real.sqrt_mul (by norm_num)] at h
  have hr : Real.sqrt (2*(N : ℝ)) ≤ (A.card : ℝ) := by linarith
  have hh := (Real.sqrt_le_iff.mp hr).2
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  linarith

private lemma densities_bdd : BddAbove strictDensities := by
  refine ⟨1/2, ?_⟩
  rintro z ⟨N,A,h,rfl⟩
  exact density_le_half h

private lemma seed_le_constant {N : ℕ+} {A : Finset (ZMod N)} (h : StrictCover A) :
    (N : ℝ)/(A.card : ℝ)^2 ≤ orderConstant :=
  le_csSup densities_bdd ⟨N, A, h, rfl⟩

private def haanpaa : Finset (ZMod 56) := {0, 1, 12, 15, 22, 29, 32, 43, 44, 48, 50, 52}

private lemma small_seed : (7/18 : ℝ) ∈ strictDensities := by
  let M : ℕ+ := ⟨56, by decide⟩
  refine ⟨M, haanpaa, ?_, ?_⟩
  · change ∀ z : ZMod 56, ∃ a ∈ haanpaa, ∃ b ∈ haanpaa, a ≠ b ∧ a+b=z
    decide +kernel
  · have hc : haanpaa.card = 12 := by decide +kernel
    change (7/18 : ℝ) = 56 / (haanpaa.card : ℝ)^2
    rw [hc]; norm_num

theorem orderConstant_bounds : 7/18 ≤ orderConstant ∧ orderConstant ≤ 1/2 :=
  ⟨le_csSup densities_bdd small_seed, csSup_le ⟨_,small_seed⟩ (by
    rintro z ⟨N,A,h,rfl⟩; exact density_le_half h)⟩

private lemma ordinary_order_bound {N : ℕ+} {A : Finset (ZMod N)} (hA : A+A=univ) :
    (N : ℝ) ≤ orderConstant * ((A.card : ℝ) + 2*(A.card.sqrt+1 : ℕ)+1)^2 := by
  obtain ⟨M, _, B, hB, h⟩ := exists_strict_lift A hA
  have hn : 0 < (N : ℝ) := by exact_mod_cast N.pos
  have hm : 0 < (M : ℝ) := by exact_mod_cast M.pos
  have hb : 0 < (B.card : ℝ) := by exact_mod_cast card_pos_of_strict hB
  have hc : 0 ≤ orderConstant := le_trans (by norm_num : (0:ℝ) ≤ 7/18) orderConstant_bounds.1
  have hM := (div_le_iff₀ (sq_pos_of_pos hb)).mp (seed_le_constant hB)
  let z : ℝ := (A.card : ℝ) + 2*(A.card.sqrt+1 : ℕ)+1
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hr : (B.card : ℝ)*Real.sqrt N ≤ z*Real.sqrt M :=
    (div_le_div_iff₀ (Real.sqrt_pos.2 hm) (Real.sqrt_pos.2 hn)).mp h
  have hs := pow_le_pow_left₀ (mul_nonneg hb.le (Real.sqrt_nonneg _)) hr 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hn.le, Real.sq_sqrt hm.le] at hs
  change (N : ℝ) ≤ orderConstant * z^2
  apply le_of_mul_le_mul_left (a := (B.card : ℝ)^2) _ (sq_pos_of_pos hb)
  calc
    (B.card : ℝ)^2*N ≤ z^2*M := hs
    _ ≤ z^2*(orderConstant*(B.card : ℝ)^2) := mul_le_mul_of_nonneg_left hM (sq_nonneg _)
    _ = _ := by ring


private noncomputable def normalized (s : Bool) (k : ℕ) : ℝ := (maxOrder s k : ℝ)/(k : ℝ)^2

private lemma eventually_lower {a : ℝ} (ha : a < orderConstant) :
    ∀ᶠ k : ℕ in atTop, a < normalized true k := by
  obtain ⟨z, ⟨M,A,hA,rfl⟩, ha⟩ := (lt_csSup_iff densities_bdd ⟨_,small_seed⟩).mp ha
  obtain ⟨C, hC⟩ := strict_seed_all_budgets hA
  let v := (M : ℝ)/(A.card : ℝ)^2
  have ht : Tendsto (fun k : ℕ => v*(1-(C:ℝ)/k)^2) atTop (𝓝 v) := by
    have h := ((tendsto_const_nhds (x := (1:ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (C:ℝ))).pow 2
    simpa using h.const_mul v
  filter_upwards [ht.eventually_const_lt ha, eventually_ge_atTop C, eventually_ge_atTop 1]
    with k hv hk hk'
  apply hv.trans_le
  have hR : (M : ℝ)*((k:ℝ)-C)^2 ≤ (A.card:ℝ)^2*(maxOrder true k : ℝ) := by
    exact_mod_cast hC k hk
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hap : 0 < (A.card:ℝ) := by exact_mod_cast card_pos_of_strict hA
  dsimp only [normalized,v]
  field_simp [hkp.ne',hap.ne']
  nlinarith only [hR]

private lemma eventually_upper {b : ℝ} (hb : orderConstant < b) :
    ∀ᶠ k : ℕ in atTop, normalized false k < b := by
  have hc : 0 ≤ orderConstant := le_trans (by norm_num : (0:ℝ) ≤ 7/18) orderConstant_bounds.1
  have hroot : Tendsto (fun k : ℕ => Real.sqrt k / k) atTop (𝓝 0) := by
    simp only [Real.sqrt_div_self']
    exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have ht : Tendsto (fun k : ℕ => orderConstant*(1+2*(Real.sqrt k / k)+3/k)^2) atTop
      (𝓝 orderConstant) := by
    have h := (((tendsto_const_nhds (x := (1:ℝ))).add (hroot.const_mul 2)).add
      (tendsto_const_div_atTop_nhds_zero_nat (3:ℝ))).pow 2
    simpa using h.const_mul orderConstant
  filter_upwards [ht.eventually_lt_const hb, eventually_ge_atTop 1] with k hsup hk
  apply lt_of_le_of_lt _ hsup
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  rcases feasible_max false k with hz | ⟨N,hn,A,ha,hA⟩
  · simp only [normalized,hz,Nat.cast_zero,zero_div]
    exact mul_nonneg hc (sq_nonneg _)
  have hf := ordinary_order_bound (covers_false_iff.mp hA)
  have hsize : (A.card:ℝ) ≤ k := by exact_mod_cast ha
  have hsqrt : (A.card.sqrt:ℝ) ≤ Real.sqrt k := Real.le_sqrt_of_sq_le
    (by exact_mod_cast (Nat.sqrt_le' A.card).trans ha)
  push_cast at hf
  have hbig : (N:ℝ) ≤ orderConstant*((k:ℝ)+2*Real.sqrt k+3)^2 := by
    apply hf.trans
    apply mul_le_mul_of_nonneg_left _ hc
    apply pow_le_pow_left₀ (by positivity)
    linarith
  dsimp only [normalized]
  rw [← hn, div_le_iff₀ (sq_pos_of_pos hkp)]
  calc
    (N:ℝ) ≤ orderConstant*((k:ℝ)+2*Real.sqrt k+3)^2 := hbig
    _ = _ := by field_simp [hkp.ne']

/-- With a size budget, both normalized maximal orders converge along all
natural numbers to the supremum of finite strict order densities. -/
theorem budget_limits (s : Bool) :
    Tendsto (fun k : ℕ => (maxOrder s k : ℝ)/(k : ℝ)^2) atTop (𝓝 orderConstant) := by
  have hle (k : ℕ) : normalized true k ≤ normalized false k :=
    div_le_div_of_nonneg_right (by exact_mod_cast strict_le_ordinary k) (sq_nonneg _)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_lower ha] with k hk
    cases s
    · exact hk.trans_le (hle k)
    · exact hk
  · intro b hb
    filter_upwards [eventually_upper hb] with k hk
    cases s
    · exact hk
    · exact (hle k).trans_lt hk


private def ExactFeasible (s : Bool) (k n : ℕ) : Prop :=
  n = 0 ∨ ∃ N : ℕ+, N.val = n ∧ ∃ A : Finset (ZMod N), A.card = k ∧ 0 ∈ A ∧ Covers s A

/-- Graham–Sloane's largest order using exactly k distinct labels, including
zero. Their functions start at k=2, with the exceptional value nγ(2)=1. -/
noncomputable def grahamSloaneOrder (s : Bool) (k : ℕ) : ℕ := by
  classical
  exact if s = true ∧ k = 2 then 1 else Nat.findGreatest (ExactFeasible s k) (k^2)

private lemma univ_covers {k : ℕ} (hk : 3 ≤ k) (s : Bool) :
    let N : ℕ+ := ⟨k, by omega⟩
    Covers (N := N) s univ := by
  intro N x
  by_cases hx : x = 0
  · subst x
    refine ⟨1,mem_univ _, -1,mem_univ _, ?_, by simp⟩
    intro _ he
    have ht : ((2:ℕ) : ZMod N) = 0 := by push_cast; linear_combination he
    have hd := (ZMod.natCast_eq_zero_iff 2 k).mp ht
    have := Nat.le_of_dvd (by decide : 0<2) hd
    omega
  · exact ⟨0,mem_univ _,x,mem_univ _,fun _ => Ne.symm hx,zero_add x⟩

private lemma pad_and_translate {N : ℕ+} {A : Finset (ZMod N)} {s : Bool} {k : ℕ}
    (hA : Covers s A) (hk : A.card ≤ k) (hN : k ≤ N.val) :
    ∃ B : Finset (ZMod N), B.card = k ∧ 0 ∈ B ∧ Covers s B := by
  classical
  obtain ⟨T,hAT,_,hTk⟩ := exists_subsuperset_card_eq (subset_univ A) hk
    (show k ≤ (univ : Finset (ZMod N)).card by simpa [ZMod.card] using hN)
  obtain ⟨c,hc,_,_,_,_⟩ := hA 0
  let shift : ZMod N ↪ ZMod N := ⟨fun t => t-c, fun _ _ h => sub_left_injective h⟩
  refine ⟨T.map shift, (card_map _).trans hTk, mem_map.mpr ⟨c,hAT hc,sub_self _⟩, ?_⟩
  intro x
  obtain ⟨a,ha,b,hb,hd,he⟩ := hA (x+c+c)
  refine ⟨shift a,mem_map.mpr ⟨a,hAT ha,rfl⟩,shift b,mem_map.mpr ⟨b,hAT hb,rfl⟩,
    fun hs h => hd hs (shift.injective h), ?_⟩
  change a-c+(b-c)=x
  linear_combination he

/-- From k=3 onward, padding and translation identify the size-budget maximum
with the original largest-order function. -/
theorem exact_eq_budget {k : ℕ} (hk : 3 ≤ k) (s : Bool) :
    grahamSloaneOrder s k = maxOrder s k := by
  classical
  simp only [grahamSloaneOrder, show ¬ (s = true ∧ k = 2) by omega, ↓reduceIte]
  apply le_antisymm
  · apply Nat.findGreatest_mono_left
    intro n h
    rcases h with h | ⟨N, hn, A, hcard, _, hA⟩
    · exact Or.inl h
    · exact Or.inr ⟨N, hn, A, hcard.le, hA⟩
  · let M : ℕ+ := ⟨k,by omega⟩
    have hmax : k ≤ maxOrder s k := le_maxOrder (N := M) (A := univ)
      (by rw [card_univ, ZMod.card]; exact le_rfl) (univ_covers hk s)
    rcases feasible_max s k with hz | ⟨N, hn, A, hcard, hA⟩
    · omega
    obtain ⟨B,hB⟩ := pad_and_translate hA hcard (hn ▸ hmax)
    apply Nat.le_findGreatest (Nat.findGreatest_le _)
    exact Or.inr ⟨N,hn,B,hB⟩

/-- Both original largest-order functions normalized by k² converge to the same
constant sSup {N/|A|² : A is a finite strict cyclic cover}. -/
theorem graham_sloane_limits (s : Bool) :
    Tendsto (fun k : ℕ => (grahamSloaneOrder s k : ℝ)/(k : ℝ)^2) atTop (𝓝 orderConstant) := by
  apply (budget_limits s).congr'
  filter_upwards [eventually_ge_atTop 3] with k hk
  rw [exact_eq_budget hk]


private lemma threshold {N : ℕ+} {A : Finset (ZMod N)} (hA : StrictCover A) {t : ℝ}
    (ht : 0 < t) : 1/t^2 < (N:ℝ)/(A.card:ℝ)^2 ↔ (A.card:ℝ)/Real.sqrt N < t := by
  have hN : 0 < (N:ℝ) := by exact_mod_cast N.pos
  have hk : 0 < (A.card:ℝ) := by exact_mod_cast card_pos_of_strict hA
  rw [div_lt_div_iff₀ (sq_pos_of_pos ht) (sq_pos_of_pos hk),
    div_lt_iff₀ (Real.sqrt_pos.mpr hN), one_mul]
  have h : (N:ℝ)*t^2 = (t*Real.sqrt N)^2 := by rw [mul_pow,Real.sq_sqrt hN.le,mul_comm]
  rw [h]
  exact sq_lt_sq₀ hk.le (mul_nonneg ht.le (Real.sqrt_nonneg _))

/-- The literal Green 33 predicate is equivalent to the common limiting order
attaining its counting upper bound. -/
theorem green_iff_orderConstant : OrdinaryLimit ↔ orderConstant = 1/2 := by
  rw [ordinary_iff_finite_strict]
  have hc : 0 < orderConstant := lt_of_lt_of_le (by norm_num : (0:ℝ)<7/18) orderConstant_bounds.1
  have htwo := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  constructor
  · intro H
    apply le_antisymm orderConstant_bounds.2
    by_contra! h
    let t := 1/Real.sqrt orderConstant
    have ht : 0 < t := by dsimp only [t]; positivity
    have hval : 1/t^2 = orderConstant := by
      dsimp only [t]; rw [div_pow,Real.sq_sqrt hc.le]; field_simp
    have hlarge : Real.sqrt 2 < t := by
      apply (sq_lt_sq₀ (Real.sqrt_nonneg 2) ht.le).mp
      rw [htwo]
      dsimp only [t]
      rw [div_pow,Real.sq_sqrt hc.le,lt_div_iff₀ hc]; linarith
    obtain ⟨N,A,hA,hk⟩ := H (t-Real.sqrt 2) (sub_pos.mpr hlarge)
    have hd := (threshold hA ht).mpr (by linarith)
    rw [hval] at hd
    exact (seed_le_constant hA).not_gt hd
  · intro h ε hε
    let t := Real.sqrt 2 + ε
    have ht : 0 < t := by dsimp only [t]; positivity
    have hthreshold : 1/t^2 < orderConstant := by
      rw [h,div_lt_div_iff₀ (sq_pos_of_pos ht) (by norm_num : (0:ℝ)<2)]
      have hh := (sq_lt_sq₀ (Real.sqrt_nonneg 2) ht.le).mpr (show Real.sqrt 2<t by
        dsimp only [t]; linarith)
      linarith
    obtain ⟨v,⟨N,A,hA,rfl⟩,hv⟩ := (lt_csSup_iff densities_bdd ⟨_,small_seed⟩).mp hthreshold
    exact ⟨N,A,hA,(threshold hA ht).mp hv⟩

#print axioms green_iff_orderConstant

#print axioms covers_true_iff
#print axioms covers_false_iff
#print axioms le_maxOrder
#print axioms strict_le_ordinary
#print axioms strict_seed_lifts
#print axioms maxOrder_mono
#print axioms strict_seed_all_budgets
#print axioms orderConstant_bounds
#print axioms budget_limits
#print axioms exact_eq_budget
#print axioms graham_sloane_limits

end Green33MaximalOrders
