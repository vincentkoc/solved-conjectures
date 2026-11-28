import CunninghamPairedCountingForms

/-! Exact-length paired counts at a fixed gap and the mean of their limiting coefficients. -/

namespace CunninghamChain.GapMean

open Finset Real Polynomial BatemanHornConjecture Filter Asymptotics
open scoped Topology

noncomputable def seedCount (P : ℕ → Prop) (x : ℝ) : ℕ := by
  classical exact ((range (⌊x⌋₊+1)).filter P).card

def Exact (k l h n : ℕ) : Prop :=
  IsFirstKindChainOfLength n k ∧ IsSecondKindChainOfLength (n+(h+2)) l

private lemma eval_ge_seed (k l h n : ℕ) {f} (hf : f∈pairedForms k l h) :
    n≤(f.eval (n:ℤ)).natAbs := by
  have pos (a b : ℤ) (ha : 1≤a) (hb : 0≤b) : n≤((C a*X+C b).eval (n:ℤ)).natAbs := by
    simp only [eval_add,eval_mul,eval_C,eval_X]
    have le : (n:ℤ)≤a*n+b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (Nat.cast_nonneg (α:=ℤ) n)]
    exact_mod_cast le.trans (Int.le_natAbs)
  change f∈(range k).image (form 1) ∪ (range l).image (shifted h) at hf
  rcases mem_union.mp hf with hf|hf
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hf
    exact pos _ _ (by positivity : 0<(2:ℤ)^i) (by simp; have := one_le_pow₀ (by decide : 1≤(2:ℤ)) (n:=i); omega)
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hf
    exact pos _ _ (by positivity : 0<(2:ℤ)^j) (by positivity)

private lemma prefix_count (k l h : ℕ) (x : ℝ) :
    CountSimultaneousPrimes (pairedForms k l h) x = seedCount (Prefix k l h) x := by
  classical
  unfold CountSimultaneousPrimes seedCount
  congr 1
  exact filter_congr (fun n _ => canonical_prefix k l h n)

/-- A failed local condition bounds all the true prime-prefix seeds and annuls
the full singular series. -/
theorem obstructed_gap {k l h : ℕ} (pos : 0<k+l) (no : ¬SchinzelCondition (pairedForms k l h)) :
    series k l h=0 ∧ ∃ q : ℕ, q.Prime ∧ ∀ n, Prefix k l h n → n≤q := by
  classical
  unfold SchinzelCondition at no
  push Not at no
  obtain ⟨q,hq,block⟩ := no
  let : Fact q.Prime := ⟨hq⟩
  have all : OmegaP (pairedForms k l h) q=q := by
    have eq : {z : ZMod q | ∃ f∈pairedForms k l h, (f.map (Int.castRingHom (ZMod q))).eval z=0}=Set.univ := by
      apply Set.eq_univ_of_forall; intro z
      obtain ⟨f,hf,hdiv⟩ := block z.val
      refine ⟨f,hf,?_⟩
      have zero := (ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval (z.val:ℤ)) q).mpr hdiv
      have eq := eval₂_at_apply (p:=f) (Int.castRingHom (ZMod q)) (z.val:ℤ)
      rw [eval_map]
      simpa only [Int.coe_castRingHom,Int.cast_natCast,ZMod.natCast_zmod_val] using eq.trans zero
    rw [OmegaP,eq,Set.ncard_univ,Nat.card_eq_fintype_card,ZMod.card]
  have van : ∀ᶠ N : ℕ in atTop, BatemanHornPartialProduct (pairedForms k l h) N=0 := by
    filter_upwards [eventually_gt_atTop q] with N big
    apply prod_eq_zero (Nat.mem_primesBelow.mpr ⟨big,hq⟩)
    simp [all,hq.ne_zero]
  exact ⟨tendsto_nhds_unique (canonical_series_limit pos h) ((tendsto_congr' van).mpr tendsto_const_nhds),
    q,hq,fun n pref => by
      obtain ⟨f,hf,hit⟩ := block n
      have eq := (Nat.prime_dvd_prime_iff_eq hq ((canonical_prefix ..).mpr pref f hf)).mp
        (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hit)
      exact (eval_ge_seed k l h n hf).trans eq.ge⟩

private lemma small_scale (m : ℕ) :
    Tendsto (fun x : ℝ => (log x)^m/x) atTop (𝓝 0) := by
  simpa only [rpow_natCast,rpow_one] using
    (isLittleO_log_rpow_rpow_atTop (m:ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero

private theorem prefix_limit (bh : type_of% BatemanHornConjecture.bateman_horn_conjecture)
    {k l : ℕ} (hk : 0<k) (hl : 0<l) (h : ℕ) :
    Tendsto (fun x : ℝ => (seedCount (Prefix k l h) x:ℝ) * ((log x)^(k+l)/x)) atTop (𝓝 (series k l h)) := by
  classical
  let F := pairedForms k l h
  by_cases cond : SchinzelCondition F
  · have card := pairedForms_card k l h
    have non : F.Nonempty := card_pos.mp (card ▸ (show 0<k+l by omega))
    have dg : DegreesProduct F=1 := prod_eq_one (fun f hf => (family_bunyakovsky k l h hf).2)
    obtain ⟨C,cp,lim,pred⟩ := bh F non (fun f hf => (family_bunyakovsky k l h hf).1) cond
    have ec := tendsto_nhds_unique lim (canonical_series_limit (show 0<k+l by omega) h)
    subst C
    dsimp only [F] at pred dg
    rw [dg,Nat.cast_one,div_one,pairedForms_card] at pred
    simp_rw [prefix_count] at pred
    have nz : ∀ᶠ x : ℝ in atTop, series k l h*x/(log x)^(k+l)≠0 := by
      filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      have lp := log_pos hx
      have xp : 0<x := by linarith
      positivity
    have norm := ((isEquivalent_iff_tendsto_one nz).mp pred).mul_const (series k l h)
    rw [one_mul] at norm
    apply norm.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have lp := (log_pos hx).ne'
    have xp : x≠0 := by linarith
    simp only [Pi.div_apply]
    field_simp
  · obtain ⟨zero,q,_,small⟩ := obstructed_gap (show 0<k+l by omega) cond
    rw [zero]
    have bound (x : ℝ) : seedCount (Prefix k l h) x≤q+1 := by
      unfold seedCount
      simpa using card_le_card (t:=range (q+1)) (fun n mem => mem_range.mpr (Nat.lt_succ_of_le (small n (mem_filter.mp mem).2)))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun _ => (0:ℝ)) (h:=fun x => (q+1:ℕ)*((log x)^(k+l)/x)) tendsto_const_nhds
    · simpa using (small_scale (k+l)).const_mul ((q+1:ℕ):ℝ)
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      have := log_pos hx; have xp : 0<x := by linarith
      positivity
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      have := log_pos hx; have xp : 0<x := by linarith
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast bound x) (by positivity)

private theorem exact_sandwich {k l : ℕ} (hk : 0<k) (hl : 0<l) (h : ℕ) (x : ℝ) :
    seedCount (Exact k l h) x ≤ seedCount (Prefix k l h) x ∧
      seedCount (Prefix k l h) x ≤ seedCount (Exact k l h) x +
        (seedCount (Prefix (k+1) l h) x + seedCount (Prefix k (l+1) h) x) := by
  classical
  let S (P : ℕ → Prop) := (range (⌊x⌋₊+1)).filter P
  let A := S (Exact k l h)
  let P := S (Prefix k l h)
  let L := S (Prefix (k+1) l h)
  let R := S (Prefix k (l+1) h)
  have sub : A ⊆ P := by
    intro n hn
    obtain ⟨bound,ex⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨bound,ex.1.2.1,ex.2.2.1⟩
  have cover : P ⊆ A ∪ (L∪R) := by
    intro n hn
    obtain ⟨bound,left,right⟩ := mem_filter.mp hn
    by_cases fst : (firstKindTerm n k).Prime
    · apply mem_union_right _ (mem_union_left _ ?_)
      refine mem_filter.mpr ⟨bound,fun i lt => ?_,right⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ lt) with hi|rfl
      · exact left i hi
      · exact fst
    by_cases snd : (secondKindTerm (n+(h+2)) l).Prime
    · apply mem_union_right _ (mem_union_right _ ?_)
      refine mem_filter.mpr ⟨bound,left,fun i lt => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ lt) with hi|rfl
      · exact right i hi
      · exact snd
    · exact mem_union_left _ (mem_filter.mpr ⟨bound,⟨hk,left,fst⟩,⟨hl,right,snd⟩⟩)
  exact ⟨card_le_card sub,(card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add_left (card_union_le L R) _))⟩

private lemma drop_level (f : ℝ → ℝ) (m : ℕ) {C : ℝ}
    (lim : Tendsto (fun x : ℝ => f x*((log x)^(m+1)/x)) atTop (𝓝 C)) :
    Tendsto (fun x : ℝ => f x*((log x)^m/x)) atTop (𝓝 0) := by
  apply (lim.div_atTop Real.tendsto_log_atTop).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  have nz := (log_pos hx).ne'
  have xp : x≠0 := by linarith
  rw [pow_succ]
  field_simp

/-- Under the pinned Bateman–Horn conjecture the fixed-gap count with both
stops enforced has the full paired singular series as its normalized limit,
including a zero limit for locally obstructed gaps. -/
theorem exact_gap_limit (bh : type_of% BatemanHornConjecture.bateman_horn_conjecture)
    {k l : ℕ} (hk : 0<k) (hl : 0<l) (h : ℕ) :
    Tendsto (fun x : ℝ => (seedCount (Exact k l h) x:ℝ)*((log x)^(k+l)/x)) atTop (𝓝 (series k l h)) := by
  let m := k+l
  let scale (x : ℝ) := (log x)^m/x
  let f (x : ℝ) := (seedCount (Prefix k l h) x:ℝ)*scale x
  let L (x : ℝ) := (seedCount (Prefix (k+1) l h) x:ℝ)*scale x
  let R (x : ℝ) := (seedCount (Prefix k (l+1) h) x:ℝ)*scale x
  have fl := prefix_limit bh hk hl h
  have ll : Tendsto L atTop (𝓝 0) := drop_level _ m (by
    simpa only [m,show k+1+l=k+l+1 by omega] using prefix_limit bh (Nat.succ_pos k) hl h)
  have rl : Tendsto R atTop (𝓝 0) := drop_level _ m (by
    simpa only [m,Nat.add_assoc] using prefix_limit bh hk (Nat.succ_pos l) h)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun x => f x-(L x+R x)) (h:=f)
    (by simpa using fl.sub (ll.add rl)) fl
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have sp : 0 ≤ scale x := div_nonneg (pow_nonneg (log_pos hx).le _) (by linarith)
    have bd : (seedCount (Prefix k l h) x:ℝ) ≤ (seedCount (Exact k l h) x:ℝ) +
        (seedCount (Prefix (k+1) l h) x+ (seedCount (Prefix k (l+1) h) x:ℝ)) := by
      exact_mod_cast (exact_sandwich hk hl h x).2
    have he := mul_le_mul_of_nonneg_right bd sp
    change f x-(L x+R x) ≤ (seedCount (Exact k l h) x:ℝ)*scale x
    dsimp only [f,L,R]
    linarith only [he]
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have sp : 0 ≤ scale x := div_nonneg (pow_nonneg (log_pos hx).le _) (by linarith)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (exact_sandwich hk hl h x).1) sp

/-- The seed-count limit is taken at each fixed gap before averaging over gaps.
The outer limit equals the product of the two single-chain constants. -/
theorem mean_exact_gap_limits (bh : type_of% BatemanHornConjecture.bateman_horn_conjecture)
    {k l : ℕ} (hk : 0<k) (hl : 0<l) :
    Tendsto (average (fun h => limUnder atTop (fun x : ℝ =>
      (seedCount (Exact k l h) x:ℝ)*((log x)^(k+l)/x)))) atTop (𝓝 (chainConstant k*chainConstant l)) := by
  simpa only [(exact_gap_limit bh hk hl _).limUnder_eq] using mean_series hk hl

#print axioms exact_gap_limit
#print axioms mean_exact_gap_limits

#print axioms obstructed_gap

end CunninghamChain.GapMean
