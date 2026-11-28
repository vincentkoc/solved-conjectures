import Erdos478ConditionalGapAction

/-! # A prime-length root after conditioning on every smaller degree -/

namespace Erdos478.FirstCollision
open Polynomial Equiv Finset MulAction Function BinaryGap FrobeniusCounts
open scoped Classical
noncomputable section

variable (K : Type*) [Field K] [Algebra ℚ K]

abbrev GapRoots (k : ℕ) := (rationalGap k).rootSet K
def fixedGap (k : ℕ) (g : Aut K) := fixedCount (GapRoots K k) g

def lowerAction (s : Finset ℕ) : Aut K →* ((i : s) → Perm (GapRoots K i.val)) :=
  MonoidHom.pi fun i => MulAction.toPermHom (Aut K) (GapRoots K i.val)

abbrev LowerKernel (s : Finset ℕ) := (lowerAction K s).ker

theorem stable_count {s : Finset ℕ} (n : LowerKernel K s) (g : Aut K) {k : ℕ} (hk : k∈s) :
    fixedGap K k (n.val*g)=fixedGap K k g := by
  have same (x : GapRoots K k) : (n.val*g) • x=g • x := by
    exact congrArg (fun f : (i : s) → Perm (GapRoots K i.val) => f ⟨k,hk⟩ (g • x)) n.prop
  have eq : fixedBy (GapRoots K k) (n.val*g)=fixedBy (GapRoots K k) g :=
    Set.ext fun x => by simp only [mem_fixedBy,same]
  unfold fixedGap fixedCount
  rw [eq]

variable [Normal ℚ K]

/-- The kernel of the lower-degree action contains a full cycle on the new roots. -/
theorem lower_transitive (s : Finset ℕ) {l : ℕ} (hl : l.Prime)
    (small : ∀ k∈s, 0<k ∧ k<l)
    (split : ∀ k∈insert l s, ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (x y : GapRoots K l) : ∃ n : LowerKernel K s, n.val • x=y := by
  classical
  let : Fact l.Prime := ⟨hl⟩
  let F := rationalGap l
  let : Fact ((F.map (algebraMap ℚ K)).Splits) := ⟨split _ (mem_insert_self ..)⟩
  let π := Gal.restrict F K
  let ρ := Gal.galActionHom F K
  let φ := lowerAction K s
  have hB : ¬l ∣ Nat.card ((i : s) → Perm (GapRoots K i.val)) := by
    rw [Nat.card_pi]
    apply hl.prime.not_dvd_finsetProd
    intro i _
    rw [Nat.card_perm,Nat.card_eq_fintype_card,gap_card_of_pos K (small i i.prop).1
      (split i (mem_insert_of_mem i.prop)),hl.dvd_factorial]
    exact (small i i.prop).2.not_ge
  have sz : Fintype.card (F.rootSet K)=l := gap_card K hl (split _ (mem_insert_self ..))
  have irr : Irreducible F := GapFamilies.irreducible_gap_rat hl.pos
  have deg : F.natDegree=l := (card_rootSet_eq_natDegree irr.separable
    (split l (mem_insert_self ..))).symm.trans sz
  have hd : l ∣ Nat.card F.Gal := deg ▸ Gal.prime_degree_dvd_card irr (deg ▸ hl)
  let N := φ.ker.map π
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' l
    (PrimeDifferences.prime_dvd_kernel_image π (Gal.restrict_surjective F K) φ hd hB)
  obtain ⟨e,he⟩ := PrimeDifferences.prime_cycle_coordinates sz (ρ a.val)
    ((orderOf_injective (ρ.comp N.subtype) ((Gal.galActionHom_injective F K).comp Subtype.val_injective) a).trans ha)
  let t := e.symm y-e.symm x
  let u : N := a^t.val
  obtain ⟨g,hg,hπ⟩ := Subgroup.mem_map.mp u.prop
  have step : ρ (π g) x=y := by
    rw [hπ]
    change ρ (a.val^t.val) x=y
    rw [map_pow,← e.apply_symm_apply x,he]
    simp [t]
  exact ⟨⟨g,hg⟩,Subtype.ext ((Gal.galActionHom_restrict F K g x).symm.trans (congrArg Subtype.val step))⟩

theorem lower_pairs (s : Finset ℕ) {l : ℕ} (hl : l.Prime) (hb : broad l) (h₃ : 3<l)
    (small : ∀ k∈s, 0<k ∧ k<l)
    (split : ∀ k∈insert l s, ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (a b c d : GapRoots K l) (pat : a=b ↔ c=d) :
    ∃ n : LowerKernel K s, n.val • a=c ∧ n.val • b=d := by
  let : Fact (((rationalGap l).map (algebraMap ℚ K)).Splits) := ⟨split _ (mem_insert_self ..)⟩
  obtain ⟨g,ha,hb,fixes⟩ := pair_fixing_lower_degrees K hl hb h₃ s (fun i hi => (small i hi).2)
    (fun k hk => ⟨(small k hk).1,split k (mem_insert_of_mem hk)⟩) pat
  refine ⟨⟨g,?_⟩,Subtype.ext ha,Subtype.ext hb⟩
  apply _root_.funext
  intro i
  exact Equiv.ext fun x => Subtype.ext (fixes i.val i.prop x)

variable [FiniteDimensional ℚ K]

/-- Arbitrary nonnegative weights determined by the smaller root actions retain
at least one l-th of their mass on a hit, or one half in the two broad classes. -/
theorem weighted_hit (s : Finset ℕ) {l : ℕ} (hl : l.Prime)
    (small : ∀ k∈s, 0<k ∧ k<l)
    (split : ∀ k∈insert l s, ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (w : Aut K → ℝ) (hn : ∀ g, 0≤w g) (stable : ∀ (n : LowerKernel K s) g, w (n.val*g)=w g) :
    uniform (Aut K) w ≤ (if broad l ∧ 3<l then 2 else (l:ℝ)) *
      uniform (Aut K) (fun g => if 0<fixedGap K l g then w g else 0) := by
  have hc := gap_card K hl (split _ (mem_insert_self ..))
  let : Nontrivial (GapRoots K l) := Fintype.one_lt_card_iff_nontrivial.mp (hc.symm ▸ hl.one_lt)
  split_ifs with h
  · exact conditional_half (LowerKernel K s) (lower_pairs K s hl h.1 h.2 small split) w stable hn
  · have mom := weighted_coset (LowerKernel K s) w (fun g => (fixedCount (GapRoots K l) g : ℝ)) 1 stable
        (transitive_coset_mean (LowerKernel K s) (lower_transitive K s hl small split))
    rw [one_mul] at mom
    rw [← mom,← smul_eq_mul,← map_smul]
    apply uniform_mono
    intro g
    simp only [Pi.smul_apply,smul_eq_mul]
    split_ifs with hp
    · have le : fixedCount (GapRoots K l) g≤l := (Nat.card_le_card_of_injective
          (Subtype.val : fixedBy (GapRoots K l) g → _) Subtype.val_injective).trans_eq
          (Nat.card_eq_fintype_card.trans hc)
      exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr le) (hn g)).trans_eq (mul_comm ..)
    · simp only [fixedGap] at hp
      simp [show fixedCount (GapRoots K l) g=0 by omega]

#print axioms GapRoots
#print axioms fixedGap
#print axioms lowerAction
#print axioms LowerKernel
#print axioms stable_count
#print axioms lower_transitive
#print axioms lower_pairs
#print axioms weighted_hit
end
end Erdos478.FirstCollision
