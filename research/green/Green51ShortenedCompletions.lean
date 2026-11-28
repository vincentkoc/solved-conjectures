import Green51ExtensionFibres
import Green51DeletedLabels

/-! # Ambient completions of shortened linear-flat avoiding sets -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open Green51ShortenedColumns Green51ExtensionFibres Green51ShortenedProfiles Green51WeightTransform
open scoped Classical Pointwise
namespace Green51ShortenedCompletions
local notation "F" => ZMod 2
local notation "V" => Cube 11

/-- Sixteen distinct labels with zero sum. -/
def sixteens (A:Finset V) : Finset (Finset V) := (A.powersetCard 16).filter fun T=>syndrome T=0

/-- Weight-sixteen words select the sixteen-label zero sums bijectively. -/
theorem sixteen_count {A:Finset V} (D:Presentation A) :
    Green51ShortenedProfiles.multiplicity D.P.ker 16=(sixteens A).card := by
  classical
  apply card_bij (fun c _=>selected A c.val)
  · intro c hc
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨selected_sub ..,(selected_card ..).trans
      (mem_filter.mp hc).2⟩,?_⟩
    exact congrArg Prod.snd ((D.eval c.val).symm.trans c.property)
  · intro x _ y _ eq;exact Subtype.ext (selected_injective A eq)
  · intro T h
    obtain ⟨mem,z⟩:=mem_filter.mp h
    obtain ⟨sub,sz⟩:=mem_powersetCard.mp mem
    obtain ⟨w,hw⟩:=selected_onto A sub
    have n:(supp w).card=16:=(selected_card A w).symm.trans ((congrArg card hw).trans sz)
    have ker:D.P w=0:=by rw [D.eval,n,hw,z];decide
    exact ⟨⟨w,ker⟩,mem_filter.mpr ⟨mem_univ _,n⟩,hw⟩

private theorem profile_holes {n a b c d s h:ℕ} (lo:18≤n) (hi:n≤23)
    (p:(a,b,c,d,s)∈profiles n) (eq:(h+d)*2^(n-12)=s) :
    h=(if n=18 then 6+6*c else 24-n) ∧ (n=18 → c≤1) := by
  interval_cases n <;> norm_num [profiles] at p eq ⊢ <;> omega

/-- The one-point extension count and the sixteen-label relation multiplicity
in a fixed eleven-dimensional space. -/
theorem extension_counts {A:Finset V} (lo:18≤A.card) (hi:A.card≤23) (avoid:¬FlatAt A 0) :
    (holes A).card = (if A.card=18 then 6+6*(sixteens A).card else 24-A.card) ∧
    (A.card=18 → (sixteens A).card≤1) := by
  classical
  obtain ⟨D⟩:=presentation lo hi avoid
  have p:=profile D.P.ker lo hi (le_of_eq D.rank.symm) D.allowed
  have h:=hole_count lo avoid D
  change ((holes A).card+((dualWords D.P.ker).filter fun z=>(supp z).card=3).card)*
    Fintype.card D.P.ker=((dualWords D.P.ker).filter fun z=>(supp z).card%4=3).card at h
  rw [Module.card_eq_pow_finrank (K:=F),ZMod.card,D.rank] at h
  rw [sixteen_count D] at p
  exact profile_holes lo hi p h

/-- All 24-label supersets in the given ambient space whose doubles avoid a
linear three-space. -/
noncomputable def completions (A:Finset V) : Finset (Finset V) :=
  univ.filter fun B=>A⊆B ∧ B.card=24 ∧ ¬FlatAt B 0

set_option maxRecDepth 2048 in
/-- Count incidences between possible next labels and 24-label completions. -/
theorem completion_flags (A:Finset V) :
    (completions A).card*(24-A.card)=∑v∈holes A,(completions (insert v A)).card := by
  classical
  have row (B) (hb:B∈completions A) : ((holes A).filter (·∈B)).card=24-A.card := by
    obtain ⟨sub,sz,good⟩:=(mem_filter.mp hb).2
    have eq:(holes A).filter (·∈B)=B\A := by
      ext x
      simp only [holes,mem_filter,mem_univ,true_and,mem_sdiff]
      constructor
      · rintro ⟨⟨ha,_⟩,h⟩;exact ⟨h,ha⟩
      · rintro ⟨h,ha⟩
        exact ⟨⟨ha,fun bad=>good (Green51ElevenColumns.flat_mono (insert_subset h sub) bad)⟩,h⟩
    rw [eq,card_sdiff_of_subset sub,sz]
  have col (v) : ((completions A).filter (v∈·)).card=(completions (insert v A)).card := by
    have eq:(completions A).filter (v∈·)=completions (insert v A) := by
      ext B;simp only [completions,mem_filter,mem_univ,true_and,insert_subset_iff];tauto
    rw [eq]
  calc
    _ = ∑ _B∈completions A,(24-A.card) := by simp
    _ = ∑ B∈completions A,∑ v∈holes A,if v∈B then (1:ℕ) else 0 := by
      apply sum_congr rfl;intro B hb;rw [sum_boole,row B hb];rfl
    _ = ∑ v∈holes A,∑ B∈completions A,if v∈B then (1:ℕ) else 0 := sum_comm
    _ = _ := by apply sum_congr rfl;intro v _;simpa only [sum_boole,Nat.cast_id] using col v

private theorem flag_count {A:Finset V}
    (one:∀v∈holes A,(completions (insert v A)).card=1) :
    (completions A).card*(24-A.card)=(holes A).card := by
  rw [completion_flags]
  calc
    _ = ∑ _v∈holes A,1 := sum_congr rfl one
    _ = _ := by simp

/-- Every set of size 19 through 24 has one extremal completion. At size 18
there are two exactly when a sixteen-label zero sum is present. -/
theorem completion_count {A:Finset V} (lo:18≤A.card) (hi:A.card≤24) (avoid:¬FlatAt A 0) :
    (completions A).card=if A.card=18 then 1+(sixteens A).card else 1 := by
  classical
  generalize water:24-A.card=k
  induction k using Nat.strong_induction_on generalizing A with
  | h k ih =>
    by_cases top:A.card=24
    · have eq:completions A={A} := by
        ext B;simp only [completions,mem_filter,mem_univ,true_and,mem_singleton]
        constructor
        · rintro ⟨sub,sz,_⟩
          exact (eq_of_subset_of_card_le sub (by omega)).symm
        · rintro rfl;exact ⟨Subset.rfl,top,avoid⟩
      simp [eq,top]
    · have bound:A.card≤23:=by omega
      have counts:=extension_counts lo bound avoid
      have flags:=flag_count (A:=A) (by
        intro v hv
        obtain ⟨fresh,good⟩:=(mem_filter.mp hv).2
        have next:=card_insert_of_notMem fresh
        have r:=ih (24-(insert v A).card) (by omega) (A:=insert v A) (by omega) (by omega) good rfl
        simpa only [if_neg (by omega : (insert v A).card≠18)] using r)
      by_cases small:A.card=18
      · rw [if_pos small]
        rw [counts.1,if_pos small,small] at flags
        omega
      · rw [if_neg small]
        rw [counts.1,if_neg small] at flags
        have pos:0<24-A.card:=by omega
        exact Nat.eq_of_mul_eq_mul_right pos (flags.trans (one_mul _).symm)

/-- The extremal completion is unique as a literal set of labels. -/
theorem unique_completion {A:Finset V} (lo:19≤A.card) (hi:A.card≤24) (avoid:¬FlatAt A 0) :
    ∃!B:Finset V,A⊆B ∧ B.card=24 ∧ ¬FlatAt B 0 := by
  classical
  have count:=completion_count (by omega : 18≤A.card) hi avoid
  rw [if_neg (by omega : A.card≠18)] at count
  obtain ⟨B,h⟩:=card_eq_one.mp count
  have spec (X:Finset V) : (A⊆X ∧ X.card=24 ∧ ¬FlatAt X 0) ↔ X=B := by
    have eq : X∈completions A ↔ X=B := by rw [h,mem_singleton]
    simpa only [completions,mem_filter,mem_univ,true_and] using eq
  exact ⟨B,(spec B).mpr rfl,fun X hx=>(spec X).mp hx⟩

end Green51ShortenedCompletions
#print axioms Green51ShortenedCompletions.extension_counts
#print axioms Green51ShortenedCompletions.completion_count
#print axioms Green51ShortenedCompletions.unique_completion

#print axioms Green51ShortenedCompletions.sixteen_count
#print axioms Green51ShortenedCompletions.completion_flags
