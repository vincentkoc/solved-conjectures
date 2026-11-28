import Erdos478RelativeGapPairs
import Mathlib.Algebra.BigOperators.Associated

/-! # Joint orbits on ordered pairs of roots at distinct prime gap lengths -/

namespace Erdos478.BinaryGap
open Polynomial Finset Equiv
noncomputable section
variable (K : Type*) [Field K] [Algebra ℚ K] [Normal ℚ K]

omit [Normal ℚ K] in
theorem gap_card {l : ℕ} (hl : l.Prime)
    (hs : ((rationalGap l).map (algebraMap ℚ K)).Splits) :
    Fintype.card ((rationalGap l).rootSet K) = l := by
  have irr : Irreducible (rationalGap l) := GapFamilies.irreducible_gap_rat hl.pos
  rw [card_rootSet_eq_natDegree irr.separable hs]
  change (descPochhammer ℚ l-1).natDegree=l
  rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa [descPochhammer_natDegree] using hl.pos),
    descPochhammer_natDegree]

/-- Fixing every root at the smaller lengths leaves full freedom at the
new pair. Equal entries must be matched with equal entries. -/
theorem pair_fixing_smaller {l : ℕ} (hl : l.Prime) (h : broad l) (h₃ : 3<l)
    [Fact (((rationalGap l).map (algebraMap ℚ K)).Splits)] (s : Finset ℕ)
    (small : ∀ t∈s, t<l)
    (split : ∀ t∈s, t.Prime ∧ ((rationalGap t).map (algebraMap ℚ K)).Splits)
    {a b c d : (rationalGap l).rootSet K} (pattern : a=b ↔ c=d) :
    ∃ σ : K ≃ₐ[ℚ] K, σ (a:K)=c ∧ σ (b:K)=d ∧
      ∀ t∈s, ∀ x : (rationalGap t).rootSet K, σ (x:K)=x := by
  classical
  let R (j : s) := (rationalGap j.val).rootSet K
  let B := (j : s) → Perm (R j)
  let (j : s) : Fact (((rationalGap j.val).map (algebraMap ℚ K)).Splits) := ⟨(split j j.prop).2⟩
  let act (j : s) := (Gal.galActionHom (rationalGap j.val) K).comp (Gal.restrict (rationalGap j.val) K)
  let φ : (K ≃ₐ[ℚ] K) →* B := MonoidHom.pi act
  have hB : ¬l ∣ Nat.card B := by
    rw [Nat.card_pi]
    apply hl.prime.not_dvd_finsetProd
    intro j _
    rw [Nat.card_perm,Nat.card_eq_fintype_card,gap_card K (split j j.prop).1 (split j j.prop).2,
      hl.dvd_factorial]
    exact (small j j.prop).not_ge
  have lift : ∃ σ : K ≃ₐ[ℚ] K, φ σ=1 ∧ σ (a:K)=c ∧ σ (b:K)=d := by
    by_cases hab : a=b
    · obtain rfl := hab
      obtain rfl := pattern.mp rfl
      have hn := gap_card K hl (Fact.out : ((rationalGap l).map (algebraMap ℚ K)).Splits)
      let : Nontrivial ((rationalGap l).rootSet K) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨v,hv⟩ := exists_ne a
      obtain ⟨w,hw⟩ := exists_ne c
      obtain ⟨σ,hσ,ha,_⟩ := relative_gap_pair hl h h₃ K φ hB hv.symm hw.symm
      exact ⟨σ,hσ,ha,ha⟩
    · exact relative_gap_pair hl h h₃ K φ hB hab (fun hcd => hab (pattern.mpr hcd))
  obtain ⟨σ,hσ,ha,hb⟩ := lift
  refine ⟨σ,ha,hb,?_⟩
  intro t ht x
  let j : s := ⟨t,ht⟩
  have he := congrArg (fun z : B => ((z j) x : K)) hσ
  exact (Gal.galActionHom_restrict (rationalGap j.val) K σ x).symm.trans he

/-- The equality pattern for each length is the sole invariant of a tuple
containing two roots per length. There is no restriction on how many
distinct lengths occur. -/
theorem joint_gap_pairs (s : Finset ℕ) (a b c d : ℕ → K)
    (good : ∀ l∈s, l.Prime ∧ broad l ∧ 3<l ∧ ((rationalGap l).map (algebraMap ℚ K)).Splits)
    (roots : ∀ l∈s, a l∈(rationalGap l).rootSet K ∧ b l∈(rationalGap l).rootSet K ∧
      c l∈(rationalGap l).rootSet K ∧ d l∈(rationalGap l).rootSet K ∧ (a l=b l ↔ c l=d l)) :
    ∃ σ : K ≃ₐ[ℚ] K, ∀ l∈s, σ (a l)=c l ∧ σ (b l)=d l := by
  classical
  induction s using Finset.induction_on_max with
  | empty => exact ⟨1,by simp⟩
  | insert l s small ih =>
    have old (t : ℕ) (ht : t∈s) : t∈insert l s := mem_insert_of_mem ht
    obtain ⟨τ,hτ⟩ := ih (fun t ht => good t (old t ht)) (fun t ht => roots t (old t ht))
    obtain ⟨hl,hb,h₃,hs⟩ := good l (mem_insert_self ..)
    obtain ⟨ha₁,ha₂,hc₁,hc₂,he⟩ := roots l (mem_insert_self ..)
    let : Fact (((rationalGap l).map (algebraMap ℚ K)).Splits) := ⟨hs⟩
    let x : (rationalGap l).rootSet K := ⟨τ (a l),rootSet_mapsTo τ.toAlgHom ha₁⟩
    let y : (rationalGap l).rootSet K := ⟨τ (b l),rootSet_mapsTo τ.toAlgHom ha₂⟩
    let u : (rationalGap l).rootSet K := ⟨c l,hc₁⟩
    let v : (rationalGap l).rootSet K := ⟨d l,hc₂⟩
    have eq : x=y ↔ u=v := by simpa [x,y,u,v,Subtype.ext_iff] using he
    obtain ⟨σ,hx,hy,fixes⟩ := pair_fixing_smaller K hl hb h₃ s small
      (fun t ht => ⟨(good t (old t ht)).1,(good t (old t ht)).2.2.2⟩) eq
    refine ⟨τ.trans σ,?_⟩
    intro t ht
    rcases mem_insert.mp ht with rfl|ht
    · exact ⟨hx,hy⟩
    · obtain ⟨h₁,h₂⟩ := hτ t ht
      change σ (τ (a t))=c t ∧ σ (τ (b t))=d t
      rw [h₁,h₂]
      exact ⟨fixes t ht ⟨_,(roots t (old t ht)).2.2.1⟩,
        fixes t ht ⟨_,(roots t (old t ht)).2.2.2.1⟩⟩

#print axioms gap_card
#print axioms pair_fixing_smaller
#print axioms joint_gap_pairs
end
end Erdos478.BinaryGap
