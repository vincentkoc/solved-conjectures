import Erdos478ConditionalFixedHits
import Erdos478GaloisObservables
import Erdos478JointGapRootOrbits
import Erdos478GapVariance

/-! # Conditioning the next prime gap on all smaller root counts -/

namespace Erdos478.ConditionalGaps
open Finset Polynomial MulAction FrobeniusCounts BinaryGap GapVariance
noncomputable section
variable (K : Type*) [Field K] [Algebra ℚ K]

abbrev Roots (l : Nat.Primes) := (rationalGap l.val).rootSet K
def count (l : Nat.Primes) (g : Aut K) := fixedCount (Roots K l) g

theorem count_eq (l : Nat.Primes) (g : Aut K) : count K l g=fixed K (gap l.val) g := by
  have he : (gap l.val).map (Int.castRingHom ℚ)=rationalGap l.val := by simp [gap,rationalGap]
  unfold count fixed rootType Roots
  rw [he]

/-- Automorphisms that fix each earlier root individually. -/
def kernel (s : Finset Nat.Primes) : Subgroup (Aut K) where
  carrier := {g | ∀ l∈s, ∀ x : Roots K l, g (x:K)=x}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := by
    intro g h hg hh i hi x
    change g (h (x:K))=x
    rw [hh i hi x,hg i hi x]
  inv_mem' := by
    intro g hg i hi x
    apply g.injective
    exact (g.apply_symm_apply _).trans (hg i hi x).symm

theorem count_stable {s : Finset Nat.Primes} (n : kernel K s) (g : Aut K)
    {i : Nat.Primes} (hi : i∈s) : count K i (n.val*g)=count K i g := by
  have h (x : Roots K i) : (n.val*g) • x=g • x := by
    apply Subtype.ext
    exact n.prop i hi (g • x)
  have eq : fixedBy (Roots K i) (n.val*g)=fixedBy (Roots K i) g :=
    Set.ext fun x => by simp only [mem_fixedBy,h]
  unfold count fixedCount
  rw [eq]

variable [Normal ℚ K]

/-- The subgroup fixing every earlier root is transitive on the diagonal
and on ordered distinct pairs of new roots. The smaller primes are arbitrary. -/
theorem kernel_pairs (s : Finset Nat.Primes) (l : Nat.Primes) (hb : broad l.val) (h3 : 3<l.val)
    (small : ∀ i∈s, i.val<l.val) (split : ∀ i∈insert l s, ((rationalGap i.val).map (algebraMap ℚ K)).Splits)
    (a b c d : Roots K l) (pat : a=b ↔ c=d) :
    ∃ n : kernel K s, n.val • a=c ∧ n.val • b=d := by
  let : Fact (((rationalGap l.val).map (algebraMap ℚ K)).Splits) := ⟨split _ (mem_insert_self ..)⟩
  let old := s.image Subtype.val
  have lt (t : ℕ) (ht : t∈old) : t<l.val := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
    exact small i hi
  have sp (t : ℕ) (ht : t∈old) : t.Prime ∧ ((rationalGap t).map (algebraMap ℚ K)).Splits := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
    exact ⟨i.prop, split _ (mem_insert_of_mem hi)⟩
  obtain ⟨g,ha,hb,fixes⟩ := pair_fixing_smaller K l.prop hb h3 old lt sp pat
  exact ⟨⟨g,fun i hi => fixes i.val (mem_image_of_mem _ hi)⟩,Subtype.ext ha,Subtype.ext hb⟩

variable [FiniteDimensional ℚ K]

theorem gap_conditional_half (s : Finset Nat.Primes) (l : Nat.Primes) (hb : broad l.val) (h3 : 3<l.val)
    (small : ∀ i∈s, i.val<l.val) (split : ∀ i∈insert l s, ((rationalGap i.val).map (algebraMap ℚ K)).Splits)
    (w : Aut K → ℝ) (hn : ∀ g, 0≤w g) (stable : ∀ (n : kernel K s) g, w (n.val*g)=w g) :
    uniform (Aut K) w≤2*uniform (Aut K) (fun g => if 0<count K l g then w g else 0) := by
  classical
  have hc : Fintype.card (Roots K l)=l.val := gap_card K l.prop (split _ (mem_insert_self ..))
  let : Nontrivial (Roots K l) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact conditional_half (kernel K s) (kernel_pairs K s l hb h3 small split) w stable hn

#print axioms Roots
#print axioms count
#print axioms count_eq
#print axioms kernel
#print axioms count_stable
#print axioms kernel_pairs
#print axioms gap_conditional_half
end
end Erdos478.ConditionalGaps
