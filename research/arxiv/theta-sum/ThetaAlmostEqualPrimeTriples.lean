import ThetaTernaryTransfer

/-! Retain almost all ordinary three-prime representations, and extract
vertex-disjoint representations with prescribed theta accuracy. -/
namespace Arxiv.«2501.03234».ThetaAlmostEqualPrimeTriples
open Filter Finset Real ThetaTernaryErrorBudget ThetaTernaryWindows
open ThetaTernaryDeletion ThetaTernaryPacking ThetaTernaryTransfer
noncomputable section

/-- An ordinary lower bound for ordered representations of odd integers by
three primes within n^θ of n/3. There is no theta condition in this input. -/
def Ordinary (θ : ℝ) (m : ℕ) (b : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, Odd n → b*((n:ℝ)^θ)^2 ≤
    ((triples (window n θ) (window n θ) (window n θ) n).card:ℝ)*(width n)^m

theorem retain {θ ε η b : ℝ} {m : ℕ} (control : Control θ)
    (hε : 0<ε) (hη : 0<η) (hb : 0<b) (ho : Ordinary θ m b) :
    ∀ᶠ n : ℕ in atTop, Odd n →
      (1-η)*((triples (window n θ) (window n θ) (window n θ) n).card:ℝ) ≤
        (distinctTriples (selected n θ ε) n).card := by
  filter_upwards [ho,original control hε (mul_pos hη hb) m,
    control hε hb m] with n hn herr hs hodd
  have hv := pow_pos hs.1.1 m
  have hc := mul_le_mul_of_nonneg_left (hn hodd) hη.le
  have he : (η*b)*((n:ℝ)^θ)^2/(width n)^m ≤
      η*(triples (window n θ) (window n θ) (window n θ) n).card := by
    apply (div_le_iff₀ hv).mpr
    linarith only [hc]
  linarith only [herr n,he]

/-- Disjointness holds inside each ordered triple and between all chosen
triples. The scale is explicit in the ordinary input b and m. -/
theorem disjoint_representations {θ ε b : ℝ} {m : ℕ} (control : Control θ)
    (hε : 0<ε) (hb : 0<b) (ho : Ordinary θ m b) :
    ∀ᶠ n : ℕ in atTop, Odd n →
      ∃ D ⊆ distinctTriples (selected n θ ε) n,
        D.card=⌊b*(n:ℝ)^θ/(500*(width n)^m)⌋₊ ∧
        ∀ t∈D,∀ u∈D,t≠u → Disjoint (vertices t) (vertices u) := by
  filter_upwards [ho,control hε (show 0<b/100 by positivity) m] with n hn hs hodd
  let A := window n θ
  let E := errors n θ ε
  let V := (width n)^m
  let R := (n:ℝ)^θ
  let k := ⌊b*R/(500*V)⌋₊
  have hV : 0<V := pow_pos hs.1.1 m
  have hR : 0<R := hs.1.2
  have hk : (k:ℝ)*(500*V)≤b*R := (le_div_iff₀ (by positivity)).mp
    (Nat.floor_le (show 0≤b*R/(500*V) by positivity))
  have hE : ((E.card:ℝ)+1)*V≤b/100*R := hs.2.2
  have hA : (A.card:ℝ)≤8*R := hs.2.1
  have hsum : ((E.card:ℝ)+3*k+1)*V≤b/50*R := by linarith only [hk,hE,mul_pos hb hR]
  have hprod := mul_le_mul hsum hA (Nat.cast_nonneg _) (by positivity)
  have hsmall : 3*((E.card:ℝ)+3*k+1)*A.card*V<b*R^2 := by
    nlinarith only [hprod,mul_pos hb (sq_pos_of_pos hR)]
  have hlt : 3*((E.card:ℝ)+3*k+1)*A.card < (triples A A A n).card :=
    (mul_lt_mul_iff_left₀ hV).mp (hsmall.trans_le (hn hodd))
  apply pack A n k E
  exact_mod_cast hlt

#print axioms retain
#print axioms disjoint_representations
end
end Arxiv.«2501.03234».ThetaAlmostEqualPrimeTriples
