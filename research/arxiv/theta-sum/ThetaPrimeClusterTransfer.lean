import ThetaShortPrimeInterval

/-! Deleting the intervals meeting a theta exception before counting prime clusters. -/
namespace Arxiv.«2501.03234».ThetaPrimeClusterTransfer
open Finset Real Filter ThetaStrongDeviation ThetaStrongOriginalTail
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Bases in (X,X+H] whose next D+1 integers contain a prime at which
the theta sum departs from its main term by at least ε p log p. -/
def contaminated (ε : ℝ) (X H D : ℕ) : Finset ℕ :=
  (Ioc X (X+H)).filter (fun n => ∃ d≤D,(n+d).Prime ∧
    ε*((n+d:ℕ):ℝ)*log (n+d:ℕ)≤|(S (n+d):ℝ)-(n+d:ℕ)*log (n+d:ℕ)/2|)

/-- One exceptional prime rules out at most D+1 bases. -/
theorem count (ε : ℝ) (X H D : ℕ) : (contaminated ε X H D).card ≤
    (D+1)*(ThetaShortPrimeInterval.primes X (H+D) (fun p =>
      ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card := by
  classical
  let E := ThetaShortPrimeInterval.primes X (H+D) (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)
  let U := (range (D+1)).biUnion (fun d => E.image (fun p => p-d))
  have hh : contaminated ε X H D⊆U := by
    intro n hn
    obtain ⟨hn, d,hd,hp,he⟩ := mem_filter.mp hn
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hn
    have hm : n+d∈E := by
      apply mem_filter.mpr
      exact ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,hp,he⟩
    exact mem_biUnion.mpr ⟨d,mem_range.mpr (by omega),mem_image.mpr ⟨n+d,hm,by omega⟩⟩
  have hU : U.card≤∑ d∈range (D+1),(E.image (fun p => p-d)).card := card_biUnion_le
  exact ((card_le_card hh).trans hU).trans ((sum_le_sum (fun _ _ => card_image_le)).trans_eq (by simp [E]))

/-- The exact interval bound transfers to the bases of any fixed bounded pattern. -/
theorem two_terms {ε : ℝ} (hε : 0<ε) (D : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
    D≤H → H+D≤X → ((contaminated ε X H D).card:ℝ)≤
      (D+1:ℕ)*((2*(H:ℝ)/log X)*exp (-rate X/1536)) + C*(X:ℝ)^(3/4:ℝ)*(1+log X)^8 := by
  obtain ⟨C,hC,hx⟩ := ThetaShortPrimeInterval.exceptional hε
  have hd : 0<((D+1:ℕ):ℝ) := by positivity
  refine ⟨(D+1:ℕ)*C,by positivity,?_⟩
  filter_upwards [hx,eventually_ge_atTop 1] with X hb hX
  intro H hD hHX
  have h := (Nat.cast_le (α:=ℝ)).mpr (count ε X H D)
  rw [Nat.cast_mul] at h
  apply (h.trans (mul_le_mul_of_nonneg_left (hb (H+D) hHX) hd.le)).trans
  have hh : ((H+D:ℕ):ℝ)≤2*(H:ℝ) := by exact_mod_cast (by omega : H+D≤2*H)
  have hlog := log_nonneg (by exact_mod_cast hX : 1≤(X:ℝ))
  have he := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh hlog) (exp_pos (-rate X/1536)).le
  exact (mul_le_mul_of_nonneg_left (add_le_add_left he _) hd.le).trans_eq (by ring)

/-- A positive proportion of H/(1+log X)^k witnesses survives whenever the
initial sieve estimate has that many witnesses and the interval is long enough. -/
theorem negligible {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (k D : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, D≤H → H+D≤X →
    K*(X:ℝ)^(3/4:ℝ)*(1+log X)^(8+k)≤H →
    ((contaminated ε X H D).card:ℝ)≤δ*H/(1+log X)^k := by
  obtain ⟨C,hC,hh⟩ := two_terms hε D
  let d := ((D+1:ℕ):ℝ)
  have hd : 0<d := by dsimp [d];positivity
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  refine ⟨2*C/δ,by positivity,?_⟩
  filter_upwards [hh,hlog.eventually_ge_atTop 1,
    absorb_log_power (by positivity : 0<4*d/δ) (by norm_num : (0:ℝ)<1536) k] with X hb hL habs
  intro H hDH hHX hsize
  change 1≤log (X:ℝ) at hL
  let V := 1+log (X:ℝ)
  let W := (X:ℝ)^(3/4:ℝ)
  let F := exp (rate X/1536)
  have hv : 0<V := by dsimp [V];linarith
  have hf : 0<F := exp_pos _
  have hxp : 0<log (X:ℝ) := by linarith
  have hmain : 4*d*V^k ≤ δ*F := by
    rw [mul_comm δ F]
    apply (div_le_iff₀ hδ).mp
    simpa only [div_mul_eq_mul_div] using habs
  have hfirst : d*(2*(H:ℝ)/log X)*exp (-rate X/1536)*V^k ≤ δ*H/2 := by
    rw [show -rate X/1536= -(rate X/1536) by ring,exp_neg]
    change _*F⁻¹*_≤_
    have he : d*2*(H:ℝ)*F⁻¹*V^k≤δ*H/2 := by
      have he' := mul_le_mul_of_nonneg_right hmain (Nat.cast_nonneg H (α:=ℝ))
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      field_simp [hf.ne']
      nlinarith only [he']
    have hx := div_le_self (by positivity : 0≤2*(H:ℝ)) hL
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hd.le)
      (inv_nonneg.mpr hf.le)) (pow_nonneg hv.le k)).trans (by linarith only [he])
  have hsecond : C*W*V^8*V^k ≤ δ*H/2 := by
    change (2*C/δ)*W*V^(8+k)≤(H:ℝ) at hsize
    rw [pow_add,div_mul_eq_mul_div,div_mul_eq_mul_div,div_le_iff₀ hδ] at hsize
    linarith only [hsize]
  apply (le_div_iff₀ (pow_pos hv k)).mpr
  have h := mul_le_mul_of_nonneg_right (hb H hDH hHX) (pow_nonneg hv.le k)
  change _ ≤ (d*(2*(H:ℝ)/log X*exp (-rate X/1536))+C*W*V^8)*V^k at h
  linarith only [h,hfirst,hsecond]

/-- At least m primes in the next D+1 integers are one modulo eight. -/
def classCluster (m D n : ℕ) : Prop :=
  m≤((Icc n (n+D)).filter (fun p => p.Prime ∧ p%8=1)).card

/-- Good clusters retain every prime in the interval at the specified precision. -/
def goodCluster (ε : ℝ) (m D n : ℕ) : Prop :=
  classCluster m D n ∧ ∀ p∈Icc n (n+D),p.Prime →
    |(S p:ℝ)-p*log p/2|<ε*p*log p

theorem lost_where (ε : ℝ) (m D X H : ℕ) (P : ℕ → Prop) :
    ((Ioc X (X+H)).filter (fun n => classCluster m D n ∧ P n)).card ≤
    ((Ioc X (X+H)).filter (fun n => goodCluster ε m D n ∧ P n)).card+(contaminated ε X H D).card := by
  let B := (Ioc X (X+H)).filter (fun n => classCluster m D n ∧ P n)
  let G := (Ioc X (X+H)).filter (fun n => goodCluster ε m D n ∧ P n)
  have hsub : B⊆G ∪ contaminated ε X H D := by
    intro n hn
    obtain ⟨hi,hcl,hP⟩ := mem_filter.mp hn
    by_cases hg : goodCluster ε m D n
    · exact mem_union_left _ (mem_filter.mpr ⟨hi,hg,hP⟩)
    · apply mem_union_right _
      have he : ¬∀ p∈Icc n (n+D),p.Prime → |(S p:ℝ)-p*log p/2|<ε*p*log p :=
        fun hall => hg ⟨hcl,hall⟩
      push Not at he
      obtain ⟨p,hp,hpr,he⟩ := he
      obtain ⟨hlo,hhi⟩ := mem_Icc.mp hp
      apply mem_filter.mpr
      refine ⟨hi,p-n,by omega,?_⟩
      simpa only [Nat.add_sub_of_le hlo] using And.intro hpr he
  exact (card_le_card hsub).trans (card_union_le ..)

theorem lost (ε : ℝ) (m D X H : ℕ) :
    ((Ioc X (X+H)).filter (classCluster m D)).card ≤
    ((Ioc X (X+H)).filter (goodCluster ε m D)).card+(contaminated ε X H D).card := by
  simpa only [and_true] using lost_where ε m D X H (fun _ => True)

theorem transfer {ε α : ℝ} (hε : 0<ε) (hα : 0<α) (m D k : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, D≤H → H+D≤X →
    K*(X:ℝ)^(3/4:ℝ)*(1+log X)^(8+k)≤H →
    α*H/(1+log X)^k ≤ (((Ioc X (X+H)).filter (classCluster m D)).card:ℝ) →
    (α/2)*H/(1+log X)^k ≤ (((Ioc X (X+H)).filter (goodCluster ε m D)).card:ℝ) := by
  obtain ⟨K,hK,hh⟩ := negligible hε (half_pos hα) k D
  refine ⟨K,hK,?_⟩
  filter_upwards [hh] with X hb
  intro H hD hHX hsize hcnt
  let B := (Ioc X (X+H)).filter (classCluster m D)
  let G := (Ioc X (X+H)).filter (goodCluster ε m D)
  have hn := (Nat.cast_le (α:=ℝ)).mpr (lost ε m D X H)
  rw [Nat.cast_add] at hn
  change _≤(B.card:ℝ) at hcnt
  change _≤(G.card:ℝ)
  have he : α*(H:ℝ)/(1+log X)^k=2*((α/2)*H/(1+log X)^k) := by ring
  rw [he] at hcnt
  linarith only [hn,hcnt,hb H hD hHX hsize]

#print axioms lost
#print axioms negligible
#print axioms transfer
#print axioms count
#print axioms two_terms
end
end Arxiv.«2501.03234».ThetaPrimeClusterTransfer
