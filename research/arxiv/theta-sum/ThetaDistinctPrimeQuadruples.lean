import ThetaLogarithmicLags

/-! Removing the three overlapping placements of two equal-displacement
prime pairs preserves the fourth-order signed main term. -/
namespace Arxiv.«2501.03234».ThetaDistinctPrimeQuadruples
open Real Filter Finset ThetaPositiveLag ThetaPrimeLagBounds ThetaLogarithmicLags
noncomputable section

def pairs (X h : ℕ) := (Nat.primesLE X).filter (fun p => p+h∈Nat.primesLE X)
def separate (p r h : ℕ) := p≠r ∧ p+h≠r ∧ r+h≠p
instance (p r h : ℕ) : Decidable (separate p r h) := by unfold separate;infer_instance
def four (X h : ℕ) (f : ℕ → ℝ) :=
  ∑ p∈pairs X h,∑ r∈(pairs X h).filter (fun r => separate p r h), (f p*f (p+h))*(f r*f (r+h))

theorem finite (X h : ℕ) {f : ℕ → ℝ} {B : ℝ} (hB : 0≤B) (hf : ∀ p∈Nat.primesLE X,|f p|≤B) :
    (corr X h f)^2≤four X h f+3*(X+1)*B^4 := by
  classical
  let S := pairs X h
  let u (p : ℕ) := f p*f (p+h)
  have hu (p : ℕ) (hp : p∈S) : |u p|≤B^2 := by
    obtain ⟨ha,hb⟩ := mem_filter.mp hp
    simpa only [u,abs_mul,sq] using mul_le_mul (hf p ha) (hf _ hb) (abs_nonneg _) hB
  have bound (p : ℕ) (hp : p∈S) :
      (∑ r∈S,u p*u r)≤(∑ r∈S.filter (fun r => separate p r h),u p*u r)+3*B^4 := by
    let T := S.filter (fun r => ¬separate p r h)
    have ht : T⊆{p,p+h,p-h} := by
      intro r hr;obtain ⟨_,hh⟩ := mem_filter.mp hr
      simp only [separate,not_and_or,not_not] at hh
      simp only [mem_insert,mem_singleton];omega
    have hc : T.card≤3 := (card_le_card ht).trans (by
      calc _ ≤ ({p+h,p-h}:Finset ℕ).card+1 := card_insert_le ..
           _ ≤ (({p-h}:Finset ℕ).card+1)+1 := Nat.add_le_add_right (card_insert_le ..) _
           _ = 3 := by simp)
    rw [←sum_filter_add_sum_filter_not S (fun r => separate p r h)]
    apply add_le_add_right
    have he := sum_le_sum (s:=T) (g:=fun _ => B^4) (fun r hr =>
      (le_abs_self (u p*u r)).trans (by
        rw [abs_mul,show B^4=B^2*B^2 by ring]
        exact mul_le_mul (hu p hp) (hu r (mem_filter.mp hr).1) (abs_nonneg _) (sq_nonneg B)))
    simp only [sum_const,nsmul_eq_mul] at he
    exact he.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity))
  have he := sum_le_sum bound
  have hex : (∑ p∈S,u p)^2=∑ p∈S,∑ r∈S,u p*u r := by
    rw [sq,sum_mul];simp_rw [mul_sum]
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul] at he
  rw [←hex] at he
  have hc : S.card≤X+1 := (card_le_card (show S⊆range (X+1) from fun p hp =>
    mem_range.mpr (Nat.lt_succ_of_le (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1))).trans (by simp)
  change (∑ p∈S,u p)^2≤(∑ p∈S,∑ r∈S.filter (fun r => separate p r h),u p*u r)+_
  apply le_trans he
  have hc' : (S.card:ℝ)≤(X:ℝ)+1 := by exact_mod_cast hc
  nlinarith only [mul_le_mul_of_nonneg_right hc' (show 0≤3*B^4 by positivity)]

def Controlled (f : ℕ → ℝ) := ∃ B : ℝ,0<B ∧ ∃ k : ℕ,∀ᶠ X : ℕ in atTop,
  ∀ p∈Nat.primesLE X,|f p|≤B*(log X)^k

theorem energy {q : ℕ} (hq : 0<q) {c : ℝ} (hc : 0<c) {f : ℕ → ℝ}
    (hs : Scales q c f) (hf : Controlled f) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ X : ℕ in atTop,∀ L : ℕ,K*log X≤L → q*L≤X →
      c^2/2*(X:ℝ)^2*L≤(∑ k∈offsets L,four X (q*k) f)*(log X)^4 := by
  obtain ⟨K,hK,H⟩ := summary hq hc hs
  obtain ⟨B,hB,k,hf⟩ := hf
  have he := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (ThetaLocalExcursionScales.logs (by norm_num : (0:ℝ)<1) (by positivity : 0<12*B^4/c^2) (k*4+4))
  refine ⟨K,hK,?_⟩
  filter_upwards [H,hf,he,eventually_ge_atTop (2:ℕ)] with X hx hF he hX
  intro L hl hh
  have hpos : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hlog := (log_pos (show (1:ℝ)<X by exact_mod_cast hX)).le
  change 12*B^4/c^2*(log X)^(k*4+4)≤(X:ℝ)^1 at he
  rw [rpow_one,div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<c^2),pow_add,pow_mul] at he
  have hmain := (hx L hl hh).2
  have hsum := sum_le_sum (s:=offsets L) (fun d _ => finite X (q*d) (mul_nonneg hB.le (pow_nonneg hlog k)) hF)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_pow] at hsum
  have hcard : (offsets L).card≤L := (card_le_card (erase_subset ..)).trans (by simp)
  have hXX : (X:ℝ)+1≤2*X := by
    have : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
    linarith
  have hbudget : ((offsets L).card:ℝ)*(3*(X+1)*(B^4*(log X^k)^4))≤
      L*(6*X*(B^4*(log X^k)^4)) := by
    apply mul_le_mul (Nat.cast_le.mpr hcard) _ (by positivity) (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith only [hXX]) (by positivity)
  nlinarith only [hmain,mul_le_mul_of_nonneg_right hsum (sq_nonneg ((log X)^2)),
    mul_le_mul_of_nonneg_right hbudget (show 0≤(log X)^4 by positivity),
    mul_le_mul_of_nonneg_right he (show 0≤(X:ℝ)*L by positivity)]

#print axioms finite
#print axioms energy
end
end Arxiv.«2501.03234».ThetaDistinctPrimeQuadruples
