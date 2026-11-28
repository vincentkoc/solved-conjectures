import ThetaRowDissection
import ThetaBandExponentialBounds
import ThetaBandProjectionBudget

/-! Simultaneous control of the full model on a finite interval by summing exceptional counts. -/
namespace Arxiv.«2501.03234».ThetaMultiscaleRows
open Finset Filter Real ThetaSmoothConditionalModel ThetaRowDissection ThetaDenominatorBandScales
open ThetaBandExponentialBounds ThetaCenteredWindow ThetaOrbitProjection
open scoped Classical
noncomputable section

def boundary (i : ℕ) := (2^(scale i))^2
def start (h : ℕ) := size (first h)
def block (h i : ℕ) (W : Window) := after (boundary i) (after (start h) W)
def bad (h q Y X : ℕ) (W : Window) :=
  (range X).filter (fun n => 1 ≤ |center Y (expose h q) W n|)
def active (h : ℕ) := (range (h+1)).filter (fun i => first h ≤ scale i)
def exceptions (h X : ℕ) (W : Window) := bad h (first h) (start h) X W ∪
  (active h).biUnion (fun i => bad h (scale i) (size (scale i)) X (block h i W))
def error (h X : ℕ) : ℝ := (X:ℝ)*(2*exp ThetaTiltBudget.total)*exp (-saving h)+2*exp (18*scale h)
def level (h : ℕ) : ℝ := (1+envelope*238*(64*((h:ℝ)+1))^2)+2*((h:ℝ)+1)

theorem successor (i : ℕ) : boundary (i+1)=size (scale i) := by
  unfold boundary size scale;rw [←pow_mul,pow_succ];congr 1;ring

theorem monotone_size {x y : ℕ} (h : x ≤ y) : size x ≤ size y :=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 4 h)

private theorem count_bad : ∀ᶠ h : ℕ in atTop,∀ q Y X : ℕ,first h ≤ q → q ≤ scale h → Y ≤ size q →
    ∀ W : Window,((bad h q Y X W).card:ℝ) ≤ error h X := by
  filter_upwards [moment] with h hh q Y X hq ht hy W
  let f := center Y (expose h q) W
  let k := order h q
  let E := bad h q Y X W
  have hm (n : ℕ) (hn : n∈E) : (1:ℝ) ≤ (f n)^(2*k) := by
    rw [←pow_abs_two_mul];exact one_le_pow₀ (mem_filter.mp hn).2
  calc ((E.card:ℕ):ℝ) = ∑ _n∈E,(1:ℝ) := by simp
       _ ≤ ∑ n∈E,(f n)^(2*k) := sum_le_sum hm
       _ ≤ ∑ n∈range X,(f n)^(2*k) := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun n _ _ => by rw [←pow_abs_two_mul];positivity)
       _ ≤ _ := hh q Y hq ht hy W X

theorem count : ∀ᶠ h : ℕ in atTop,∀ (X : ℕ) (W : Window),
    ((exceptions h X W).card:ℝ) ≤ ((h:ℝ)+2)*error h X := by
  filter_upwards [count_bad,first_le] with h H hfirst X W
  have hi (i : ℕ) (hi : i∈active h) : scale i ≤ scale h := Nat.pow_le_pow_right (by decide) (by have := mem_range.mp (mem_filter.mp hi).1;omega)
  have he : (exceptions h X W).card ≤ (bad h (first h) (start h) X W).card+
      ∑ i∈active h,(bad h (scale i) (size (scale i)) X (block h i W)).card :=
    (card_union_le ..).trans (Nat.add_le_add_left card_biUnion_le _)
  have casted : ((exceptions h X W).card:ℝ) ≤ ((bad h (first h) (start h) X W).card:ℝ)+
      ∑ i∈active h,((bad h (scale i) (size (scale i)) X (block h i W)).card:ℝ) := by exact_mod_cast he
  have hb := sum_le_sum (s:=active h) (g:=fun _ : ℕ => error h X) (fun i h' => H (scale i) _ X (mem_filter.mp h').2 (hi i h') le_rfl (block h i W))
  rw [sum_const,nsmul_eq_mul] at hb
  have hc : (active h).card ≤ h+1 := (card_le_card (filter_subset ..)).trans_eq (card_range _)
  have he₀ : 0 ≤ error h X := by unfold error;positivity
  have ht := mul_le_mul_of_nonneg_right (show ((active h).card:ℝ) ≤ (h:ℝ)+1 by exact_mod_cast hc) he₀
  have hlow := H (first h) (start h) X le_rfl hfirst le_rfl W
  linarith only [casted,hlow,hb,ht]

private theorem value {h q Y X n : ℕ} {W : Window} (hn : n < X) (hne : n∉bad h q Y X W) :
    |rowModel Y W n| ≤ 1+|smooth Y (expose h q) (rowModel Y W) n| := by
  have he : |center Y (expose h q) W n| < 1 := lt_of_not_ge (fun hh => hne (mem_filter.mpr ⟨mem_range.mpr hn,hh⟩))
  have ht := abs_add_le (center Y (expose h q) W n) (smooth Y (expose h q) (rowModel Y W) n)
  unfold center at he
  rw [center,sub_add_cancel] at ht;linarith only [ht,he]

theorem outside : ∀ᶠ h : ℕ in atTop,∀ (X n : ℕ) (W : Window),n < X → n∉exceptions h X W →
    |rowModel (size (scale h)) W n| ≤ level h := by
  filter_upwards [first_le,ThetaBandProjectionBudget.high] with h hfirst HH X n W hn he
  have hbase := value hn (show n∉bad h (first h) (start h) X W from fun hh => he (mem_union_left _ hh))
  have size₂ (q : ℕ) (hq : 0 < q) : 2 ≤ size q := by
    apply (show 2=2^1 by decide).le.trans (Nat.pow_le_pow_right (by decide) (show 1 ≤ 4*q by omega))
  have hF : 1 ≤ first h := Nat.mul_pos (by decide : 0 < 65536) (pow_pos (Nat.succ_pos h) 2)
  have low := ThetaBandProjectionBudget.low hfirst (Y:=start h) (size₂ _ hF) W n
  let W' := after (start h) W
  have hsplit := split (monotone_size hfirst) W n
  change rowModel (size (scale h)) W n=rowModel (start h) W n+rowModel (size (scale h)) W' n at hsplit
  have hmono (i : ℕ) : boundary i ≤ boundary (i+1) := by
    unfold boundary;apply Nat.pow_le_pow_left _ _;exact Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  have htel := telescoping boundary hmono W' n (h+1)
  have h₄ : 4 ≤ start h := by
    change 2^2 ≤ 2^(4*first h);exact Nat.pow_le_pow_right (by decide) (by omega)
  have hz : rowModel (boundary 0) W' n=0 := by
    apply zero;intro d hd;change _ ≤ 4 at hd;simp [W',after,ThetaDenominatorTails.above,hd.trans h₄]
  simp only [successor,hz,zero_add] at htel
  rw [hsplit,htel]
  have all (i : ℕ) (hi : i∈range (h+1)) : |rowModel (size (scale i)) (block h i W) n| ≤ 2 := by
    by_cases hq : first h ≤ scale i
    · have hactive : i∈active h := mem_filter.mpr ⟨hi,hq⟩
      have notbad : n∉bad h (scale i) (size (scale i)) X (block h i W) := fun hh => he (mem_union_right _ (mem_biUnion.mpr ⟨i,hactive,hh⟩))
      have hh := HH (scale i) _ hq (Nat.pow_le_pow_right (by decide) (by have := mem_range.mp hi;omega))
        (size₂ (scale i) (by unfold scale;positivity)) (block h i W)
        (fun d hd => by simp [block,after,ThetaDenominatorTails.above,show d ≤ boundary i from hd]) n
      linarith only [value hn notbad,hh]
    · rw [zero _ n,abs_zero];norm_num
      intro d hd
      have hl := hd.trans (monotone_size (le_of_not_ge hq))
      simp [block,after,ThetaDenominatorTails.above,show d ≤ start h from hl]
  apply (abs_add_le ..).trans
  have hsum := (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum all)
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at hsum
  change _ ≤ 1+envelope*238*(64*((h:ℝ)+1))^2+2*((h:ℝ)+1)
  change |∑ i∈range (h+1),rowModel (size (scale i)) (block h i W) n| ≤ _ at hsum
  change |rowModel (start h) W n|+|∑ i∈range (h+1),rowModel (size (scale i)) (block h i W) n| ≤ _
  linarith only [hbase,low,hsum]

#print axioms count
#print axioms outside
end
end Arxiv.«2501.03234».ThetaMultiscaleRows
