import Green53ThresholdConcentration

/-! # Counting disjoint sign changes in an affine parity slice -/

open Finset
open scoped Classical
namespace Green53ParityBlocks

/-- In a two-point fibre differing by one heavy sign, at least one weighted
sum has absolute value at least as large as that coefficient. -/
theorem one_large_sign (a b : ℝ) : |a| ≤ |b+a| ∨ |a| ≤ |b-a| := by
  by_contra! h
  have triangle := abs_sub (b+a) (b-a)
  rw [show b+a-(b-a)=2*a by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at triangle
  linarith

/-- If the mean is at least half the block count, a variance bound controls the
fraction of samples with fewer than one quarter of the blocks. -/
theorem few_good {m : ℕ} {Sample : Type*} [Fintype Sample] (score : Sample → ℝ) (μ : ℝ)
    (mean : (m:ℝ)/2 ≤ μ)
    (variance : ∑ x, (score x-μ)^2 ≤ Fintype.card Sample * ((m:ℝ)/4))
    (pos : 0 < m) :
    ((univ.filter (fun x => score x < (m:ℝ)/4)).card:ℝ) * m ≤ 4*Fintype.card Sample := by
  classical
  let bad := univ.filter (fun x => score x < (m:ℝ)/4)
  have lower (x) (hx : x∈bad) : ((m:ℝ)/4)^2 ≤ (score x-μ)^2 := by
    have sm := (mem_filter.mp hx).2
    change score x < (m:ℝ)/4 at sm
    have pos' : (0:ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith [sq_nonneg ((μ-score x)-(m:ℝ)/4),
      mul_nonneg (by linarith : 0 ≤ μ-score x-(m:ℝ)/4) (by linarith : 0 ≤ μ-score x+(m:ℝ)/4)]
  have I : (bad.card:ℝ)*((m:ℝ)/4)^2 ≤ Fintype.card Sample * ((m:ℝ)/4) := calc
    _ = ∑ _x∈bad, ((m:ℝ)/4)^2 := by simp
    _ ≤ ∑ x∈bad, (score x-μ)^2 := sum_le_sum lower
    _ ≤ ∑ x, (score x-μ)^2 := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
    _ ≤ _ := variance
  change (bad.card:ℝ)*(m:ℝ) ≤ _
  have pm : (0:ℝ) < m := by exact_mod_cast pos
  apply (mul_le_mul_iff_left₀ pm).mp
  nlinarith
/-- Sum the diagonal terms of the centered second moment. -/
theorem uncorrelated_variance {I Sample : Type*} [Fintype I] [Fintype Sample]
    (w : I → Sample → ℝ) (μ : I → ℝ)
    (off : ∀ i j, i ≠ j → ∑ x, (w i x-μ i)*(w j x-μ j)=0)
    (diag : ∀ i, ∑ x, (w i x-μ i)^2 ≤ Fintype.card Sample/4) :
    ∑ x, ((∑ i, w i x)-(∑ i, μ i))^2 ≤ Fintype.card Sample*(Fintype.card I/4) := by
  classical
  let f i x := w i x-μ i
  have expand x : ((∑ i, w i x)-(∑ i, μ i))^2 = ∑ i,∑ j, f i x*f j x := by
    rw [←sum_sub_distrib, pow_two, sum_mul_sum]
  have inner (i : I) : (∑ j,∑ x, f i x*f j x)=∑ x,(w i x-μ i)^2 := by
    rw [sum_eq_single i]
    · simp [f,pow_two]
    · intro j _ ne
      exact off i j ne.symm
    · simp
  calc
    _ = ∑ x, ∑ i, ∑ j, f i x*f j x := sum_congr rfl (fun x _ => expand x)
    _ = ∑ i, ∑ j, ∑ x, f i x*f j x := by
      rw [sum_comm]; exact sum_congr rfl (fun _ _ => sum_comm)
    _ = ∑ i, ∑ x,(w i x-μ i)^2 := sum_congr rfl (fun i _ => inner i)
    _ ≤ ∑ _i : I, (Fintype.card Sample:ℝ)/4 := sum_le_sum (fun i _ => diag i)
    _ = _ := by simp; ring


/-- Fewer than one quarter of the preferred coins match on at most a 4/m fraction
of the cube. The preferred signs can be chosen separately for every application. -/
theorem match_tail {m : ℕ} (pref : Fin m → Bool) (hm : 0 < m) :
    (univ.filter (fun x : Fin m → Bool =>
      4*(univ.filter (fun i => x i=pref i)).card < m)).card*m ≤ 4*2^m := by
  classical
  let w (i : Fin m) (x : Fin m → Bool) : ℝ := if x i=pref i then 1 else 0
  let μ (_ : Fin m) : ℝ := 1/2
  have diag i : ∑ x, (w i x-μ i)^2 ≤ Fintype.card (Fin m → Bool)/4 := by
    have eq (x) : (w i x-μ i)^2=(1/4:ℝ) := by by_cases h : x i=pref i <;> norm_num [w,μ,h]
    simp_rw [eq]
    simp; ring_nf; rfl
  have off (i j : Fin m) (ij : i≠j) :
      ∑ x, (w i x-μ i)*(w j x-μ j)=0 := by
    let e := Equiv.piCongrRight (fun k : Fin m => if k=i then Equiv.boolNot else Equiv.refl Bool)
    let f (x : Fin m → Bool) : ℝ := (w i x-μ i)*(w j x-μ j)
    have neg (x : Fin m → Bool) : f (e x) = -f x := by
      have hi : e x i = !(x i) := by simp [e,Equiv.piCongrRight_apply,Equiv.boolNot]
      have hj : e x j = x j := by simp [e,Equiv.piCongrRight_apply,ij.symm]
      dsimp only [f,w,μ]
      rw [hi,hj]
      cases h : x i <;> cases g : pref i <;> by_cases b : x j=pref j <;> norm_num [b]
    have bij := Equiv.sum_comp e f
    simp_rw [neg, sum_neg_distrib] at bij
    change ∑ x, f x=0
    linarith
  have variance := uncorrelated_variance w μ off diag
  have mu : ∑ i, μ i=(m:ℝ)/2 := by simp [μ]; ring
  rw [mu] at variance
  have tail := few_good (m:=m) (fun x => ∑ i, w i x) ((m:ℝ)/2) le_rfl (by simpa using variance) hm
  have score (x : Fin m → Bool) : (∑ i, w i x : ℝ) = (univ.filter (fun i => x i=pref i)).card := by
    simp only [w,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have eq (x : Fin m → Bool) : ((∑ i, w i x)<(m:ℝ)/4) ↔
      4*(univ.filter (fun i => x i=pref i)).card < m := by
    rw [score,lt_div_iff₀ (by norm_num)]
    rw [mul_comm]; exact_mod_cast Iff.rfl
  simp_rw [eq] at tail
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at tail
  exact_mod_cast tail

open Green53Threshold in
/-- A separate sign in each coefficient prevents the dependent bits from
concentrating the whole two-sign sum in one short interval. -/
theorem two_sign_window {m r c : ℕ} (hr : 0 < r)
    (size : m=8*(4*r*(c+1))^2) (offset : (Fin m → Bool) → ℝ)
    (B C : Fin m → ℝ) {δ : ℝ} (pos : 0 < δ) (large : ∀ i, δ ≤ |C i|) :
    2*r*(∑ x : Fin m → Bool, (univ.filter (fun y : Fin m → Bool =>
      |offset x+∑ i, (B i+C i*signBit (x i))*signBit (y i)| ≤ c*δ)).card) ≤ 2^m*2^m := by
  classical
  let u := 4*r*(c+1)
  let g := 2*u^2
  have mg : m=4*g := by dsimp [g,u]; rw [size]; ring
  have small : 16*r ≤ m := by
    have ru : r ≤ u := by dsimp [u]; nlinarith
    have pu : 0 < u := lt_of_lt_of_le hr ru
    dsimp only [g] at mg
    have ru' : 4*r ≤ u := by dsimp [u]; nlinarith
    nlinarith [Nat.mul_le_mul_left u (show 1≤u by omega)]
  have mp : 0 < m := by omega
  have pick (i) : ∃ bit : Bool, δ ≤ |B i+C i*signBit bit| := by
    rcases one_large_sign (C i) (B i) with h|h
    · exact ⟨true,by simpa [signBit] using (large i).trans h⟩
    · exact ⟨false,by simpa [signBit,sub_eq_add_neg] using (large i).trans h⟩
  choose pref good using pick
  let aligned (x : Fin m → Bool) := univ.filter (fun i => x i=pref i)
  let bad := univ.filter (fun x : Fin m → Bool => 4*(aligned x).card < m)
  let count (x : Fin m → Bool) := (univ.filter (fun y : Fin m → Bool =>
    |offset x+∑ i, (B i+C i*signBit (x i))*signBit (y i)| ≤ c*δ)).card
  have miss : 4*r*bad.card ≤ 2^m := by
    have d := match_tail pref mp
    change bad.card*m ≤ 4*2^m at d
    have e := (Nat.mul_le_mul_left bad.card small).trans d
    nlinarith
  have short (x) (outside : x∉bad) : 4*r*count x ≤ 2^m := by
    have cap : g ≤ (aligned x).card := by
      have h : ¬4*(aligned x).card < m := fun h => outside (mem_filter.mpr ⟨mem_univ _,h⟩)
      omega
    obtain ⟨t,sub,card⟩ := exists_subset_card_eq cap
    have heavy (i) (hi : i∈t) : δ ≤ |B i+C i*signBit (x i)| := by
      rw [(mem_filter.mp (sub hi)).2]; exact good i
    have bounded := block_small_ball t (fun i => B i+C i*signBit (x i)) δ (offset x) c pos heavy
    simp only [card,Fintype.card_fin] at bounded
    have mid : g.choose (g/2)=(u^2).centralBinom := by simp [g,Nat.centralBinom_eq_two_mul_choose]
    rw [mid] at bounded
    have inst : (fun a b : Fin m => Classical.propDecidable (a=b)) = instDecidableEqFin m :=
      Subsingleton.elim _ _
    rw [inst] at bounded
    have lim : count x ≤ 2^(m-g)*((c+1)*(u^2).centralBinom) := by simpa only [count] using bounded
    have gm : g ≤ m := by omega
    calc
      _ ≤ 4*r*(2^(m-g)*((c+1)*(u^2).centralBinom)) := Nat.mul_le_mul_left _ lim
      _ = (u*(u^2).centralBinom)*2^(m-g) := by dsimp [u]; ring
      _ ≤ 2^g*2^(m-g) := Nat.mul_le_mul_right _ (central_layer_bound u).le
      _ = _ := by rw [←pow_add,Nat.add_sub_of_le gm]
  have each (x : Fin m → Bool) : 4*r*count x ≤ 2^m+(if x∈bad then 4*r*2^m else 0) := by
    by_cases hx : x∈bad
    · have bound : count x ≤ 2^m := (card_filter_le _ _).trans_eq (by simp)
      simpa [hx] using (Nat.mul_le_mul_left (4*r) bound).trans (Nat.le_add_left _ _)
    · simpa [hx] using short x hx
  have both : 4*r*(∑ x, count x) ≤ 2^m*2^m+4*r*bad.card*2^m := by
    rw [mul_sum]
    refine (sum_le_sum (fun x _ => each x)).trans_eq ?_
    rw [sum_add_distrib]
    simp; ring
  have twice := both.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (2^m) miss) _)
  change 2*r*(∑ x, count x) ≤ _
  nlinarith

end Green53ParityBlocks

#print axioms Green53ParityBlocks.one_large_sign
#print axioms Green53ParityBlocks.uncorrelated_variance
#print axioms Green53ParityBlocks.few_good

#print axioms Green53ParityBlocks.match_tail

#print axioms Green53ParityBlocks.two_sign_window
