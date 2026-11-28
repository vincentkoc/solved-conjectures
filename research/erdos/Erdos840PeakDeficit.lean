import Green33SubpowerIntervals
import Mathlib.Combinatorics.Additive.Energy

/-! A quantitative obstruction to quasi-Sidon sets with bounded ordered sum counts. -/

open Finset Filter Asymptotics Green33SubpowerIntervals
open scoped Pointwise Topology Combinatorics.Additive

namespace Erdos840PeakDeficit

/-- Lost unordered sums, allowing equal summands. -/
def deficit (A : Finset ℕ) : ℕ := (A.card+1).choose 2-(A+A).card

/-- The maximum includes diagonal ordered pairs. -/
def peak (A : Finset ℕ) : ℕ := (A+A).sup (orderedCount A)

private lemma all_fibers {α β : Type*} [DecidableEq β] (P : Finset α) (T : Finset β)
    (f : α → β) (cover : ∀ a ∈ P, f a ∈ T) :
    (∑ y ∈ T, (P.filter (fun a => f a=y)).card) = P.card := by
  rw [sum_card_fiberwise_eq_card_filter,filter_eq_self.mpr cover]

private lemma fiber_single {A : Finset ℕ} {s : ℕ} (hs : s∈A+A) (one : orderedCount A s=1) :
    0 < (A.filter (fun a => a+a=s)).card := by
  obtain ⟨a,ha,b,hb,eq⟩ := mem_add.mp hs
  let F := (A ×ˢ A).filter fun p => p.1+p.2=s
  have h₁ : (a,b) ∈ F := mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,eq⟩
  have h₂ : (b,a) ∈ F := mem_filter.mpr ⟨mem_product.mpr ⟨hb,ha⟩,(add_comm b a).trans eq⟩
  have he : (a,b)=(b,a) := card_le_one_iff.mp (show F.card≤1 from one.le) h₁ h₂
  have e : a=b := congrArg Prod.fst he
  exact card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,by simpa only [←e] using eq⟩⟩

/-- Nontrivial additive quadruples are controlled by the product of the
ordered peak and the unordered sum deficit. -/
theorem energy_deficit (A : Finset ℕ) :
    E[A]+A.card ≤ 2*A.card^2+2*peak A*deficit A := by
  let S := A+A
  let r := orderedCount A
  let d (s : ℕ) := (A.filter fun a => a+a=s).card
  let m := peak A
  let k := A.card
  have mass : ∑ s ∈ S, r s = k^2 := by
    calc
      _ = (A ×ˢ A).card := all_fibers _ _ _ (by
        intro p hp
        exact mem_add.mpr ⟨p.1,(mem_product.mp hp).1,p.2,(mem_product.mp hp).2,rfl⟩)
      _ = _ := by simp [k,sq]
  have diag : ∑ s ∈ S, d s = k := all_fibers _ _ _ (by
    intro a ha; exact mem_add.mpr ⟨a,ha,a,ha,rfl⟩)
  have localBound (s) (hs : s∈S) : (r s)^2+2*m+d s ≤ (m+2)*r s + m*d s := by
    have cap : r s ≤ m := Finset.le_sup (f := r) hs
    have pos : 0<r s := by
      obtain ⟨a,ha,b,hb,eq⟩ := mem_add.mp hs
      exact card_pos.mpr ⟨(a,b),mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,eq⟩⟩
    by_cases one : r s=1
    · have hd : 0<d s := fiber_single hs one
      obtain ⟨a,hm⟩ := Nat.exists_eq_add_of_le (show 1 ≤ m by omega)
      obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le (show 1≤d s by omega)
      rw [one,hm,hb]
      nlinarith only [Nat.zero_le (a*b)]
    · have lo : 2≤r s := by omega
      obtain ⟨a,hm⟩ := Nat.exists_eq_add_of_le cap
      obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le lo
      rw [hm,hb]
      nlinarith only [Nat.zero_le (a*b),Nat.zero_le (b*d s),Nat.zero_le (a*d s),Nat.zero_le (d s)]
  have e : ∑ s ∈ S, (r s)^2 = E[A] := (addEnergy_eq_sum_sq' A A).symm
  have sumBound := sum_le_sum localBound
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,mass,diag,e] at sumBound
  have combine : deficit A + S.card = (k+1).choose 2 :=
    Nat.sub_add_cancel (Green33QuasiSidon.sumset_upper A)
  have pairs : (k+1)*k = (k+1).choose 2 * 2 := by
    simpa using Nat.add_one_mul_choose_eq k 1
  change E[A]+k ≤ 2*k^2+2*m*deficit A
  nlinarith only [sumBound,congrArg (fun x : ℕ => 2*m*x) combine,congrArg (fun x : ℕ => m*x) pairs]


private def diff (p : ℕ × ℕ) := (p.1:ℤ)-p.2
private def support (A : Finset ℕ) := (A ×ˢ A).image diff
private def count (A : Finset ℕ) (z : ℤ) := ((A ×ˢ A).filter fun p => diff p=z).card

private lemma count_mass (A : Finset ℕ) (T : Finset ℤ) (sub : support A ⊆ T) :
    ∑ z ∈ T, count A z = A.card^2 := by
  calc
    _ = (A ×ˢ A).card := all_fibers _ _ _ (fun p hp => sub (mem_image_of_mem _ hp))
    _ = _ := by simp [sq]

private lemma count_zero (A : Finset ℕ) : count A 0=A.card := by
  have e : ((A ×ˢ A).filter fun p => diff p=0)=A.diag := by
    ext p
    simp only [mem_filter,mem_product,mem_diag,diff,sub_eq_zero,Nat.cast_inj]
    grind
  simp only [count,e,diag_card]

private lemma count_le (A : Finset ℕ) (z : ℤ) : count A z ≤ A.card := by
  apply card_le_card_of_injOn Prod.fst
  · intro x hx; exact (mem_product.mp (mem_filter.mp hx).1).1
  · intro x hx y hy e
    have h₁ := (mem_filter.mp hx).2
    have h₂ := (mem_filter.mp hy).2
    dsimp only [diff] at h₁ h₂
    exact Prod.ext e (by omega)

private lemma difference_energy (A B : Finset ℕ) (T : Finset ℤ) (sub : support A ⊆ T) :
    E[A,B] = ∑ z ∈ T, count A z*count B z := by
  let X := ((A ×ˢ A) ×ˢ B ×ˢ B).filter fun p => p.1.1+p.2.1=p.1.2+p.2.2
  have mapped (v) (hv : v∈X) : diff v.1 ∈ T :=
    sub (mem_image_of_mem _ ((mem_product.mp (mem_filter.mp hv).1).1))
  change X.card=_
  rw [← all_fibers X T (fun v => diff v.1) mapped]
  apply sum_congr rfl
  intro z _
  have rev : ((B ×ˢ B).filter (fun p => diff (p.2,p.1)=z)).card=count B z := by
    apply Finset.card_equiv (Equiv.prodComm ℕ ℕ)
    intro p
    simp only [mem_filter,mem_product,Equiv.prodComm_apply,Prod.swap]
    tauto
  calc
    _ = (((A ×ˢ A).filter (fun p => diff p=z)) ×ˢ ((B ×ˢ B).filter (fun p => diff (p.2,p.1)=z))).card := by
      apply congrArg Finset.card
      apply Finset.ext
      intro v
      constructor
      · intro hv
        obtain ⟨hx,hz⟩ := Finset.mem_filter.mp hv
        obtain ⟨both,eq⟩ := Finset.mem_filter.mp hx
        obtain ⟨ha,hb⟩ := mem_product.mp both
        apply mem_product.mpr
        refine ⟨Finset.mem_filter.mpr ⟨ha,hz⟩,Finset.mem_filter.mpr ⟨hb,?_⟩⟩
        dsimp only [diff] at hz ⊢
        omega
      · intro hv
        obtain ⟨ha,hb⟩ := mem_product.mp hv
        obtain ⟨ha,hz⟩ := Finset.mem_filter.mp ha
        obtain ⟨hb,hw⟩ := Finset.mem_filter.mp hb
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,?_⟩,hz⟩
        dsimp only [diff] at hz hw
        omega
    _ = _ := by rw [card_product,rev]; rfl

/-- The estimate for translates works for arbitrary finite shift sets B. -/
theorem mixed_energy (A B : Finset ℕ) :
    E[A,B] ≤ B.card*(A.card+B.card-1+peak A*deficit A) := by
  classical
  let T := insert 0 (support A ∪ support B)
  have ha : support A ⊆ T := fun _ e => mem_insert_of_mem (mem_union_left _ e)
  have hb : support B ⊆ T := fun _ e => mem_insert_of_mem (mem_union_right _ e)
  have z : (0:ℤ) ∈ T := mem_insert_self ..
  have totA := count_mass A T ha
  have totB := count_mass B T hb
  have self := difference_energy A A T ha
  have mixed := difference_energy A B T ha
  rw [←sum_erase_add _ _ z,count_zero] at totA totB
  rw [←sum_erase_add _ _ z,count_zero] at self mixed
  simp only [count_zero] at mixed
  have each (x : ℤ) : 2*(count A x*count B x)+B.card*count A x ≤
      2*count B x+B.card*(count A x*count A x) := by
    have bound := count_le B x
    rcases count A x with _|_|a
    · simp
    · simp
    · nlinarith only [bound,Nat.mul_le_mul_right a bound,Nat.zero_le (a*a*B.card)]
  have sum := sum_le_sum (s := T.erase 0) (fun x _ => each x)
  simp only [sum_add_distrib,← mul_sum] at sum
  have energy := energy_deficit A
  by_cases small : A.card+B.card=0
  · have e : B=∅ := card_eq_zero.mp (by omega)
    simp [e]
  have base := Nat.sub_add_cancel (show 1≤A.card+B.card by omega)
  nlinarith only [sum,mixed,self,totA,totB,congrArg (fun u : ℕ => B.card*u) totA,
    congrArg (fun u : ℕ => B.card*u) self,Nat.mul_le_mul_left B.card energy,
    congrArg (fun u : ℕ => B.card*u) base]


/-- H consecutive translates of A give a finite size–multiplicity inequality
in the ambient interval [1,N]. -/
theorem window {A : Finset ℕ} {N H : ℕ} (sub : A ⊆ Icc 1 N) (hH : 0<H) :
    H*A.card^2 ≤ (N+H-1)*(A.card+H-1+peak A*deficit A) := by
  have bound : (A+range H).card ≤ N+H-1 := by
    have contained : A+range H ⊆ Icc 1 (N+H-1) := by
      intro t ht
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp ht
      obtain ⟨lo,hi⟩ := mem_Icc.mp (sub ha)
      have h := mem_range.mp hb
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    simpa using card_le_card contained
  have e := le_card_add_mul_addEnergy A (range H)
  have upper := Nat.mul_le_mul bound (mixed_energy A (range H))
  simp only [card_range] at e upper
  apply Nat.le_of_mul_le_mul_left (c := H) _ hH
  simpa only [sq,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using e.trans upper


private lemma size_moments {k : ℕ → ℕ} {c : ℝ}
    (size : Tendsto (fun n => (k n:ℝ)/Real.sqrt n) atTop (𝓝 c)) :
    Tendsto (fun n => (k n:ℝ)^2/(n:ℝ)) atTop (𝓝 (c^2)) ∧
    Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  constructor
  · simpa [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)] using size.pow 2
  · have v := size.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    apply v.congr
    intro n
    change (k n:ℝ)/Real.sqrt n/Real.sqrt n=_
    rw [div_div,←sq,Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Above the Sidon density, the product of peak and lost unordered sums has
linear size. The constant comes from choosing H/N tending to c−1. -/
theorem product_lower {A : ℕ → Finset ℕ} {c b : ℝ} (hc : 1<c)
    (sub : ∀ n, A n ⊆ Icc 1 n)
    (size : Tendsto (fun n => ((A n).card:ℝ)/Real.sqrt n) atTop (𝓝 c))
    (hb : b<(c-1)^2) :
    ∀ᶠ n : ℕ in atTop, b < (peak (A n):ℝ)*(deficit (A n):ℝ)/(n:ℝ) := by
  let H (n : ℕ) := ⌊(c-1)*(n:ℝ)⌋₊+1
  let k (n : ℕ) := (A n).card
  have lh : Tendsto (fun n : ℕ => (H n:ℝ)/(n:ℝ)) atTop (𝓝 (c-1)) := by
    have floor := (tendsto_nat_floor_mul_div_atTop (show 0≤c-1 by linarith)).comp tendsto_natCast_atTop_atTop
    have v := floor.add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
    simpa [H,add_div,Function.comp_def] using v
  obtain ⟨sqsize,sparse⟩ := size_moments (k := k) size
  have lim : Tendsto (fun n : ℕ => (H n:ℝ)/(n:ℝ)/(1+(H n:ℝ)/(n:ℝ))*((k n:ℝ)^2/(n:ℝ))
      -(k n:ℝ)/(n:ℝ)-(H n:ℝ)/(n:ℝ)) atTop (𝓝 ((c-1)^2)) := by
    have v := (((lh.div ((tendsto_const_nhds (x := (1:ℝ))).add lh) (by linarith)).mul sqsize).sub sparse).sub lh
    have value : (c-1)/(1+(c-1))*c^2-0-(c-1)=(c-1)^2 := by
      rw [show 1+(c-1)=c by ring]
      field_simp [show c≠0 by linarith]
      ring
    rw [value] at v
    exact v
  filter_upwards [lim.eventually_const_lt hb,eventually_gt_atTop 0] with n near hn
  apply near.trans_le
  have hp : 0<H n := Nat.succ_pos _
  have W := window (sub n) hp
  have weak : H n*(k n)^2 ≤ (n+H n)*(k n+H n+peak (A n)*deficit (A n)) :=
    W.trans (Nat.mul_le_mul (Nat.sub_le ..) (Nat.add_le_add_right (Nat.sub_le ..) _))
  have realW : (H n:ℝ)*(k n:ℝ)^2 ≤ ((n:ℝ)+H n)*((k n:ℝ)+H n+(peak (A n):ℝ)*(deficit (A n):ℝ)) := by
    exact_mod_cast weak
  have den : 0 < (n:ℝ) := by exact_mod_cast hn
  have pos : 0 < (n:ℝ)+H n := by positivity
  calc
    _ = ((H n:ℝ)*(k n:ℝ)^2/((n:ℝ)+H n)-(k n:ℝ)-H n)/(n:ℝ) := by
      field_simp [den.ne',pos.ne']
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ den.le
      have le : (H n:ℝ)*(k n:ℝ)^2/((n:ℝ)+H n) ≤ (k n:ℝ)+H n+(peak (A n):ℝ)*(deficit (A n):ℝ) :=
        (div_le_iff₀ pos).mpr (by simpa only [mul_comm] using realW)
      linarith only [le]


/-- Every quasi-Sidon witness above density one has peak tending to infinity,
with the two asymptotic assumptions taken from the literal Erdős 840 predicate. -/
theorem quasi_sidon_peak {A : ℕ → Finset ℕ} {c : ℝ} (hc : 1<c)
    (sub : ∀ n, A n ⊆ Icc 1 n)
    (size : (fun n => ((A n).card:ℝ)) ~[atTop] (fun n : ℕ => c*Real.sqrt n))
    (sums : (fun n => ((A n+A n).card:ℝ)) ~[atTop] (fun n => ((A n).card.choose 2:ℝ))) :
    Tendsto (fun n => peak (A n)) atTop atTop := by
  let k (n : ℕ) := (A n).card
  have linear : Tendsto (fun n : ℕ => c*Real.sqrt n/Real.sqrt n) atTop (𝓝 c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    field_simp
  have scale : Tendsto (fun n => (k n:ℝ)/Real.sqrt n) atTop (𝓝 c) :=
    (size.div (IsEquivalent.refl (u := fun n : ℕ => Real.sqrt n))).symm.tendsto_nhds linear
  obtain ⟨squares,sparse⟩ := size_moments scale
  have pairs : Tendsto (fun n => ((k n).choose 2:ℝ)/(n:ℝ)) atTop (𝓝 (c^2/2)) := by
    have v := (squares.sub sparse).div_const 2
    rw [sub_zero] at v
    apply v.congr
    intro n
    rw [Nat.cast_choose_two]
    ring
  have sumScale : Tendsto (fun n => ((A n+A n).card:ℝ)/(n:ℝ)) atTop (𝓝 (c^2/2)) :=
    (sums.div (IsEquivalent.refl (u := fun n : ℕ => (n:ℝ)))).symm.tendsto_nhds pairs
  have loss : Tendsto (fun n => (deficit (A n):ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    have v := (pairs.add sparse).sub sumScale
    rw [add_zero,sub_self] at v
    apply v.congr
    intro n
    rw [deficit,Nat.cast_sub (Green33QuasiSidon.sumset_upper _),Nat.choose_succ_succ, Nat.choose_one_right,Nat.cast_add]
    change _=((k n:ℝ)+((k n).choose 2:ℝ)-_)/_
    ring
  let b := (c-1)^2/2
  have bp : 0<b := by dsimp [b]; positivity
  have lt : b<(c-1)^2 := by dsimp [b]; nlinarith [sq_pos_of_pos (show 0<c-1 by linarith)]
  have lower := product_lower hc sub scale lt
  apply tendsto_atTop.mpr
  intro m
  have vanishing : Tendsto (fun n => (m:ℝ)*((deficit (A n):ℝ)/(n:ℝ))) atTop (𝓝 0) := by
    simpa using loss.const_mul (m:ℝ)
  filter_upwards [lower,vanishing.eventually_lt_const bp] with n low high
  by_contra! small
  have le : (peak (A n):ℝ) ≤ (m:ℝ) := by exact_mod_cast small.le
  have bound := mul_le_mul_of_nonneg_right le (show 0≤(deficit (A n):ℝ)/(n:ℝ) by positivity)
  rw [←mul_div_assoc] at bound
  linarith only [low,high,bound]


/-- The Green transfer selects Erdős 840 witnesses whose ordered peak
diverges and eventually lies below every positive power of interval length. -/
theorem green_quasi_sidon_two_sided (green : Green33StrictReduction.OrdinaryLimit) :
    ∃ A : ℕ → Finset ℕ, (∀ n, A n ⊆ Icc 1 n) ∧
      ((fun n => ((A n).card:ℝ)) ~[atTop] (fun n : ℕ => Real.sqrt 2*Real.sqrt n)) ∧
      ((fun n => ((A n+A n).card:ℝ)) ~[atTop] (fun n => ((A n).card.choose 2:ℝ))) ∧
      Tendsto (fun n => peak (A n)) atTop atTop ∧
      ∀ h : ℕ, ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, (orderedCount (A n) t)^h ≤ n := by
  obtain ⟨A,sub,size,sums,cap⟩ := green_erdos840_subpower green
  exact ⟨A,sub,size,sums,quasi_sidon_peak (Real.lt_sqrt_of_sq_lt (by norm_num)) sub size sums,cap⟩

#print axioms green_quasi_sidon_two_sided

#print axioms quasi_sidon_peak

#print axioms product_lower

#print axioms window

#print axioms mixed_energy

#print axioms energy_deficit

end Erdos840PeakDeficit
