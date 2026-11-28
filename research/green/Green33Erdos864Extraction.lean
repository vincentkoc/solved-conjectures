import Green33ReflectionRigidity
import FormalConjectures.ErdosProblems.«864»
import Mathlib.Data.Finset.Sym

/-! Extracting an interval set with one exceptional sum from a cyclic two-basis. -/

open Finset Filter Green33ReflectionRigidity Green33Multiplicity
open scoped Pointwise Topology

namespace Green33Erdos864Extraction

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private def pairSum : Sym2 G → G := Sym2.lift ⟨(· + ·), add_comm⟩

/-- All unordered pairs of equal sum agree, except possibly at the center c. -/
def UniqueOff (A : Finset G) (c : G) : Prop :=
  ∀ u ∈ A.sym2, ∀ v ∈ A.sym2, pairSum u = pairSum v → pairSum u ≠ c → u = v

private lemma center_fiber [Fintype G] (A : Finset G) (c : G) :
    reps A c ≤ 2 * (A.sym2.filter fun u => pairSum u = c).card := by
  rw [← card_reflectedPart]
  let f (a : G) := Sym2.mk a (c-a)
  apply card_le_mul_card_image_of_maps_to (f := f) _ 2 _
  · intro x hx
    obtain ⟨ha,hb⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mk_mem_sym2_iff.mpr ⟨ha,hb⟩,by change x+(c-x)=c; abel⟩
  · rintro ⟨x,y⟩ _
    apply (card_le_card (t := {x,y}) ?_).trans card_le_two
    intro a ha
    rcases Sym2.eq_iff.mp (mem_filter.mp ha).2 with h | h <;> simp [h.1]

/-- Removing at most one label per excess pair outside a chosen center leaves
all other sum representations unique. The finite loss is measured against the
ordered count at that center. -/
theorem extract_off_center [Fintype G] (A : Finset G) (hA : A+A = univ) (c : G) :
    ∃ B ⊆ A, UniqueOff B c ∧
      2*(A.card - B.card) + reps A c + 2*Fintype.card G ≤ A.card^2 + A.card + 2 := by
  classical
  have inhabitants (s : G) : ∃ u ∈ A.sym2, pairSum u = s := by
    have hs : s ∈ A+A := hA.symm ▸ mem_univ s
    obtain ⟨a,ha,b,hb,he⟩ := Finset.mem_add.mp hs
    exact ⟨Sym2.mk a b,mk_mem_sym2_iff.mpr ⟨ha,hb⟩,he⟩
  choose rep hmem hsum using inhabitants
  let chosen := (univ.erase c).image rep
  let center := A.sym2.filter fun u => pairSum u = c
  let keep := chosen ∪ center
  let bad := A.sym2 \ keep
  have hex (u : Sym2 G) : ∃ x, x ∈ u := by
    obtain ⟨x,y⟩ := u
    exact ⟨x,Sym2.mem_mk_left x y⟩
  choose endpoint hend using hex
  let cut := bad.image endpoint
  let B := A \ cut
  have hB : B ⊆ A := sdiff_subset
  have survives (u : Sym2 G) (hu : u ∈ B.sym2) (hne : pairSum u ≠ c) :
      u = rep (pairSum u) := by
    have huA := sym2_mono hB hu
    have hkeep : u ∈ keep := by
      by_contra h
      have he := mem_sym2_iff.mp hu _ (hend u)
      exact (mem_sdiff.mp he).2 (mem_image_of_mem _ (mem_sdiff.mpr ⟨huA,h⟩))
    rcases mem_union.mp hkeep with h | h
    · obtain ⟨s,_,rfl⟩ := mem_image.mp h
      rw [hsum]
    · exact False.elim (hne (mem_filter.mp h).2)
  refine ⟨B,hB,?_,?_⟩
  · intro u hu v hv he hne
    exact (survives u hu hne).trans (he ▸ (survives v hv (he ▸ hne)).symm)
  · have inj : Function.Injective rep := fun x y h =>
        (hsum x).symm.trans ((congrArg pairSum h).trans (hsum y))
    have disj : Disjoint chosen center := by
      apply disjoint_left.mpr
      intro u hu hv
      obtain ⟨s,hs,rfl⟩ := mem_image.mp hu
      exact (mem_erase.mp hs).1 ((hsum s).symm.trans (mem_filter.mp hv).2)
    have keepSub : keep ⊆ A.sym2 := by
      intro u hu
      rcases mem_union.mp hu with h | h
      · obtain ⟨s,_,rfl⟩ := mem_image.mp h
        exact hmem s
      · exact (mem_filter.mp h).1
    have hbad : bad.card + keep.card = A.sym2.card := card_sdiff_add_card_eq_card keepSub
    have hkeep : keep.card = (Fintype.card G - 1) + center.card := by
      rw [show keep = chosen ∪ center from rfl,card_union_of_disjoint disj]
      simp [chosen,card_image_of_injective _ inj]
    have hcut : cut.card ≤ bad.card := card_image_le
    have hdiff : A.card ≤ B.card + cut.card := card_le_card_sdiff_add_card
    have hf : reps A c ≤ 2*center.card := center_fiber A c
    have hg : 0 < Fintype.card G := Fintype.card_pos
    have hpairs : 2*A.sym2.card = A.card^2 + A.card := by
      rw [card_sym2]
      apply Nat.cast_injective (R := ℚ)
      push_cast [Nat.cast_choose_two]
      ring
    omega


/-- Lift a cyclic set with at most one repeated residue to an interval of the
same length. Translating the center to zero or one prevents a second repeated
integer sum at the wrap. -/
theorem interval_lift (M : ℕ+) (A : Finset (ZMod M)) {c : ZMod M} (hA : UniqueOff A c) :
    ∃ B ⊆ Finset.Icc 1 M.val, B.card = A.card ∧ Erdos864.HasAtMostOneRepeatedSum B := by
  classical
  let h := c.val / 2
  let f (a : ZMod M) := (a - (h : ZMod M)).val + 1
  let B := A.image f
  have inj : Function.Injective f := by
    intro a b hab
    have he : a - (h : ZMod M) = b - h := (ZMod.val_injective M.val) (Nat.add_right_cancel hab)
    exact sub_left_injective he
  have rangeF (a : ZMod M) : f a ∈ Finset.Icc 1 M.val := by
    dsimp [f]
    exact mem_Icc.mpr ⟨by omega,(a-(h : ZMod M)).val_lt⟩
  have casts (a : ZMod M) : (f a : ZMod M) = a-(h : ZMod M)+1 := by
    simp [f]
  have hc : ((c.val%2 : ℕ) : ZMod M) + 2*(h : ZMod M) = c := by
    have hh := congrArg (fun n : ℕ => (n : ZMod M)) (Nat.mod_add_div c.val 2)
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val] using hh
  have exceptional (n : ℕ) (hn : 1 < (Erdos864.sumRepresentations B n).card) :
      n = M.val + c.val%2 + 2 := by
    obtain ⟨⟨a,b⟩,hp,⟨d,e⟩,hq,hneq⟩ := one_lt_card.mp hn
    obtain ⟨⟨ha,hb⟩,hab,habn⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hp
    obtain ⟨⟨hd,he⟩,hde,hden⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hq
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hb
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hd
    obtain ⟨w,hw,rfl⟩ := mem_image.mp he
    have sumxy : (n : ZMod M) = x+y-2*(h : ZMod M)+2 := by
      rw [← habn,Nat.cast_add,casts,casts]; ring
    have sumvw : (n : ZMod M) = v+w-2*(h : ZMod M)+2 := by
      rw [← hden,Nat.cast_add,casts,casts]; ring
    have center : x+y = c := by
      by_contra hne
      have heq : x+y=v+w := by linear_combination sumvw-sumxy
      have hu := hA (Sym2.mk x y) (mk_mem_sym2_iff.mpr ⟨hx,hy⟩)
        (Sym2.mk v w) (mk_mem_sym2_iff.mpr ⟨hv,hw⟩) heq hne
      apply hneq
      rcases Sym2.eq_iff.mp hu with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rfl
      · exact Prod.ext (by omega) (by omega)
    have hpos : 4 ≤ n := by
      have hx' := (mem_Icc.mp (rangeF x)).1
      have hv' := (mem_Icc.mp (rangeF v)).1
      by_contra! hn'
      apply hneq
      exact Prod.ext (by omega) (by omega)
    have hbnd : n ≤ 2*M.val := by
      have hx' := (mem_Icc.mp (rangeF x)).2
      have hy' := (mem_Icc.mp (rangeF y)).2
      omega
    have hcast : ((c.val%2 + 2 : ℕ) : ZMod M) = (n : ZMod M) := by
      rw [Nat.cast_add,Nat.cast_ofNat,sumxy,center]
      linear_combination hc
    have hm := (ZMod.natCast_eq_natCast_iff ..).mp hcast
    have hr := Nat.mod_lt c.val (by decide : 0<2)
    obtain ⟨d,hd⟩ := (Nat.modEq_iff_dvd' (show c.val%2 + 2 ≤ n by omega)).mp hm
    have hd1 : d=1 := by
      by_contra hne
      rcases Nat.eq_zero_or_pos d with rfl | hpos'
      · simp at hd; omega
      · have hh := Nat.mul_le_mul_left M.val (show 2≤d by omega)
        omega
    rw [hd1,mul_one] at hd
    omega
  refine ⟨B,?_,card_image_of_injective _ inj,?_⟩
  · intro a ha
    obtain ⟨x,_,rfl⟩ := mem_image.mp ha
    exact rangeF x
  · intro n m hn hm
    exact (exceptional n hn).trans (exceptional m hm).symm

/-- A k-label basis of the cyclic group of order M yields an interval example
for the exact Erdős 864 predicate, losing at most max(k²−2M,0)+1 labels. -/
theorem finite_transfer (M : ℕ+) (A : Finset (ZMod M)) (hA : A+A = univ) :
    ∃ B ⊆ Finset.Icc 1 M.val, Erdos864.HasAtMostOneRepeatedSum B ∧
      A.card ≤ B.card + (A.card^2 - 2*M.val) + 1 := by
  obtain ⟨c,hMiss⟩ := exists_reflection A hA
  obtain ⟨D,hD,hUnique,hLoss⟩ := extract_off_center A hA c
  obtain ⟨B,hB,hcard,hSingle⟩ := interval_lift M D hUnique
  have he := card_sdiff_add_card_eq_card (show reflectedPart A c ⊆ A from filter_subset _ _)
  rw [card_reflectedPart] at he
  simp only [ZMod.card] at hMiss hLoss
  exact ⟨B,hB,hSingle,by omega⟩

/-- The same interval extraction at a maximum center preserves a quadratic
constraint on the retained size. The group energy gives the improved bound
when the discrepancy is comparable to the basis size. -/
theorem moment_transfer (M : ℕ+) (A : Finset (ZMod M)) (hA : A+A = univ) :
    ∃ B ⊆ Finset.Icc 1 M.val, Erdos864.HasAtMostOneRepeatedSum B ∧
      let k := (A.card : ℝ)
      let u := k^2 - 2*(M : ℝ)
      (k-1)*(k-2) ≤ (u-k+2*(B.card : ℝ)+1)*(u+k) := by
  obtain ⟨s,_,hmax⟩ := exists_max_image univ (reps A) univ_nonempty
  obtain ⟨D,hD,hU,hloss⟩ := extract_off_center A hA s
  obtain ⟨B,hB,hcard,hSin⟩ := interval_lift M D hU
  have hcap := cap_surplus A hA (reps A s) (fun x => hmax x (mem_univ x))
  simp only [ZMod.card] at hcap hloss
  have hlo : (2:ℝ)*((A.card : ℝ)-D.card) + reps A s + 2*(M : ℝ) ≤
      (A.card : ℝ)^2+A.card+2 := by
    have ht : (2:ℝ)*((A.card-D.card : ℕ):ℝ) + reps A s + 2*(M : ℝ) ≤
        (A.card : ℝ)^2+A.card+2 := by exact_mod_cast hloss
    rwa [Nat.cast_sub (card_le_card hD)] at ht
  have cov : (A+A).card ≤ (A.card+1).choose 2 := by
    have h : A+A ⊆ A.sym2.image pairSum := by
      intro z hz
      obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hz
      exact mem_image.mpr ⟨Sym2.mk x y,mk_mem_sym2_iff.mpr ⟨hx,hy⟩,rfl⟩
    simpa only [card_sym2] using (card_le_card h).trans card_image_le
  rw [hA,card_univ,ZMod.card] at cov
  have hn : (M : ℝ) ≤ ((A.card+1).choose 2 : ℝ) := by exact_mod_cast cov
  rw [Nat.cast_choose_two,Nat.cast_add_one] at hn
  refine ⟨B,hB,hSin,?_⟩
  dsimp only
  rw [hcard]
  apply hcap.trans
  have hz : 0 ≤ (A.card : ℝ)^2 + A.card - 2*(M : ℝ) := by linarith
  rw [show (A.card : ℝ)^2-2*(M : ℝ)+A.card = (A.card : ℝ)^2+A.card-2*(M : ℝ) by ring]
  gcongr
  linarith

/-- The maximum-center moment improves the conditional deficit constant. Every
nonnegative c below the positive root of (c−√2+4/√3)(c+√2)=2 is admissible,
uniformly over all sufficiently large cyclic orders and all full bases. -/
theorem erdos864_moment_gap (h864 : type_of% Erdos864.erdos_864) {c : ℝ} (hc : 0 ≤ c)
    (hcrit : (c-Real.sqrt 2+2*(2/Real.sqrt 3))*(c+Real.sqrt 2) < 2) :
    ∀ᶠ M : ℕ+ in atTop, ∀ A : Finset (ZMod M), A+A = univ →
      c * Real.sqrt M < (A.card : ℝ)^2-2*(M : ℝ) := by
  let v := Real.sqrt 2
  let L := 2/Real.sqrt 3
  have hv : v^2 = 2 := Real.sq_sqrt (by norm_num)
  have hv1 : 1 ≤ v := by dsimp [v]; norm_num
  have hL : 0<L := by dsimp [L]; positivity
  have hcrit' : (c-v+2*L)*(c+v) < 2 := hcrit
  have hp : 0<c+v := by linarith
  let ε := (2-(c-v+2*L)*(c+v))/(4*L*(c+v))
  have denom : 0<4*L*(c+v) := by positivity
  have he : 0<ε := div_pos (sub_pos.mpr hcrit') denom
  have heq : ε*(4*L*(c+v))=2-(c-v+2*L)*(c+v) := by
    dsimp only [ε]; field_simp [denom.ne']
  let a := c-v+2*((1+ε)*L)
  have ha : a*(c+v)<v*v := by dsimp only [a]; nlinarith [heq,hcrit']
  let d (M : ℕ+) := 1/Real.sqrt (M : ℝ)
  have hwtop := Real.tendsto_sqrt_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_PNat_val_atTop_atTop)
  have hd : Tendsto d atTop (𝓝 0) := (tendsto_const_nhds (x := (1:ℝ))).div_atTop hwtop
  have lower := ((tendsto_const_nhds (x := v)).sub ((tendsto_const_nhds (x := (2:ℝ))).mul hd)).mul
    ((tendsto_const_nhds (x := v)).sub ((tendsto_const_nhds (x := (3:ℝ))).mul hd))
  have upper := ((tendsto_const_nhds (x := a)).add ((tendsto_const_nhds (x := (2:ℝ))).mul hd)).mul
    ((tendsto_const_nhds (x := c+v)).add ((tendsto_const_nhds (x := c)).mul hd))
  simp only [mul_zero,sub_zero,add_zero] at lower upper
  filter_upwards [upper.eventually_lt lower ha,hwtop.eventually_gt_atTop 4,
    tendsto_PNat_val_atTop_atTop.eventually (h864 ε he)] with M hsep hw4 hbound
  intro A hA
  by_contra! hlow
  let w := Real.sqrt (M : ℝ)
  let k := (A.card : ℝ)
  let u := k^2 - 2*(M : ℝ)
  have hw : 0<w := Real.sqrt_pos.mpr (by exact_mod_cast M.pos)
  have hw2 : w^2=(M : ℝ) := Real.sq_sqrt (by positivity)
  have hdef : u ≤ c*w := hlow
  have hkk : 0≤k := Nat.cast_nonneg _
  have hq := order_bound A hA
  rw [ZMod.card] at hq
  have hq' : 2 * (M : ℝ) ≤ k^2+2 := by dsimp only [k]; exact_mod_cast hq
  have hvw : (v*w)^2 = 2*(M : ℝ) := by rw [mul_pow,hv,hw2]
  change 4<w at hw4
  have hwv : w ≤ v*w := by nlinarith [mul_nonneg (sub_nonneg.mpr hv1) hw.le]
  have hklo : v*w-1 ≤ k := by
    by_contra! h
    have hsq := sq_lt_sq' (show -(v*w-1)<k by linarith) h
    nlinarith only [hsq,hvw,hq',hwv,hw4]
  have hkhi : k ≤ v*w+c := by
    by_contra! h
    have hsq := sq_lt_sq' (show -k<v*w+c by linarith only [hkk,hwv,hw4,hc]) h
    have hu : k^2 ≤ 2*(M : ℝ)+c*w := by dsimp only [u] at hdef; linarith
    nlinarith only [hsq,hu,hvw,mul_le_mul_of_nonneg_right hwv hc,sq_nonneg c,mul_nonneg hw.le hc]
  obtain ⟨B,hB,hSing,hineq⟩ := moment_transfer M A hA
  change (k-1)*(k-2) ≤ (u-k+2*(B.card : ℝ)+1)*(u+k) at hineq
  have hBcard : (B.card : ℝ) ≤ (1+ε)*L*w := hbound B hB hSing
  have hz : 0 ≤ u+k := by dsimp only [u]; linarith
  have hleft : (v*w-2)*(v*w-3) ≤ (k-1)*(k-2) := by
    apply mul_le_mul <;> linarith
  have hfirst : u-k+2*(B.card : ℝ)+1 ≤ a*w+2 := by dsimp only [a]; linarith
  have hn : 0 ≤ a*w+2 := by
    by_contra! h
    have hf : u-k+2*(B.card : ℝ)+1 ≤ 0 := by linarith
    have hmal := mul_nonpos_of_nonpos_of_nonneg hf hz
    nlinarith [mul_pos (show 0<k-1 by linarith) (show 0<k-2 by linarith)]
  have hright : (u-k+2*(B.card : ℝ)+1)*(u+k) ≤ (a*w+2)*((c+v)*w+c) :=
    mul_le_mul hfirst (by linarith) hz hn
  have contra := hleft.trans (hineq.trans hright)
  change (a + 2*(1/w))*((c+v)+c*(1/w)) < (v-2*(1/w))*(v-3*(1/w)) at hsep
  field_simp [hw.ne'] at hsep
  nlinarith [contra]

/-- In particular the ordinary cyclic minimum eventually exceeds √(2M)+1/10
under the conjectured Erdős 864 upper bound. -/
theorem tenth_gap (h864 : type_of% Erdos864.erdos_864) :
    ∀ᶠ M : ℕ+ in atTop, ∀ A : Finset (ZMod M), A+A = univ →
      Real.sqrt (2*(M : ℝ)) + 1/10 < (A.card : ℝ) := by
  have twoLo : (141421:ℝ)/100000 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have twoHi : Real.sqrt 2 < (141422:ℝ)/100000 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have threeLo : (173205:ℝ)/100000 < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have Lhi : 2/Real.sqrt 3 < (115471:ℝ)/100000 := by
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3))).mpr
    linarith only [threeLo]
  have hcrit : ((283:ℝ)/1000-Real.sqrt 2+2*(2/Real.sqrt 3))*(283/1000+Real.sqrt 2)<2 := by
    have h := mul_le_mul (by linarith only [twoLo,Lhi] :
      (283:ℝ)/1000-Real.sqrt 2+2*(2/Real.sqrt 3) ≤ 283/1000-141421/100000+2*(115471/100000))
      (by linarith only [twoHi] : (283:ℝ)/1000+Real.sqrt 2 ≤ 283/1000+141422/100000)
      (by positivity) (by norm_num)
    linarith only [h]
  have ht := erdos864_moment_gap h864 (by norm_num : (0:ℝ) ≤ 283/1000) hcrit
  have hlarge := Real.tendsto_sqrt_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_PNat_val_atTop_atTop)
  filter_upwards [ht,hlarge.eventually_gt_atTop 100] with M hgap hroot
  intro A hA
  have hg := hgap A hA
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  by_contra! h
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg A.card) h 2
  have he : (Real.sqrt 2 * Real.sqrt (M : ℝ))^2 = 2*(M : ℝ) := by
    rw [mul_pow,Real.sq_sqrt (by norm_num),Real.sq_sqrt (by positivity)]
  change 100 < Real.sqrt (M : ℝ) at hroot
  have prod := mul_le_mul_of_nonneg_right twoHi.le (Real.sqrt_nonneg (M : ℝ))
  nlinarith only [hs,he,hg,prod,hroot]

#print axioms extract_off_center
#print axioms interval_lift
#print axioms finite_transfer
#print axioms erdos864_moment_gap
#print axioms tenth_gap
#print axioms moment_transfer

end Green33Erdos864Extraction
