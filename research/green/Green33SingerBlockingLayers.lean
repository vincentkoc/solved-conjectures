import Green33SingerReflectedCoverage
import Green33SingerAllCharacteristics

/-! Partial blocking sets for the translates of a perfect difference set.

The two incidence inequalities are the counts in the proof of Theorem 3.2
of Blokhuis, Brouwer, Szőnyi and Weiner, *On q-analogues and stability theorems*
(2011), following Erdős and Lovász. The full-cover corollary is Bruen's
blocking-set bound. We apply these counts to both parities of a cyclic basis.
-/

open Finset Green33PerfectDifferenceCenters Green33TailEnergy
open scoped Pointwise

namespace Green33SingerBlockingLayers

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The intersection of the second layer with the line indexed by x. -/
def occupancy (D B : Finset G) (x : G) : ℕ := (D.filter fun d => x-d∈B).card

omit [Fintype G] in
private theorem occupancy_sum (D B : Finset G) (x : G) :
    occupancy D B x = ∑ d ∈ D, if x-d∈B then 1 else 0 := by
  exact Finset.card_filter _ _

omit [Fintype G] in
theorem occupancy_pos (D B : Finset G) (x : G) : 0<occupancy D B x ↔ x∈D+B := by
  rw [occupancy,card_pos,mem_add]
  constructor
  · rintro ⟨d,hd⟩
    obtain ⟨h₁,h₂⟩ := mem_filter.mp hd
    exact ⟨d,h₁,x-d,h₂,by abel⟩
  · rintro ⟨d,hd,b,hb,rfl⟩
    exact ⟨d,mem_filter.mpr ⟨hd,by simpa using hb⟩⟩

/-- Two successive incidences through a pencil count each nonzero difference once. -/
private theorem pencil_sum (D : Finset G) (hD : Perfect D) {q : ℕ} (size : D.card=q+1)
    (w : G → ℕ) (z : G) :
    ∑ a ∈ D, ∑ b ∈ D, w (z+(a-b)) = q*w z + ∑ x, w x := by
  have zero : diffReps D 0 = D.card := by
    change ((D ×ˢ D).filter fun p => p.1-p.2=0).card = D.card
    rw [show ((D ×ˢ D).filter fun p => p.1-p.2=0) = D.diag by
      ext p; simp [Finset.mem_diag]; grind]
    simp
  have fiber : ∑ t, diffReps D t * w (z+t) = ∑ a ∈ D, ∑ b ∈ D, w (z+(a-b)) := by
    simp only [diffReps,card_eq_sum_ones,sum_mul,sum_filter]
    rw [sum_comm]
    simp [sum_product]
  have point (t : G) : diffReps D t * w (z+t) =
      (if t=0 then q*w z else 0)+w (z+t) := by
    by_cases ht : t=0
    · subst t; simp [zero,size,add_mul]
    · simp [ht,hD t ht]
  rw [← fiber]
  simp only [point,sum_add_distrib,sum_ite_eq',mem_univ,if_true]
  exact congrArg (q*w z+·) (Equiv.sum_comp (Equiv.addLeft z) w)

private theorem pencil_occupancy (D B : Finset G) (hD : Perfect D) {q : ℕ} (size : D.card=q+1)
    (z : G) (hz : z∉B) : ∑ d ∈ D, occupancy D B (z+d) = B.card := by
  simp_rw [occupancy_sum,add_sub_assoc]
  simpa [hz] using pencil_sum D hD size (fun y => if y∈B then 1 else 0) z

private theorem total_occupancy (D B : Finset G) :
    ∑ x, occupancy D B x = D.card*B.card := by
  simp_rw [occupancy_sum]
  rw [sum_comm]
  have count (d : G) : (∑ x : G, if x-d∈B then 1 else 0)=B.card := by
    calc
      _ = ∑ y : G, if y∈B then 1 else 0 := by
        simp only [sub_eq_add_neg]
        exact Equiv.sum_comp (Equiv.addRight (-d)) (fun y : G => if y∈B then (1:ℕ) else 0)
      _ = _ := by simp
  simp [count]

private theorem energy (D B : Finset G) (hD : Perfect D) {q : ℕ} (size : D.card=q+1) :
    ∑ x, (occupancy D B x:ℝ)^2 = q*B.card+(B.card:ℝ)^2 := by
  let w (x : G) : ℝ := if x∈B then 1 else 0
  have ind : ∑ x, w x = B.card := by simp [w]
  have sq (x : G) : w x*w x=w x := by by_cases h : x∈B <;> simp [w,h]
  have count (x : G) : ∑ d ∈ D, w (x-d) = (occupancy D B x:ℝ) := by
    rw [occupancy_sum,Nat.cast_sum]
    apply sum_congr rfl
    intro d _
    by_cases h : x-d∈B <;> simp [h,w]
  have e := translate_inner D hD w w
  simp only [count,sq,ind,size,Nat.cast_add,Nat.cast_one,add_sub_cancel_right,← pow_two] at e
  exact e

/-- The missing values of a mixed sumset pay for the collisions forced by a perfect layer. -/
theorem collision_bound (D B : Finset G) (hD : Perfect D) {q M : ℕ} (size : D.card=q+1)
    (cap : ∀ x, occupancy D B x≤M) :
    (B.card:ℝ)*(B.card-1) ≤ M*((D.card:ℝ)*B.card-(D+B).card) := by
  have at_x (x : G) : (occupancy D B x:ℝ)^2-occupancy D B x ≤
      (M:ℝ)*((occupancy D B x:ℝ)-(if x∈D+B then 1 else 0)) := by
    have c : (occupancy D B x:ℝ)≤M := by exact_mod_cast cap x
    by_cases h : x∈D+B
    · have one : (1:ℝ)≤occupancy D B x := by exact_mod_cast (occupancy_pos D B x).mpr h
      rw [if_pos h]
      nlinarith [mul_nonneg (sub_nonneg.mpr c) (sub_nonneg.mpr one)]
    · have z : occupancy D B x=0 := by
        have := mt (occupancy_pos D B x).mp h
        omega
      simp [h,z]
  have summed := sum_le_sum (s:=univ) (fun x _ => at_x x)
  have total : (∑ x, (occupancy D B x:ℝ))=(D.card:ℝ)*B.card := by
    exact_mod_cast total_occupancy D B
  have support : (∑ x : G, if x∈D+B then (1:ℝ) else 0)=(D+B).card := by simp
  rw [← mul_sum] at summed
  simp only [sum_sub_distrib,total,support,energy D B hD size] at summed
  rw [size,Nat.cast_add,Nat.cast_one] at summed ⊢
  nlinarith

#print axioms collision_bound

private theorem exterior_pencil (D B : Finset G) (hD : Perfect D) {q : ℕ} (size : D.card=q+1)
    {c d : G} (hit : c∈D+B) (hd : d∈D) (outside : c-d∉B) :
    occupancy D B c+q ≤ B.card + ∑ e ∈ D, if c-d+e∈D+B then 0 else 1 := by
  let w (x : G) : ℕ := if x∈D+B then 0 else 1
  have cover (e : G) : 1 ≤ occupancy D B (c-d+e) + w (c-d+e) := by
    by_cases h : c-d+e∈D+B
    · have pos := (occupancy_pos D B _).mpr h
      simp only [w,if_pos h,add_zero]
      omega
    · simp [w,h]
  have low := sum_le_sum (s:=D.erase d) (fun e _ => cover e)
  have full := sum_erase_add D (fun e => occupancy D B (c-d+e)+w (c-d+e)) hd
  simp [card_erase_of_mem hd,size] at low
  simp only [sub_add_cancel,show w c=0 from if_pos hit,add_zero] at full
  have eqn : (∑ e ∈ D, (occupancy D B (c-d+e)+w (c-d+e))) =
      B.card+∑ e ∈ D, w (c-d+e) := by rw [sum_add_distrib,pencil_occupancy D B hD size _ outside]
  rw [eqn] at full
  change occupancy D B c + q ≤ B.card + ∑ e ∈ D, w (c-d+e)
  omega

/-- Every missed line meets a fixed occupied line in just one point.
The inequality includes all missing points on that line. -/
theorem secant_bound (D B : Finset G) (hD : Perfect D) {q : ℕ} (size : D.card=q+1)
    {c : G} (hit : c∈D+B) :
    (D.card-occupancy D B c)*(occupancy D B c+q) ≤
      (D.card-occupancy D B c)*B.card+(D+B)ᶜ.card := by
  let X := D.filter fun d => c-d∉B
  let w (x : G) : ℕ := if x∈D+B then 0 else 1
  have cost : (∑ d ∈ D, ∑ e ∈ D, w (c-d+e)) = (D+B)ᶜ.card := by
    rw [sum_comm]
    have eqn (d e : G) : c-d+e=c+(e-d) := by abel
    simp_rw [eqn]
    rw [pencil_sum D hD size w c]
    have count : ∑ x : G, w x = (D+B)ᶜ.card := by
      change (∑ x : G, if x∈D+B then 0 else 1) = _
      have flip (x : G) : (if x∈D+B then 0 else 1) = (if x∈(D+B)ᶜ then (1:ℕ) else 0) := by
        by_cases hx : x∈D+B <;> simp [hx]
      calc
        _ = ∑ x : G, if x∈(D+B)ᶜ then (1:ℕ) else 0 := sum_congr rfl (fun x _ => flip x)
        _ = _ := (show ∀ S : Finset G, (∑ x : G, if x∈S then (1:ℕ) else 0)=S.card by
          intro S; simp) _
    rw [show w c=0 from if_pos hit,count,mul_zero,zero_add]
  have bound := sum_le_sum (s:=X) (fun d hd =>
    exterior_pencil D B hD size hit (mem_filter.mp hd).1 (mem_filter.mp hd).2)
  have total : (∑ d ∈ X, ∑ e ∈ D, w (c-d+e)) ≤ (D+B)ᶜ.card := by
    rw [← cost]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have partition := card_filter_add_card_filter_not (s:=D) (p:=fun d => c-d∈B)
  have sz : X.card = D.card-occupancy D B c := by
    change _ + X.card = D.card at partition
    unfold occupancy
    omega
  have bound₁ : X.card*(occupancy D B c+q) ≤ X.card*B.card+∑ d ∈ X, ∑ e ∈ D, w (c-d+e) := by
    simpa only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_add] using bound
  rw [← sz]
  exact Nat.le_trans bound₁ (Nat.add_le_add_left total _)

#print axioms secant_bound

/-- Bruen's blocking-set bound for the projective plane of a perfect difference set.
A full mixed sumset either contains a full reflected line in the second layer
or pays at least the square root of the order beyond q+1 points. -/
theorem blocking_alternative (D B : Finset G) (hD : Perfect D) {q s : ℕ} (size : D.card=q+1)
    (budget : B.card=q+1+s) (full : D+B=univ) :
    (∃ c : G, ∀ d ∈ D, c-d∈B) ∨ q≤s^2 := by
  classical
  by_cases line : ∃ c : G, ∀ d ∈ D, c-d∈B
  · exact Or.inl line
  right
  have cap (c : G) : occupancy D B c ≤ s+1 := by
    obtain ⟨d,hd,out⟩ : ∃ d ∈ D, c-d∉B := by
      by_contra! all
      exact line ⟨c,all⟩
    have hit : c∈D+B := full ▸ mem_univ _
    have bound := exterior_pencil D B hD size hit hd out
    simp [full,budget] at bound
    omega
  have bound := collision_bound D B hD size cap
  have param := parameters D hD
  rw [size,Nat.cast_add,Nat.cast_one] at param
  have v : (Fintype.card G:ℝ)=(q:ℝ)^2+q+1 := by linarith only [param]
  rw [full,card_univ,size,budget] at bound
  push_cast at bound
  rw [v] at bound
  by_cases hq : q=0
  · simp [hq]
  have pos : (0:ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have key : (q:ℝ)*q≤q*(s:ℝ)^2 := by nlinarith only [bound]
  exact_mod_cast (le_of_mul_le_mul_left key pos)

#print axioms blocking_alternative

/-- At the line size, a nearly blocking set is either within a square root of
one reflected line or misses at least q√q−2q lines. -/
theorem partial_blocking (D B : Finset G) (hD : Perfect D) {q : ℕ} (size : D.card=q+1)
    (budget : B.card=q+1) :
    (∃ c : G, (q:ℝ)+1-occupancy D B c<Real.sqrt q) ∨
      (q:ℝ)*Real.sqrt q-2*q≤(D+B)ᶜ.card := by
  classical
  by_cases zero : q=0
  · right; simp [zero]
  have qp : (0:ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero zero
  let u := Real.sqrt (q:ℝ)
  have up : 0<u := Real.sqrt_pos.mpr qp
  have uu : u^2=(q:ℝ) := Real.sq_sqrt qp.le
  let H : ℝ := ((D+B)ᶜ.card:ℝ)
  obtain ⟨c,_,peak⟩ := exists_max_image univ (occupancy D B) univ_nonempty
  let m := occupancy D B c
  have cap (x : G) : occupancy D B x≤m := peak x (mem_univ _)
  by_cases near : (q:ℝ)+1-m<u
  · exact Or.inl ⟨c,near⟩
  right
  change (q:ℝ)*u-2*q≤H
  have far : u≤(q:ℝ)+1-m := le_of_not_gt near
  have v := parameters D hD
  rw [size,Nat.cast_add,Nat.cast_one] at v
  have complete : ((D+B).card:ℝ)+H = Fintype.card G := by
    dsimp only [H]
    exact_mod_cast card_add_card_compl (D+B)
  have support : ((D+B).card:ℝ)=(q:ℝ)^2+q+1-H := by linarith
  by_cases small : (m:ℝ)≤u
  · have cyl := collision_bound D B hD size cap
    rw [size,budget,support] at cyl
    push_cast at cyl
    have low : (q:ℝ)*q ≤ m*((q:ℝ)+H) := by nlinarith only [cyl,qp]
    have Hpos : 0≤H := Nat.cast_nonneg _
    have high := mul_le_mul_of_nonneg_right small (add_nonneg qp.le Hpos)
    have eqn : u*((q:ℝ)*u) = (q:ℝ)*q := by
      calc _ = (q:ℝ)*u^2 := by ring
           _ = _ := by rw [uu]
    have h := le_of_mul_le_mul_left (eqn.le.trans (low.trans high)) up
    linarith
  · have mp : 0<m := by
      have hr : (0:ℝ)<m := up.trans (lt_of_not_ge small)
      exact_mod_cast hr
    have nat_bound := secant_bound D B hD size ((occupancy_pos D B c).mp mp)
    have nat_cap : m≤D.card := card_filter_le _ _
    change (D.card-m)*(m+q)≤(D.card-m)*B.card+(D+B)ᶜ.card at nat_bound
    have bound : ((D.card:ℝ)-m)*(m+q)≤((D.card:ℝ)-m)*B.card+H := by
      dsimp only [H]
      exact_mod_cast nat_bound
    rw [size,budget] at bound
    push_cast at bound
    have both := mul_nonneg (sub_nonneg.mpr (le_of_not_ge small))
      (show 0≤(q:ℝ)+1-m-(u-1) by linarith)
    have one : 1≤u := Real.one_le_sqrt.mpr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero)
    nlinarith only [both,bound,uu,one]

#print axioms partial_blocking

/-- Enlarging or changing a set can add at most one mixed sum per new point
and per member of the changed set. -/
theorem changed_sums (S R : Finset G) :
    (R+R)ᶜ.card ≤ (S+S)ᶜ.card+(S\R).card*S.card := by
  have sub : S+S ⊆ (R+R) ∪ ((S\R)+S) := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hz
    by_cases ax : x∈R
    · by_cases ay : y∈R
      · exact mem_union_left _ (add_mem_add ax ay)
      · exact mem_union_right _ (by simpa only [add_comm y x] using add_mem_add (mem_sdiff.mpr ⟨hy,ay⟩) hx)
    · exact mem_union_right _ (add_mem_add (mem_sdiff.mpr ⟨hx,ax⟩) hy)
  have h := (card_le_card sub).trans (card_union_le _ _)
  have mult : ((S\R)+S).card ≤ (S\R).card*S.card := card_add_le
  have a := card_add_card_compl (S+S)
  have b := card_add_card_compl (R+R)
  omega

#print axioms changed_sums

open Green33ReflectedLayers

/-- Arbitrary even and odd layers in the cyclic group of double order. -/
def split {v : ℕ+} (D B : Finset (ZMod v)) : Finset (ZMod (2*v.val)) :=
  D.image (doubleHom v) ∪ B.image (fun b => 1+doubleHom v b)

private theorem odd_holes {v : ℕ+} (D B : Finset (ZMod v)) :
    (D+B)ᶜ.card ≤ (split D B+split D B)ᶜ.card := by
  let f := doubleHom v
  obtain ⟨inj,odd,axis⟩ := double_coordinates v 0
  have no (a b : ZMod v) : f a ≠ 1+f b := by
    intro h
    apply odd (a-b)
    change f (a-b)=1+f 0
    rw [map_sub,h,map_zero]; abel
  have two : f 1=1+1 := by simpa [f] using axis
  have sub : (D+B)ᶜ.image (fun y => 1+f y) ⊆ (split D B+split D B)ᶜ := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
    apply mem_compl.mpr
    intro sum
    obtain ⟨a,ha,b,hb,eq⟩ := mem_add.mp sum
    rcases mem_union.mp ha with ha|ha <;> rcases mem_union.mp hb with hb|hb
    · obtain ⟨u,_,rfl⟩ := mem_image.mp ha
      obtain ⟨w,_,rfl⟩ := mem_image.mp hb
      exact no (u+w) y ((map_add f _ _).trans eq)
    · obtain ⟨u,hu,rfl⟩ := mem_image.mp ha
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hb
      have e : u+w=y := inj (by change f (u+w)=f y; rw [map_add]; change f u+(1+f w)=1+f y at eq; linear_combination eq)
      exact mem_compl.mp hy (e ▸ add_mem_add hu hw)
    · obtain ⟨u,hu,rfl⟩ := mem_image.mp ha
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hb
      have e : w+u=y := inj (by change f (w+u)=f y; rw [map_add]; change (1+f u)+f w=1+f y at eq; linear_combination eq)
      exact mem_compl.mp hy (e ▸ add_mem_add hw hu)
    · obtain ⟨u,_,rfl⟩ := mem_image.mp ha
      obtain ⟨w,_,rfl⟩ := mem_image.mp hb
      apply no (1+u+w) y
      change (1+f u)+(1+f w)=1+f y at eq
      rw [map_add,map_add,two]
      linear_combination eq
  have h := card_le_card sub
  rwa [card_image_of_injective _ (fun a b h => inj (add_left_cancel h))] at h

private theorem outside_reflection {v : ℕ+} (D B : Finset (ZMod v)) (c : ZMod v) :
    ((split D B)\(doubled D c)).card ≤ B.card-occupancy D B c := by
  let f := doubleHom v
  let L := D.image (c-·)
  have inter : L∩B = (D.filter (fun d => c-d∈B)).image (c-·) := by
    ext y
    constructor
    · intro h
      obtain ⟨hL,hy⟩ := mem_inter.mp h
      obtain ⟨d,hd,rfl⟩ := mem_image.mp hL
      exact mem_image.mpr ⟨d, mem_filter.mpr ⟨hd,hy⟩,rfl⟩
    · intro h
      obtain ⟨d,hd,rfl⟩ := mem_image.mp h
      exact mem_inter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hd).1,(mem_filter.mp hd).2⟩
  have cost : (B\L).card=B.card-occupancy D B c := by
    rw [card_sdiff,inter,card_image_of_injective _ (fun a b h => sub_right_inj.mp h)]
    rfl
  have sub : split D B \ doubled D c ⊆ (B\L).image (fun y => 1+f y) := by
    intro x hx
    obtain ⟨hs,hr⟩ := mem_sdiff.mp hx
    rcases mem_union.mp hs with a|odd_mem
    · exact False.elim (hr (mem_union_left _ a))
    · obtain ⟨b,hb,rfl⟩ := mem_image.mp odd_mem
      refine mem_image_of_mem _ (mem_sdiff.mpr ⟨hb,?_⟩)
      intro hL
      obtain ⟨d,hd,eq⟩ := mem_image.mp hL
      apply hr
      apply mem_union_right _
      refine mem_image.mpr ⟨d,hd,?_⟩
      change (1+f c)-f d=1+f b
      rw [← eq,map_sub]; abel
  exact (card_le_card sub).trans (card_image_le.trans_eq cost)

private theorem split_card {v : ℕ+} (A B : Finset (ZMod v)) :
    (split A B).card=A.card+B.card := by
  let f := doubleHom v
  obtain ⟨inj,odd,_⟩ := double_coordinates v 0
  have sep : Disjoint (A.image f) (B.image (fun b => 1+f b)) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    obtain ⟨b,_,eq⟩ := mem_image.mp hy
    apply odd (a-b)
    change f (a-b)=1+f 0
    rw [map_sub,← eq,map_zero]; abel
  change (A.image f ∪ B.image (fun b => 1+f b)).card=_
  rw [card_union_of_disjoint sep,card_image_of_injective _ inj,
    card_image_of_injective _ (fun a b h => inj (add_left_cancel h))]

/-- Either the mixed sumset misses q√q−2q residues, or a reflected seed
has at most 2(q+1)√q more missing residues than the cyclic double. -/
theorem doubled_alternative {v : ℕ+} (D B : Finset (ZMod v)) (hD : Perfect D) {q : ℕ}
    (size : D.card=q+1) (budget : B.card=q+1) :
    (q:ℝ)*Real.sqrt q-2*q≤(D+B)ᶜ.card ∨
    ∃ c : ZMod v, ((doubled D c+doubled D c)ᶜ.card:ℝ) ≤
      (split D B+split D B)ᶜ.card+2*((q:ℝ)+1)*Real.sqrt q := by
  obtain ⟨c,hc⟩|holes := partial_blocking D B hD size budget
  · right
    refine ⟨c,?_⟩
    let S := split D B
    let R := doubled D c
    have change_bound := changed_sums S R
    have mBound : occupancy D B c≤B.card := by rw [budget,←size];exact card_filter_le _ _
    have r : ((S\R).card:ℝ)≤(B.card:ℝ)-occupancy D B c := by
      exact_mod_cast outside_reflection D B c
    rw [budget,Nat.cast_add,Nat.cast_one] at r
    have n := (split_card D B).le
    rw [size,budget] at n
    change S.card≤(q+1)+(q+1) at n
    have n' : (S.card:ℝ)≤2*((q:ℝ)+1) := by exact_mod_cast (by omega : S.card≤2*(q+1))
    have cost := mul_le_mul (r.trans hc.le) n' (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    have bound : ((R+R)ᶜ.card:ℝ) ≤ (S+S)ᶜ.card+(S\R).card*S.card := by exact_mod_cast change_bound
    linarith only [bound,cost]
  · exact Or.inl holes

#print axioms doubled_alternative

open Filter
open scoped Topology

/-- A uniform reflected deficit forces square-root-scale repairs even when the
initial opposite layer of size q+1 can be chosen freely. -/
theorem layer_alternatives {v : ℕ→ℕ+} {q : ℕ→ℕ} (D B : ∀ i, Finset (ZMod (v i)))
    (perfect : ∀ i, Perfect (D i)) (size : ∀ i, (D i).card=q i+1)
    (budget : ∀ i, (B i).card=q i+1) (big : Tendsto q atTop atTop)
    (cov : ∀ t : (i : ℕ) → ZMod (v i), Tendsto (fun i =>
      ((doubled (D i) (t i)+doubled (D i) (t i)).card:ℝ)/(2*((v i).val:ℝ)))
      atTop (𝓝 (7/8))) :
    ∀ᶠ i in atTop, (q i:ℝ)*Real.sqrt (q i)-2*q i≤(D i+B i)ᶜ.card ∨
      2*(q i:ℝ)*Real.sqrt (q i)-2*q i≤(split (D i) (B i)+split (D i) (B i))ᶜ.card := by
  classical
  let H (i : ℕ) : ℝ := (split (D i) (B i)+split (D i) (B i))ᶜ.card
  let R (i : ℕ) (c : ZMod (v i)) := doubled (D i) c+doubled (D i) c
  have pick (i : ℕ) : ∃ c : ZMod (v i), (q i:ℝ)*Real.sqrt (q i)-2*q i≤(D i+B i)ᶜ.card ∨
      ((R i c)ᶜ.card:ℝ)≤H i+2*((q i:ℝ)+1)*Real.sqrt (q i) := by
    rcases doubled_alternative (D i) (B i) (perfect i) (size i) (budget i) with h|⟨c,h⟩
    · exact ⟨0,Or.inl h⟩
    · exact ⟨c,Or.inr h⟩
  choose c hc using pick
  have cut := (cov c).eventually_lt_const (show (7:ℝ)/8<15/16 by norm_num)
  filter_upwards [cut,big.eventually_ge_atTop 4096] with i sparse large
  rcases hc i with easy|near
  · exact Or.inl easy
  right
  let n : ℝ := q i
  let u := Real.sqrt n
  have hq : (4096:ℝ)≤n := by dsimp only [n]; exact_mod_cast large
  have ularge : 64≤u := Real.le_sqrt_of_sq_le (by norm_num; exact hq)
  have uu : u^2=n := Real.sq_sqrt (by linarith)
  have small : 64*u ≤ n := by nlinarith only [uu,mul_nonneg (sub_nonneg.mpr ularge) (Real.sqrt_nonneg n)]
  have reduction : 8*((2*n*u-2*n)+2*(n+1)*u)≤n^2 := by
    nlinarith only [mul_nonneg (show 0≤n-2 by linarith) (Real.sqrt_nonneg n),
      mul_nonneg (show 0≤n by linarith) (sub_nonneg.mpr small),hq]
  have vsize := parameters (D i) (perfect i)
  rw [size i,Nat.cast_add,Nat.cast_one,ZMod.card] at vsize
  have den : (0:ℝ)<2*((v i).val:ℝ) := by positivity
  change ((R i (c i)).card:ℝ)/(2*((v i).val:ℝ))<15/16 at sparse
  have few := (div_lt_iff₀ den).mp sparse
  have count : ((R i (c i)).card:ℝ)+((R i (c i))ᶜ.card:ℝ)=2*((v i).val:ℝ) := by
    have h := card_add_card_compl (R i (c i))
    rw [ZMod.card] at h
    exact_mod_cast h
  change (n+1)^2=(_ : ℝ)+(n+1)-1 at vsize
  change ((R i (c i))ᶜ.card:ℝ)≤H i+2*(n+1)*u at near
  change 2*n*u-2*n ≤ H i
  nlinarith only [reduction,vsize,few,count,near,hq]

#print axioms layer_alternatives

theorem all_layers {v : ℕ→ℕ+} {q : ℕ→ℕ} (D B : ∀ i, Finset (ZMod (v i)))
    (perfect : ∀ i, Perfect (D i)) (size : ∀ i, (D i).card=q i+1)
    (budget : ∀ i, (B i).card=q i+1) (big : Tendsto q atTop atTop)
    (cov : ∀ t : (i : ℕ) → ZMod (v i), Tendsto (fun i =>
      ((doubled (D i) (t i)+doubled (D i) (t i)).card:ℝ)/(2*((v i).val:ℝ)))
      atTop (𝓝 (7/8))) :
    ∀ᶠ i in atTop, (q i:ℝ)*Real.sqrt (q i)-2*q i≤
      (split (D i) (B i)+split (D i) (B i))ᶜ.card := by
  filter_upwards [layer_alternatives D B perfect size budget big cov] with i h
  rcases h with mixed|whole
  · exact mixed.trans (by exact_mod_cast odd_holes (D i) (B i))
  · nlinarith only [whole,mul_nonneg (Nat.cast_nonneg (α:=ℝ) (q i)) (Real.sqrt_nonneg (q i))]

#print axioms all_layers

open Green33SingerCoordinates Green33SingerProjectiveOverlap in
/-- Every arbitrary balanced second layer misses at least q√q−2q sums for all
large binary cubic Singer frames, without an analytic hypothesis. -/
theorem binary_holes {F K : ℕ→Type*} [∀ i, Field (F i)] [∀ i, Field (K i)]
    [∀ i, Algebra (F i) (K i)] [∀ i, CharP (F i) 2] [∀ i, Fintype (F i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (F i)] (C : ∀ i, CubicFrame (F i) (K i))
    (B : ∀ i, Finset (ZMod (Green33SingerReflectedCoverage.order (F i))))
    (budget : ∀ i, (B i).card=Fintype.card (F i)+1)
    (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    ∀ᶠ i in atTop, (Fintype.card (F i):ℝ)*Real.sqrt (Fintype.card (F i))-2*Fintype.card (F i)
      ≤(split (v:=Green33SingerReflectedCoverage.order (F i)) (labels (C i)) (B i)+
        split (v:=Green33SingerReflectedCoverage.order (F i)) (labels (C i)) (B i))ᶜ.card :=
  all_layers (v:=fun i => Green33SingerReflectedCoverage.order (F i)) _ B (fun i => Green33SingerReflectedCoverage.perfect (C i))
    (fun i => Green33SingerReflectedCoverage.label_card (C i)) budget big
    (fun t => Green33SingerReflectedCoverage.coverage C t big)

#print axioms binary_holes

private theorem decompose {v : ℕ+} (W : Finset (ZMod (2*v.val))) :
    ∃ U V : Finset (ZMod v), W=split U V ∧ W.card=U.card+V.card := by
  let f := doubleHom v
  let U := univ.filter fun x => f x∈W
  let V := univ.filter fun x => 1+f x∈W
  have all : split (v:=v) univ univ=univ := by
    apply (card_eq_iff_eq_univ _).mp
    rw [split_card,card_univ,ZMod.card,ZMod.card,two_mul]
  have eqn : W=split U V := by
    ext x
    constructor
    · intro hx
      have hu : x∈split (v:=v) univ univ := all ▸ mem_univ _
      rcases mem_union.mp hu with a|b
      · obtain ⟨a,_,rfl⟩ := mem_image.mp a
        exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hx⟩))
      · obtain ⟨b,_,rfl⟩ := mem_image.mp b
        exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hx⟩))
    · intro hx
      rcases mem_union.mp hx with a|b
      · obtain ⟨a,ha,rfl⟩ := mem_image.mp a
        exact (mem_filter.mp ha).2
      · obtain ⟨b,hb,rfl⟩ := mem_image.mp b
        exact (mem_filter.mp hb).2
  exact ⟨U,V,eqn,eqn ▸ split_card U V⟩

/-- Each new point makes mixed sums with just the opposite old layer. -/
theorem mixed_repair {v : ℕ+} {k : ℕ} (D B : Finset (ZMod v))
    (size : D.card≤k) (budget : B.card≤k) (T : Finset (ZMod (2*v.val))) (full : T+T=univ) :
    let w := (T\split D B).card
    (D+B)ᶜ.card≤k*w+w^2 := by
  let S := split D B
  let W := T\S
  obtain ⟨U,V,eqn,count⟩ := decompose W
  have enlarged : split (D∪U) (B∪V) = S∪W := by
    rw [eqn];unfold S split; simp only [image_union];ac_rfl
  have included : T ⊆ split (D∪U) (B∪V) := by
    rw [enlarged]
    intro x hx
    by_cases h : x∈S
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hx,h⟩)
  have full' : split (D∪U) (B∪V)+split (D∪U) (B∪V)=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp (show x∈T+T from full ▸ mem_univ _)
    exact add_mem_add (included ha) (included hb)
  have hh := odd_holes (D∪U) (B∪V)
  rw [full',compl_univ,card_empty] at hh
  have mixed : (D∪U)+(B∪V)=univ := by
    have empty : ((D∪U)+(B∪V))ᶜ=∅ := card_eq_zero.mp (by omega)
    simpa using congrArg (fun A : Finset (ZMod v) => Aᶜ) empty
  have sub : (D+B)ᶜ ⊆ (D+V)∪(U+B)∪(U+V) := by
    intro x hx
    obtain ⟨d,hd,b,hb,rfl⟩ := mem_add.mp (show x∈(D∪U)+(B∪V) from mixed ▸ mem_univ _)
    rcases mem_union.mp hd with hd|hu <;> rcases mem_union.mp hb with hb|hv
    · exact False.elim (mem_compl.mp hx (add_mem_add hd hb))
    · exact mem_union_left _ (mem_union_left _ (add_mem_add hd hv))
    · exact mem_union_left _ (mem_union_right _ (add_mem_add hu hb))
    · exact mem_union_right _ (add_mem_add hu hv)
  have h := (card_le_card sub).trans (card_union_le _ _)
  have ab := card_union_le (D+V) (U+B)
  have dv := (card_add_le : (D+V).card≤_).trans (Nat.mul_le_mul_right V.card size)
  have ub := (card_add_le : (U+B).card≤_).trans (Nat.mul_le_mul_left U.card budget)
  have uv : (U+V).card≤U.card*V.card := card_add_le
  change (D+B)ᶜ.card≤k*W.card+W.card^2
  rw [count]
  nlinarith only [h,ab,dv,ub,uv,Nat.zero_le (U.card^2),Nat.zero_le (V.card^2),
    Nat.zero_le (U.card*V.card)]

#print axioms mixed_repair

/-- Large mixed deficits or twice as many total deficits both require √q−4
fresh points. The replacement basis may delete old points and use either parity. -/
theorem repair_bound {v : ℕ+} {q : ℕ} (D B : Finset (ZMod v))
    (size : D.card≤q+1) (budget : B.card≤q+1)
    (loss : (q:ℝ)*Real.sqrt q-2*q≤(D+B)ᶜ.card ∨
      2*(q:ℝ)*Real.sqrt q-2*q≤(split D B+split D B)ᶜ.card)
    (T : Finset (ZMod (2*v.val))) (full : T+T=univ) :
    Real.sqrt (q:ℝ)-4≤(T\split D B).card := by
  let S := split D B
  let w : ℝ := (T\S).card
  let u := Real.sqrt (q:ℝ)
  have wp : 0≤w := Nat.cast_nonneg _
  have qp : (0:ℝ)≤q := Nat.cast_nonneg _
  have uu : u^2=(q:ℝ) := Real.sq_sqrt qp
  change u-4≤w
  by_contra! hw
  have mul := mul_nonneg qp (show 0≤u-4-w by linarith)
  have sq := mul_nonneg (show 0≤u-w by linarith) (show 0≤u+w by linarith)
  rcases loss with mixed|whole
  · have m := mixed_repair D B size budget T full
    have upper : ((D+B)ᶜ.card:ℝ)≤((q:ℝ)+1)*w+w^2 := by dsimp only [w,S];exact_mod_cast m
    change (q:ℝ)*u-2*q≤(D+B)ᶜ.card at mixed
    nlinarith only [upper,mixed,mul,sq,hw,uu,sq_nonneg (u-1),qp]
  · have m := changed_sums T S
    simp only [full,compl_univ,card_empty,zero_add] at m
    have cap := (split_card D B).le
    have total := card_sdiff_add_card T S
    have ts : T.card≤(T∪S).card := card_le_card subset_union_left
    have nt : T.card≤2*(q+1)+(T\S).card := by
      change S.card≤D.card+B.card at cap
      omega
    have real_sz : (T.card:ℝ) ≤ 2*((q:ℝ)+1)+w := by dsimp only [w]; exact_mod_cast nt
    have miss : ((S+S)ᶜ.card:ℝ)≤w*T.card := by dsimp only [w]; exact_mod_cast m
    change 2*(q:ℝ)*u-2*q≤(S+S)ᶜ.card at whole
    have upper := whole.trans (miss.trans (mul_le_mul_of_nonneg_left real_sz wp))
    nlinarith only [upper,mul,sq,hw,uu,sq_nonneg (u-1),qp]

#print axioms repair_bound

open Green33SingerCoordinates Green33SingerProjectiveOverlap in
/-- Uniformly in every opposite layer and replacement ordinary basis in the
binary cubic Singer family, at least √q−4 elements of the basis are fresh. -/
theorem binary_repairs {F K : ℕ→Type*} [∀ i, Field (F i)] [∀ i, Field (K i)]
    [∀ i, Algebra (F i) (K i)] [∀ i, CharP (F i) 2] [∀ i, Fintype (F i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (F i)] (C : ∀ i, CubicFrame (F i) (K i))
    (B : ∀ i, Finset (ZMod (Green33SingerReflectedCoverage.order (F i))))
    (budget : ∀ i, (B i).card=Fintype.card (F i)+1)
    (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    ∀ᶠ i in atTop, ∀ T : Finset (ZMod (2*(Green33SingerReflectedCoverage.order (F i)).val)),
      T+T=univ → Real.sqrt (Fintype.card (F i):ℝ)-4≤
        (T\split (v:=Green33SingerReflectedCoverage.order (F i)) (labels (C i)) (B i)).card := by
  have alt := layer_alternatives (v:=fun i => Green33SingerReflectedCoverage.order (F i))
    _ B (fun i => Green33SingerReflectedCoverage.perfect (C i))
    (fun i => Green33SingerReflectedCoverage.label_card (C i)) budget big
    (fun t => Green33SingerReflectedCoverage.coverage C t big)
  filter_upwards [alt] with i h
  exact repair_bound _ _ (Green33SingerReflectedCoverage.label_card (C i)).le (budget i).le h

#print axioms binary_repairs

open Green33SingerAllCharacteristics Green33SingerKloosterman in
/-- In any characteristic, the same bounds for cubic hyperplanes follow from
the explicitly normalized rank-four Kloosterman estimate. -/
theorem all_characteristics {F K : ℕ→Type*} [∀ i, Field (F i)] [∀ i, Field (K i)]
    [∀ i, Algebra (F i) (K i)] [∀ i, Fintype (F i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (F i)] [∀ i, DecidableEq (K i)]
    (h : ∀ i, Fintype.card (K i)=(Fintype.card (F i))^3)
    (L : ∀ i, K i→ₗ[F i] F i) (onto : ∀ i, Function.Surjective (L i))
    (ψ : ∀ i, AddChar (F i) ℂ) (nt : ∀ i, ψ i≠0) (bound : ∀ i, RankFourBound (L i) (ψ i))
    (B : ∀ i, Finset (ZMod (order (F i)))) (budget : ∀ i, (B i).card=Fintype.card (F i)+1)
    (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    let S i := split (v:=positiveOrder (F i)) (labels (h i) (L i)) (B i)
    ∀ᶠ i in atTop, (Fintype.card (F i):ℝ)*Real.sqrt (Fintype.card (F i))-2*Fintype.card (F i)
      ≤(S i+S i)ᶜ.card ∧ ∀ T, T+T=univ → Real.sqrt (Fintype.card (F i):ℝ)-4≤(T\S i).card := by
  classical
  have sz (i : ℕ) : (labels (h i) (L i)).card=Fintype.card (F i)+1 := by
    rw [labels,card_map,(cubic_parameters (L i) (onto i) (h i)).1]
  have alt := layer_alternatives (v:=fun i => positiveOrder (F i)) _ B
    (fun i => perfect_labels (h i) (L i) (onto i)) sz budget big (coverage h L onto ψ nt bound · big)
  filter_upwards [alt] with i hi
  refine ⟨?_,repair_bound _ _ (sz i).le (budget i).le hi⟩
  rcases hi with mixed|whole
  · exact mixed.trans (by exact_mod_cast odd_holes (v:=positiveOrder (F i)) (labels (h i) (L i)) (B i))
  · nlinarith only [whole,mul_nonneg (Nat.cast_nonneg (α:=ℝ) (Fintype.card (F i))) (Real.sqrt_nonneg (Fintype.card (F i)))]

#print axioms all_characteristics

/-- Every balanced perfect-difference layer meets Green 33's size normalization
in its actual doubled cyclic group, for arbitrary second layers of the same size. -/
theorem balanced_size_limit {v : ℕ→ℕ+} (D B : ∀ i, Finset (ZMod (v i)))
    (perfect : ∀ i, Perfect (D i)) (balanced : ∀ i, (B i).card=(D i).card)
    (big : Tendsto (fun i => (v i).val) atTop atTop) :
    Tendsto (fun i => ((split (D i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2)) := by
  have grow : Tendsto (fun i => Fintype.card (ZMod (v i))) atTop atTop := by simpa only [ZMod.card] using big
  have h := (perfect_size_limit D perfect grow).const_mul (Real.sqrt 2)
  rw [mul_one] at h
  apply h.congr
  intro i
  rw [split_card,balanced i,ZMod.card,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num)]
  have vv : (0:ℝ)<(v i).val := by exact_mod_cast (v i).property
  field_simp [Real.sqrt_ne_zero'.mpr vv,show Real.sqrt 2≠0 by positivity]
  nlinarith only [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]

#print axioms balanced_size_limit

end Green33SingerBlockingLayers
