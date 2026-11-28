import Green53ThresholdRounding
import Green53ThresholdConcentration
import Green52Complements

/-! # Colour classes determined by affine thresholds in a common basis -/

open Finset
open scoped Classical Pointwise
namespace Green53Threshold
private theorem largest {J : Type*} (a : J → ℝ) (s : Finset J) (k : ℕ) :
    ∃ t ⊆ s, t.card = min k s.card ∧ ∀ i∈t, ∀ j∈s, j∉t → a j ≤ a i := by
  classical
  induction k generalizing s with
  | zero => exact ⟨∅,empty_subset _,by simp,by simp⟩
  | succ k ih =>
    rcases s.eq_empty_or_nonempty with rfl|hs
    · exact ⟨∅,by simp,by simp,by simp⟩
    obtain ⟨i,hi,hmax⟩ := s.exists_max_image a hs
    obtain ⟨t,ht,hcard,htop⟩ := ih (s.erase i)
    have no : i∉t := fun mem => notMem_erase i s (ht mem)
    refine ⟨insert i t,insert_subset hi (ht.trans (erase_subset _ _)),?_,?_⟩
    · rw [card_insert_of_notMem no,hcard,card_erase_of_mem hi]
      have := card_pos.mpr hs
      omega
    · intro b hb j hj hnot
      rcases mem_insert.mp hb with rfl|hb
      · exact hmax _ hj
      · exact htop b hb j (mem_erase.mpr ⟨fun h => hnot (h ▸ mem_insert_self i t),hj⟩)
          (fun h => hnot (mem_insert_of_mem h))
private theorem pin_large {J : Type*} (a : J → ℝ) (s : Finset J) (b : ℝ) (h : ℕ) :
    ∃ (t : Finset J) (e : J → ℝ) (M : ℝ), t ⊆ s ∧ t.card ≤ h ∧
      (∀ j, e j=1 ∨ e j= -1) ∧ 0 ≤ M ∧
      (∀ j ∈ s, j∉t → |a j| ≤ M) ∧ (h:ℝ)*M ≤ |b+∑ j∈t, a j*e j| := by
  classical
  obtain ⟨t,sub,card,order⟩ := largest (fun j => |a j|) s h
  let d (y : ℝ) : ℝ := if 0≤y then 1 else -1
  have unit (y : ℝ) : d y=1 ∨ d y= -1 := by by_cases h : 0≤y <;> simp [d,h]
  have mul (y : ℝ) : y*d y=|y| := by by_cases h : 0≤y <;> simp [d,h,abs_of_nonneg,abs_of_neg,lt_of_not_ge]
  let e (j : J) := d (a j)*d b
  have sign_e (j : J) : e j=1 ∨ e j= -1 := by
    rcases unit (a j) with u|u <;> rcases unit b with v|v <;> simp [e,u,v]
  have nonneg : 0 ≤ ∑ j∈t, |a j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have aligned : (∑ j∈t, |a j|) ≤ |b+∑ j∈t, a j*e j| := by
    simp only [e,←mul_assoc,mul,←sum_mul]
    by_cases hb : 0≤b
    · rw [show d b=1 by simp [d,hb],mul_one,abs_of_nonneg (add_nonneg hb nonneg)]; linarith
    · rw [show d b= -1 by simp [d,hb],mul_neg_one,abs_of_nonpos (by linarith)]; linarith
  have le := card.trans_le (min_le_left _ _)
  by_cases hs : (s\t).Nonempty
  · obtain ⟨j,hj,maxj⟩ := (s\t).exists_max_image (fun j => |a j|) hs
    have hj' := mem_sdiff.mp hj
    have lt : t.card<s.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, fun eq => hj'.2 (eq ▸ hj'.1)⟩)
    have eq : t.card=h := by omega
    refine ⟨t,e,|a j|,sub,le,sign_e,abs_nonneg _,fun l hl hlt => maxj l (mem_sdiff.mpr ⟨hl,hlt⟩),?_⟩
    calc
      _ = ∑ _i∈t, |a j| := by simp [eq]
      _ ≤ ∑ i∈t, |a i| := sum_le_sum (fun i hi => order i hi j hj'.1 hj'.2)
      _ ≤ _ := aligned
  · exact ⟨t,e,0,sub,le,sign_e,le_rfl,fun j hj h => (hs ⟨j,mem_sdiff.mpr ⟨hj,h⟩⟩).elim,
        by rw [mul_zero]; exact abs_nonneg _⟩

private def pinCount (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => 2*pinCount c r+c

private theorem stabilize {J : Type*} (c : ℕ) (s : Finset J) {r : ℕ}
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (e : J → ℝ), t ⊆ s ∧ t.card ≤ pinCount c r ∧
      (∀ j, e j=1 ∨ e j= -1) ∧ ∀ i j, j∈s → j∉t →
        (c:ℝ)*|A i j| ≤ |b i+∑ l∈t, A i l*e l| := by
  classical
  induction r generalizing s with
  | zero => exact ⟨∅,fun _ => 1,empty_subset _,by simp [pinCount],by simp,fun i => i.elim0⟩
  | succ r ih =>
    let k := pinCount c r
    obtain ⟨u,f,M,us,uc,fu,hm,bounds,margin⟩ := pin_large (A 0) s (b 0) (k+c)
    obtain ⟨v,g,vs,vc,gu,hmarg⟩ := ih (s\u) (fun i => A i.succ)
      (fun i => b i.succ + ∑ l∈u, A i.succ l*f l)
    let e (j : J) := if j∈u then f j else g j
    have dis : Disjoint u v := Finset.disjoint_left.mpr (by intro j hj hv; exact (mem_sdiff.mp (vs hv)).2 hj)
    have eq (i : Fin (r+1)) : ∑ l∈u∪v, A i l*e l =
        (∑ l∈u,A i l*f l) + ∑ l∈v,A i l*g l := by
      rw [sum_union dis]
      congr 1
      · exact sum_congr rfl (fun j hj => by simp [e,hj])
      · exact sum_congr rfl (fun j hj => by simp [e,(mem_sdiff.mp (vs hj)).2])
    refine ⟨u∪v,e,union_subset us (vs.trans sdiff_subset),?_,?_,?_⟩
    · rw [card_union_of_disjoint dis, pinCount]
      change u.card + v.card ≤ 2*k+c
      change v.card ≤ k at vc
      omega
    · intro j
      by_cases h : j∈u
      · simpa only [e,if_pos h] using fu j
      · simpa only [e,if_neg h] using gu j
    · intro i j hs jnot
      have ju : j∉u := fun hj => jnot (mem_union_left _ hj)
      have jv : j∉v := fun hj => jnot (mem_union_right _ hj)
      rw [eq,←add_assoc]
      refine Fin.cases ?_ (fun i => hmarg i j (mem_sdiff.mpr ⟨hs,ju⟩) jv) i
      have absG : ∀ l, |g l|=1 := fun l => (gu l).elim (fun h => by simp [h]) (fun h => by simp [h])
      have loss : |∑ l∈v, A 0 l*g l| ≤ (k:ℝ)*M := by
        calc
          _ ≤ ∑ l∈v, |A 0 l*g l| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _l∈v, M := sum_le_sum (fun l hl => by
            have h := mem_sdiff.mp (vs hl)
            simpa only [abs_mul,absG,mul_one] using bounds l h.1 h.2)
          _ = (v.card:ℝ)*M := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast vc) hm
      let B := b 0+∑ l∈u, A 0 l*f l
      let G := ∑ l∈v,A 0 l*g l
      have tri : |B| ≤ |B+G| + |G| := by simpa using abs_add_le (B+G) (-G)
      dsimp only [B,G] at tri
      have desired := mul_le_mul_of_nonneg_left (bounds j hs ju) (Nat.cast_nonneg (α:=ℝ) c)
      push_cast at margin
      linarith [add_mul (k:ℝ) (c:ℝ) M]

/-- The maximum absolute weight of the free coordinates, with zero for an empty set. -/
theorem row_cap {J : Type*} (s : Finset J) (a : J → ℝ) :
    ∃ M : ℝ, 0≤M ∧ (∀ j∈s, |a j|≤M) ∧ (M=0 ∨ ∃ j∈s, |a j|=M) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl|hs
  · exact ⟨0,le_rfl,by simp,Or.inl rfl⟩
  obtain ⟨j,h,m⟩ := s.exists_max_image (fun j => |a j|) hs
  exact ⟨_,abs_nonneg _,m,Or.inr ⟨j,h,rfl⟩⟩


/-- Inside any set of signings of density at least `2⁻ˢ`, choose a common signing and
pinned coordinates with a margin in each row. -/
theorem dense_margins {J : Type*} [Fintype J] (r c s : ℕ)
    (G : Finset (J → Bool)) (density : 2^(Fintype.card J) ≤ 2^s*G.card)
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (x : J → Bool), t.card ≤ 2*r*(2^s*r*(c+1))^2 ∧
      x∈G ∧ ∀ i j, j∉t → (c:ℝ)*|A i j| ≤ |b i+∑ l∈t, A i l*signBit (x l)| := by
  classical
  let u := 2^s*r*(c+1)
  let h := 2*u^2
  let n := Fintype.card J
  by_cases enough : h≤n
  · choose top part card order using fun i => largest (fun j => |A i j|) (univ : Finset J) h
    have len (i : Fin r) : (top i).card=h := by
      rw [card i,card_univ]; exact min_eq_left enough
    let t := univ.biUnion top
    have sub (i : Fin r) : top i⊆t := subset_biUnion_of_mem top (mem_univ i)
    have tc : t.card ≤ r*h := by
      calc _ ≤ _ := card_biUnion_le
           _ = _ := by simp [len]
    let U := univ\t
    choose M nonneg cap attained using fun i => row_cap U (A i)
    let a (i : Fin r) (j : J) := if j∈t then A i j else 0
    let bad (i : Fin r) := univ.filter (fun x : J → Bool =>
      0 < M i ∧ |b i+∑ j,a i j*signBit (x j)|≤c*M i)
    have each (i : Fin r) : (bad i).card ≤ 2^(n-h)*((c+1)*(u^2).centralBinom) := by
      by_cases pos : 0<M i
      · obtain h0|⟨j,hj,eq⟩ := attained i
        · linarith
        have large (l) (hl : l∈top i) : M i ≤ |a i l| := by
          have ctop : j∉top i := fun hp => (mem_sdiff.mp hj).2 (sub i hp)
          have ord := order i l hl j (mem_univ _) ctop
          simpa [a,sub i hl,eq] using ord
        have lim := block_small_ball (top i) (a i) (M i) (b i) c pos large
        simpa [bad,pos,len,h,Nat.centralBinom_eq_two_mul_choose] using lim
      · simp [bad,pos]
    have strict : 2^s*(univ.biUnion bad).card < 2^n := by
      calc
        _ ≤ 2^s*(∑ i, (bad i).card) := Nat.mul_le_mul_left _ card_biUnion_le
        _ ≤ 2^s*(∑ _i : Fin r,2^(n-h)*((c+1)*(u^2).centralBinom)) :=
          Nat.mul_le_mul_left _ (sum_le_sum (fun i _ => each i))
        _ = (u*(u^2).centralBinom)*2^(n-h) := by simp [u]; ring
        _ < 2^h*2^(n-h) := (Nat.mul_lt_mul_right (by positivity)).mpr (central_layer_bound u)
        _ = _ := by rw [←pow_add,Nat.add_sub_of_le enough]
    have count : (univ.biUnion bad).card < G.card := by
      by_contra! opp
      exact strict.not_ge ((Nat.mul_le_mul_left (2^s) opp).trans' density)
    obtain ⟨x,hx⟩ := exists_mem_notMem_of_card_lt_card count
    refine ⟨t,x,?_,hx.1,?_⟩
    · simpa [h,u,mul_left_comm,mul_comm,mul_assoc] using tc
    · intro i j hj
      have hj' : j∈U := mem_sdiff.mpr ⟨mem_univ j,hj⟩
      by_cases pos : 0<M i
      · have hi : x∉bad i := fun p => hx.2 (mem_biUnion.mpr ⟨i,mem_univ _,p⟩)
        have ref : (c:ℝ)*M i < |b i+∑ l,a i l*signBit (x l)| := by simpa [bad,pos] using hi
        have sm : (∑ l,a i l*signBit (x l)) = ∑ l∈t,A i l*signBit (x l) := by simp [a,ite_mul,sum_ite_mem]
        rw [sm] at ref
        exact (mul_le_mul_of_nonneg_left (cap i j hj') (Nat.cast_nonneg c)).trans ref.le
      · have zero := (cap i j hj').trans (not_lt.mp pos)
        rw [abs_nonpos_iff.mp zero,abs_zero,mul_zero]; exact abs_nonneg _
  · have gn : G.Nonempty := by
      by_contra! empty
      rw [empty,card_empty,mul_zero] at density
      exact (Nat.pow_pos (by decide) (n:=Fintype.card J)).not_ge density
    obtain ⟨x,hx⟩ := gn
    refine ⟨univ,x,?_,hx,by simp⟩
    have lr : 0<r := by by_contra! hr; have := Nat.eq_zero_of_le_zero hr; simp [h,u,this,n] at enough
    change n≤_
    have := (not_le.mp enough).le
    dsimp only [h,u] at this
    nlinarith [Nat.mul_le_mul_right ((2^s*r*(c+1))^2) lr]


/-- A common signing with a margin in every nonconstant row, by a union bound. -/
private theorem polynomial_margins {J : Type*} [Fintype J] (r c : ℕ)
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (f : J → ℝ), t.card ≤ 2*r*(r*(c+1))^2 ∧
      (∀ j, f j=1 ∨ f j= -1) ∧ ∀ i j, j∉t →
        (c:ℝ)*|A i j| ≤ |b i+∑ l∈t, A i l*f l| := by
  classical
  have density : 2^Fintype.card J ≤ 2^0*(univ : Finset (J → Bool)).card := by simp
  obtain ⟨t,x,card,_,margin⟩ := dense_margins r c 0 univ density A b
  refine ⟨t,fun j => signBit (x j),by simpa using card,?_,margin⟩
  intro j
  cases h : x j <;> simp [signBit,h]

private theorem stable_side {B x m u : ℝ} (hm : 0 ≤ m) (noise : |x| ≤ u*m)
    (margin : (u+1)*m ≤ |B|) : 0 ≤ B+x ↔ 0 ≤ B := by
  rcases eq_or_lt_of_le hm with h|h
  · subst m
    simp only [mul_zero,abs_nonpos_iff] at noise
    simp [noise]
  · have gap : |x| < |B| := by nlinarith
    have bounds := abs_le.mp noise
    by_cases hb : 0 ≤ B
    · rw [abs_of_nonneg hb] at gap
      have := (abs_lt.mp gap).1
      constructor <;> intro <;> linarith
    · rw [abs_of_neg (lt_of_not_ge hb)] at gap
      have := (abs_lt.mp gap).2
      constructor <;> intro <;> linarith

/-- The binary vector recording the weak positive side of each affine test. -/
noncomputable def readings {J : Type*} [Fintype J] {r : ℕ}
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) (x : J → ℝ) : Fin r → Bool :=
  fun i => decide (0 ≤ b i + ∑ j, A i j*x j)

/-- The better of deterministic pinning and the Littlewood–Offord bound. -/
def thresholdCost (r : ℕ) : ℕ := min ((2*r+1)*(2^r-1)) (2*r*(r*(2*r+2))^2)

/-- An explicit degree-five bound, independent of the dimension of the cube. -/
theorem cost_le_polynomial (r : ℕ) : thresholdCost r ≤ 8*r^3*(r+1)^2 := by
  calc
    _ ≤ 2*r*(r*(2*r+2))^2 := min_le_right _ _
    _ = _ := by ring

private theorem best_margins {J : Type*} [Fintype J] {r : ℕ}
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (f : J → ℝ), t.card ≤ thresholdCost r ∧
      (∀ j, f j=1 ∨ f j= -1) ∧ ∀ i j, j∉t →
        ((2*r+1:ℕ):ℝ)*|A i j| ≤ |b i+∑ l∈t,A i l*f l| := by
  classical
  by_cases h : (2*r+1)*(2^r-1) ≤ 2*r*(r*(2*r+2))^2
  · let c := 2*r+1
    obtain ⟨t,f,_,tc,fs,mar⟩ := stabilize c (univ : Finset J) A b
    have count (k : ℕ) : pinCount c k+c = c*2^k := by
      induction k with
      | zero => simp [pinCount]
      | succ k ih => simp only [pinCount,pow_succ]; nlinarith
    have count' := count r
    have positive : 0 < 2^r := pow_pos (by decide) _
    have card : t.card ≤ (2*r+1)*(2^r-1) := by
      change t.card ≤ c*(2^r-1)
      rw [Nat.mul_sub_left_distrib,Nat.mul_one]
      omega
    refine ⟨t,f,?_,fs,fun i j => mar i j (mem_univ j)⟩
    simpa only [thresholdCost,min_eq_left h] using card
  · obtain ⟨t,f,tc,fs,hf⟩ := polynomial_margins r (2*r+1) A b
    refine ⟨t,f,?_,fs,hf⟩
    simpa only [thresholdCost,min_eq_right (not_le.mp h).le,Nat.add_assoc] using tc

/-- Every flip outside a fixed set of coordinates can be realized within the same joint cell. -/
private theorem sign_cell_bounded {J : Type*} [Fintype J] [DecidableEq J] {r : ℕ}
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (y : Fin r → Bool), t.card ≤ thresholdCost r ∧
      ∀ (d : Finset J), Disjoint d t →
        ∃ e : J → ℝ, (∀ j, e j=1 ∨ e j= -1) ∧ readings A b e=y ∧
          readings A b (fun j => if j∈d then -e j else e j)=y := by
  classical
  let c := 2*r+1
  obtain ⟨t,f,tc,fs,mar⟩ := best_margins (r:=r) A b
  let U := univ \ t
  let B (i : Fin r) := b i+∑ j∈t,A i j*f j
  choose M nonneg cap attained using fun i => row_cap U (A i)
  have buffer i : ((2*r:ℕ):ℝ)*M i + M i ≤ |B i| := by
    rcases attained i with h|⟨j,hj,h⟩
    · simp [h]
    · have ref := mar i j (mem_sdiff.mp hj).2
      rw [h] at ref
      simpa [B,c,Nat.cast_add,add_mul] using ref
  refine ⟨t,fun i => decide (0 ≤ B i),tc,?_⟩
  intro d dis
  have du : d⊆U := fun j hj => mem_sdiff.mpr ⟨mem_univ _,fun h => Finset.disjoint_left.mp dis hj h⟩
  obtain ⟨g,gs,loss⟩ := two_signs A U d du M nonneg cap
  let x (j : J) := if j∈t then f j else g j
  have cut : (univ : Finset J)=t∪U := (union_sdiff_of_subset (subset_univ t)).symm
  have sep : Disjoint t U := disjoint_sdiff
  have split (w w' : J → ℝ) (p : ∀ j∈t, w j = f j) (h : ∀ j∈U,w j=w' j) (i : Fin r) :
      b i+∑ j,A i j*w j = B i+∑ j∈U,A i j*w' j := by
    conv_lhs => rw [cut,sum_union sep]
    rw [←add_assoc]
    have ep : ∑ j∈t,A i j*w j = ∑ j∈t,A i j*f j := sum_congr rfl (fun j hj => by rw [p j hj])
    have ef : ∑ j∈U,A i j*w j = ∑ j∈U,A i j*w' j := sum_congr rfl (fun j hj => by rw [h j hj])
    rw [ep,ef]
  have pin j (hj : j∈t) : x j=f j := by simp [x,hj]
  have free j (hj : j∈U) : x j=g j := by simp [x,(mem_sdiff.mp hj).2]
  refine ⟨x,fun j => ?_,?_,?_⟩
  · by_cases h : j∈t
    · simpa only [x,if_pos h] using fs j
    · simpa only [x,if_neg h] using gs j
  · funext i
    apply decide_eq_decide.mpr
    rw [split x g pin free i]
    apply stable_side (nonneg i) (loss i).1
    simpa only [add_mul,one_mul] using buffer i
  · funext i
    apply decide_eq_decide.mpr
    let v (j : J) := if j∈d then -x j else x j
    let w (j : J) := if j∈d then -g j else g j
    have p j (hj : j∈t) : v j=f j := by
      have h : j∉d := fun hd => Finset.disjoint_left.mp dis hd hj
      simp [v,h,pin j hj]
    have h j (hj : j∈U) : v j=w j := by simp [v,w,free j hj]
    rw [split v w p h i]
    apply stable_side (nonneg i) (loss i).2
    simpa only [add_mul,one_mul] using buffer i

theorem sign_cell {J : Type*} [Fintype J] [DecidableEq J] {r : ℕ}
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (y : Fin r → Bool), t.card ≤ (2*r+1)*(2^r-1) ∧
      ∀ (d : Finset J), Disjoint d t →
        ∃ e : J → ℝ, (∀ j, e j=1 ∨ e j= -1) ∧ readings A b e=y ∧
          readings A b (fun j => if j∈d then -e j else e j)=y := by
  obtain ⟨t,y,size,cell⟩ := sign_cell_bounded A b
  exact ⟨t,y,size.trans (min_le_left _ _),cell⟩

open Green52Complements
/-- The real sign assigned to a binary coordinate. -/
def spin (v : ZMod 2) : ℝ := if v=0 then 1 else -1

/-- Translating a binary coordinate flips its sign exactly when the shift is nonzero. -/
theorem spin_add (u v : ZMod 2) :
    spin (u+v) = if v≠0 then -spin u else spin u := by
  have binary : ∀ x : ZMod 2, x=0 ∨ x=1 := by decide
  have two : (1:ZMod 2)+1=0 := by decide
  rcases binary u with rfl|rfl <;> rcases binary v with rfl|rfl <;> norm_num [spin,two]
  decide

/-- A joint threshold cell realizes every difference vanishing on the selected coordinates. -/
private theorem coordinate_differences_bounded {n r : ℕ} (A : Fin r → Fin n → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset (Fin n)) (y : Fin r → Bool), t.card ≤ thresholdCost r ∧
      ∀ z : Cube n, (∀ j∈t,z j=0) →
        z ∈ {x : Cube n | readings A b (fun j => spin (x j))=y} +
          {x : Cube n | readings A b (fun j => spin (x j))=y} := by
  classical
  obtain ⟨t,y,size,cell⟩ := sign_cell_bounded A b
  refine ⟨t,y,size,?_⟩
  intro z zero
  let d := univ.filter (fun j => z j≠0)
  have dis : Disjoint d t := Finset.disjoint_left.mpr (by
    intro j hd ht; exact (mem_filter.mp hd).2 (zero j ht))
  obtain ⟨e,se,first,second⟩ := cell d dis
  let x (j : Fin n) : ZMod 2 := if e j=1 then 0 else 1
  have sides (j : Fin n) : spin (x j)=e j := by
    rcases se j with h|h <;> norm_num [spin,x,h]
  have toggle (j : Fin n) : spin (x j+z j)=(if j∈d then -e j else e j) := by
    simp [spin_add,sides,d]
  refine ⟨x,?_,x+z,?_,?_⟩
  · simpa only [Set.mem_ofPred_eq,sides] using first
  · simpa only [Set.mem_ofPred_eq,Pi.add_apply,toggle] using second
  · funext j
    exact (by decide : ∀ u v : ZMod 2, u+(u+v)=v) (x j) (z j)

theorem coordinate_differences {n r : ℕ} (A : Fin r → Fin n → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset (Fin n)) (y : Fin r → Bool), t.card ≤ (2*r+1)*(2^r-1) ∧
      ∀ z : Cube n, (∀ j∈t,z j=0) →
        z ∈ {x : Cube n | readings A b (fun j => spin (x j))=y} +
          {x : Cube n | readings A b (fun j => spin (x j))=y} := by
  obtain ⟨t,y,size,cover⟩ := coordinate_differences_bounded A b
  exact ⟨t,y,size.trans (min_le_left _ _),cover⟩

/-- In any common linear basis, every readout of r thresholds has a colour whose
double contains a linear subspace of codimension at most the smaller of the two bounds. -/
theorem threshold_subspace_bound {n r : ℕ} {C : Type*}
    (A : Fin r → Fin n → ℝ) (b : Fin r → ℝ) (L : Cube n ≃ₗ[ZMod 2] Cube n)
    (colour : (Fin r → Bool) → C) :
    ∃ (i : C) (W : Submodule (ZMod 2) (Cube n)),
      n ≤ Module.finrank (ZMod 2) W + thresholdCost r ∧
      (W : Set (Cube n)) ⊆
        {x | colour (readings A b (fun j => spin (L x j)))=i} +
        {x | colour (readings A b (fun j => spin (L x j)))=i} := by
  classical
  obtain ⟨t,y,size,cover⟩ := coordinate_differences_bounded A b
  let P : Cube n →ₗ[ZMod 2] (t → ZMod 2) := LinearMap.pi (fun i => LinearMap.proj i.val)
  let H := P.comp L.toLinearMap
  refine ⟨colour y,H.ker,?_,?_⟩
  · have eq := H.finrank_range_add_finrank_ker
    have bound := Submodule.finrank_le (LinearMap.range H)
    have dom : Module.finrank (ZMod 2) (Cube n)=n := by simp [Cube]
    have ran : Module.finrank (ZMod 2) (t → ZMod 2)=t.card := by simp
    rw [dom] at eq
    rw [ran] at bound
    omega
  · intro z hz
    have zero (j : Fin n) (hj : j∈t) : L z j=0 :=
      congrFun (LinearMap.mem_ker.mp hz) (⟨j,hj⟩ : t)
    obtain ⟨x,hx,w,hw,add⟩ := cover (L z) zero
    change readings A b (fun j => spin (x j))=y at hx
    change readings A b (fun j => spin (w j))=y at hw
    refine ⟨L.symm x,?_,L.symm w,?_,?_⟩
    · simp only [Set.mem_ofPred_eq,LinearEquiv.apply_symm_apply,hx]
    · simp only [Set.mem_ofPred_eq,LinearEquiv.apply_symm_apply,hw]
    · apply L.injective; simpa only [map_add,LinearEquiv.apply_symm_apply] using add

theorem threshold_subspace {n r : ℕ} {C : Type*}
    (A : Fin r → Fin n → ℝ) (b : Fin r → ℝ) (L : Cube n ≃ₗ[ZMod 2] Cube n)
    (colour : (Fin r → Bool) → C) :
    ∃ (i : C) (W : Submodule (ZMod 2) (Cube n)),
      n ≤ Module.finrank (ZMod 2) W + (2*r+1)*(2^r-1) ∧
      (W : Set (Cube n)) ⊆
        {x | colour (readings A b (fun j => spin (L x j)))=i} +
        {x | colour (readings A b (fun j => spin (L x j)))=i} := by
  obtain ⟨i,W,dim,sub⟩ := threshold_subspace_bound A b L colour
  exact ⟨i,W,dim.trans (Nat.add_le_add_left (min_le_left _ _) _),sub⟩

/-- The Green 53 partition conclusion for colourings depending on a bounded
number of threshold tests in any single basis. -/
theorem threshold_partition_green53 (rows : ℕ → ℕ) :
    ∃ c : ℕ → ℕ, ∀ (n k : ℕ) (as : Fin k → Set (Cube n)),
      (⋃ i, as i) = Set.univ → Pairwise (fun i j => Disjoint (as i) (as j)) →
      (∃ (A : Fin (rows k) → Fin n → ℝ) (b : Fin (rows k) → ℝ)
          (L : Cube n ≃ₗ[ZMod 2] Cube n) (colour : (Fin (rows k) → Bool) → Fin k),
        ∀ i, as i={x | colour (readings A b (fun j => spin (L x j)))=i}) →
      ∃ i, Flat n (c k) (as i) := by
  refine ⟨fun k => thresholdCost (rows k),?_⟩
  rintro n k as _ _ ⟨A,b,L,colour,classes⟩
  obtain ⟨i,W,dim,sub⟩ := threshold_subspace_bound A b L colour
  refine ⟨i,W.toAffineSubspace,?_,?_⟩
  · rw [classes]; exact sub
  · rw [Submodule.toAffineSubspace_direction]
    exact dim

/-- In dimension r, r coordinate thresholds have singleton joint cells.
Any bound valid for every readout of r rows must therefore be at least r. -/
theorem coordinate_lower (r : ℕ) :
    ∃ (A : Fin r → Fin r → ℝ) (b : Fin r → ℝ),
      ∀ y : Fin r → Bool, ∀ W : Submodule (ZMod 2) (Cube r),
        (W : Set (Cube r)) ⊆
          {x | readings A b (fun j => spin (x j))=y} +
          {x | readings A b (fun j => spin (x j))=y} →
        Module.finrank (ZMod 2) W=0 := by
  classical
  let A (i j : Fin r) : ℝ := if i=j then 1 else 0
  let key (x : Cube r) := readings A 0 (fun j => spin (x j))
  have get (x : Cube r) (i : Fin r) : key x i = decide (x i=0) := by
    simp only [key,readings,A,Pi.zero_apply,ite_mul,one_mul,zero_mul,
      Finset.sum_ite_eq,mem_univ,if_true,zero_add]
    by_cases h : x i=0 <;> norm_num [spin,h]
  have inj : Function.Injective key := by
    intro x z eq
    funext i
    have same := congrFun eq i
    rw [get,get] at same
    have bi := decide_eq_decide.mp same
    have binary : ∀ a : ZMod 2, a=0 ∨ a=1 := by decide
    rcases binary (x i) with h|h <;> rcases binary (z i) with h'|h' <;> simp_all
  refine ⟨A,0,?_⟩
  intro y W sub
  have bot : W=⊥ := eq_bot_iff.mpr (by
    intro w hw
    obtain ⟨x,hx,z,hz,eq⟩ := sub hw
    have same : key x=key z := (show key x=y from hx).trans (show key z=y from hz).symm
    have xz := inj same
    subst z; subst w
    change x+x=0
    funext i
    exact (by decide : ∀ a : ZMod 2, a+a=0) (x i))
  simp [bot]

end Green53Threshold

#print axioms Green53Threshold.dense_margins

#print axioms Green53Threshold.sign_cell
#print axioms Green53Threshold.coordinate_differences
#print axioms Green53Threshold.threshold_subspace
#print axioms Green53Threshold.cost_le_polynomial
#print axioms Green53Threshold.threshold_subspace_bound
#print axioms Green53Threshold.coordinate_lower
#print axioms Green53Threshold.threshold_partition_green53
