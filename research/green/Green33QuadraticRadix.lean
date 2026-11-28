import Green33StrictReduction
import Green33Divergence
import Mathlib.NumberTheory.Bertrand

/-! Cyclic lifts with a quadratic correction from the preceding digit. -/

open Finset
open scoped Pointwise

namespace Green33QuadraticRadix

/-- The high half of a base-q² digit tests the squares of the preceding coordinates. -/
def block (p q s i prev t : ℕ) : ℕ :=
  (s+i*q)*t + q*(prev^2 % p)

/-- Base-q² encoding before reduction modulo its d-digit modulus. -/
def encode (p q s i : ℕ) : (d prev : ℕ) → (Fin d → Fin (q+s)) → ℕ
  | 0, _, _ => 0
  | d+1, prev, t => block p q s i prev (t 0) + q^2 * encode p q s i d (t 0) (Fin.tail t)

/-- Equality of the high quotient disambiguates an unreduced low digit. -/
private lemma strip {B d x y X Y : ℕ} (hB : 0 < B)
    (h : x+B*X ≡ y+B*Y [MOD B^(d+1)]) (bucket : x/B=y/B) :
    x=y ∧ X ≡ Y [MOD B^d] := by
  have low := h.of_dvd (dvd_pow_self B (Nat.succ_ne_zero d))
  have rem : x%B=y%B := by simpa [Nat.ModEq,Nat.add_mod] using low
  have eq : x=y := by
    calc
      x = x%B+B*(x/B) := (Nat.mod_add_div ..).symm
      _ = y%B+B*(y/B) := by rw [rem,bucket]
      _ = y := Nat.mod_add_div ..
  subst y
  rw [pow_succ'] at h
  exact ⟨rfl,Nat.ModEq.mul_left_cancel' hB.ne' (Nat.ModEq.add_left_cancel' x h)⟩

/-- Over an odd prime field the sum and sum of squares determine an unordered pair. -/
theorem quadratic_pair {q : ℕ} [Fact q.Prime] (hq : 2 < q) (a b c d : ZMod q)
    (hs : a+b=c+d) (hm : a^2+b^2=c^2+d^2) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have h₂ : (2 : ZMod q) ≠ 0 := by
    rw [← Nat.cast_two,ne_eq,ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) hq
  have hb : b=c+d-a := by linear_combination hs
  rw [hb] at hm
  have prod : 2*((a-c)*(a-d))=0 := by linear_combination hm
  rcases mul_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left h₂) with hc|hd
  · exact Or.inl ⟨sub_eq_zero.mp hc,by linear_combination hs-hc⟩
  · exact Or.inr ⟨sub_eq_zero.mp hd,by linear_combination hs-hd⟩

/-- Distinct arms still cover the whole d-digit modulus. Their earlier
coordinates merely translate the target for the next pair of progressions. -/
theorem twisted_pair (p : ℕ) {q s i j l : ℕ} (hs : 0<s) (hij : i<j) (gap : j-i ∣ s)
    (hq : s*l+1=q) (d : ℕ) (a b : ℕ) (z : ℤ) :
    ∃ t u : Fin d → Fin (q+s), ∃ e : ℤ,
      z = encode p q s i d a t + (encode p q s j d b u : ℤ) + ((q:ℤ)^2)^d*e := by
  obtain ⟨h,hdh⟩ := gap
  have hd : 0<j-i := Nat.sub_pos_of_lt hij
  have hh : 0<h := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hdh; omega
  have hhs : h ≤ s := hdh ▸ Nat.le_mul_of_pos_left h hd
  have hi : (i:ℤ)+((j-i:ℕ):ℤ)=j := by exact_mod_cast Nat.add_sub_of_le hij.le
  induction d generalizing a b z with
  | zero => exact ⟨Fin.elim0,Fin.elim0,z,by simp [encode]⟩
  | succ d ih =>
    let off := q*(a^2%p)+q*(b^2%p)
    obtain ⟨x,y,hx,hxq,hy,hyq,e,he⟩ := Green33StrictCoverLift.pair_lifts s i (j-i : ℕ) h q l
      (z-(off:ℤ)) (by exact_mod_cast hs) (by exact_mod_cast hh) (by exact_mod_cast hhs)
      (by exact_mod_cast hdh.symm) (by exact_mod_cast (by omega : 0<q)) (by exact_mod_cast hq)
    rw [hi] at he
    let X : Fin (q+s) := ⟨x.toNat,by omega⟩
    let Y : Fin (q+s) := ⟨y.toNat,by omega⟩
    obtain ⟨t,u,f,hf⟩ := ih X Y e
    refine ⟨Fin.cons X t,Fin.cons Y u,f,?_⟩
    simp only [encode,Fin.cons_zero,Fin.tail_cons,block,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Int.natCast_emod]
    rw [pow_succ ((q:ℤ)^2) d]
    have hX : (X.val:ℤ)=x := Int.toNat_of_nonneg hx
    have hY : (Y.val:ℤ)=y := Int.toNat_of_nonneg hy
    dsimp [off] at he
    rw [hX,hY]
    linear_combination he+(q:ℤ)^2*hf

private lemma quot_rem_eq {q a b : ℕ} (hq : a/q=b/q) (hr : a%q=b%q) : a=b := by
  calc
    a = a%q+q*(a/q) := (Nat.mod_add_div ..).symm
    _ = b%q+q*(b/q) := by rw [hq,hr]
    _ = b := Nat.mod_add_div ..

private lemma same_total {p q s i j a b a' b' t u t' u' : ℕ}
    (unit : IsUnit (s : ZMod q))
    (hb : block p q s i a t + block p q s j b u = block p q s i a' t' + block p q s j b' u')
    (hbucket : (t+u)/q=(t'+u')/q) : t+u=t'+u' := by
  have he := congrArg (fun x : ℕ => (x : ZMod q)) hb
  simp [block] at he
  have ht : (t : ZMod q)+u=(t' : ZMod q)+u' := by
    apply unit.mul_left_cancel
    simpa [mul_add] using he
  apply quot_rem_eq hbucket
  exact (ZMod.natCast_eq_natCast_iff' (t+u) (t'+u') q).mp (by simpa using ht)

private lemma square_signature {q a b c d : ℕ} [Fact q.Prime] (hq : 2<q)
    (sum : a+b=c+d) (sqsum : a^2%q+b^2%q=c^2%q+d^2%q)
    (bit : (a%q ≤ b%q) ↔ (c%q ≤ d%q)) (quot : a/q=c/q) : a=c ∧ b=d := by
  have hsum := congrArg (fun n : ℕ => (n : ZMod q)) sum
  have hs := congrArg (fun n : ℕ => (n : ZMod q)) sqsum
  simp only [Nat.cast_add,ZMod.natCast_mod,Nat.cast_pow] at hsum hs
  obtain ⟨h₁,_⟩|⟨h₂,h₃⟩ := quadratic_pair hq _ _ _ _ hsum hs
  · have he := quot_rem_eq quot ((ZMod.natCast_eq_natCast_iff' _ _ q).mp h₁)
    omega
  · have hd := (ZMod.natCast_eq_natCast_iff' _ _ q).mp h₂
    have hc := (ZMod.natCast_eq_natCast_iff' _ _ q).mp h₃
    have he := quot_rem_eq quot (show a%q=c%q by omega)
    omega

private abbrev Word (q s d : ℕ) := Fin d → Fin (q+s)

private def sums (p q s i j : ℕ) : (d a b : ℕ) → Word q s d → Word q s d → Fin d → ℕ
  | 0, _, _, _, _ => Fin.elim0
  | d+1, a, b, t, u => Fin.cons (block p q s i a (t 0)+block p q s j b (u 0))
      (sums p q s i j d (t 0) (u 0) (Fin.tail t) (Fin.tail u))

private def last {q s : ℕ} : (d prev : ℕ) → Word q s d → ℕ
  | 0, prev, _ => prev
  | d+1, _, t => last d (t 0) (Fin.tail t)

private lemma aligned {p q s i j : ℕ} (hq : 0 < q) (d a b a' b' : ℕ)
    (t u t' u' : Word q s d)
    (code : ∀ h, sums p q s i j d a b t u h/q^2=sums p q s i j d a' b' t' u' h/q^2)
    (res : encode p q s i d a t+encode p q s j d b u ≡
      encode p q s i d a' t'+encode p q s j d b' u' [MOD (q^2)^d]) :
    ∀ h, sums p q s i j d a b t u h=sums p q s i j d a' b' t' u' h := by
  induction d generalizing a b a' b' with
  | zero => intro h; exact h.elim0
  | succ d ih =>
    simp only [encode,show ∀ x X y Y : ℕ, x+q^2*X+(y+q^2*Y)=x+y+q^2*(X+Y) by intros; ring] at res
    have c := code 0
    simp only [sums,Fin.cons_zero] at c
    obtain ⟨low,tail⟩ := strip (by positivity : 0 < q^2) res c
    exact Fin.cases low (ih _ _ _ _ _ _ _ _ (fun h => by
      simpa only [sums,Fin.cons_succ] using code h.succ) tail)

private def Mark (k width : ℕ) := Fin (4*k+7) × Fin 4 × Fin width × Bool
private instance (k width : ℕ) : Fintype (Mark k width) := inferInstanceAs (Fintype (_ × _ × _ × Bool))

private lemma block_le {p q s : ℕ} (hp : 0<p) (hpq : p≤q) (hs : s < q) (k : ℕ) (i : Fin k) (a : ℕ) (t : Fin (q+s)) :
    block p q s i a t ≤ (2*k+3)*q^2 := by
  have hq : 0 < q := by omega
  have ht : t.val ≤ 2*q := by have := t.isLt; omega
  have hw : s+i.val*q ≤ (k+1)*q := by
    have h := Nat.mul_le_mul_right q i.isLt.le
    nlinarith only [h,hs]
  have hm := (Nat.mod_lt (a^2) hp).le.trans hpq
  dsimp [block]
  calc
    _ ≤ (k+1)*q*(2*q)+q*q := Nat.add_le_add (Nat.mul_le_mul hw ht) (Nat.mul_le_mul_left q hm)
    _ = _ := by ring

private def mark {p q s k d width : ℕ} (hp : 0<p) (wide : q+s ≤ width*p) (hs : s < q) (i j : Fin k) (a b : ℕ)
    (t u : Word q s d) (h : Fin d) : Mark k width :=
  (⟨(sums p q s i j d a b t u h/q^2)%(4*k+7),Nat.mod_lt _ (by omega)⟩,
   ⟨((t h).val+(u h).val)/q,Nat.div_lt_iff_lt_mul (by omega) |>.mpr (by have := (t h).isLt; have := (u h).isLt; omega)⟩,
   ⟨(t h).val/p,(Nat.div_lt_iff_lt_mul hp).mpr ((t h).isLt.trans_le wide)⟩,
   decide ((t h).val%p ≤ (u h).val%p))

private lemma sums_le {p q s k : ℕ} (hp : 0<p) (hpq : p≤q) (hs : s < q) (i j : Fin k) (d a b : ℕ) (t u : Word q s d) :
    ∀ h, sums p q s i j d a b t u h ≤ (4*k+6)*q^2 := by
  induction d generalizing a b with
  | zero => intro h; exact h.elim0
  | succ d ih =>
    apply Fin.cases
    · simp only [sums,Fin.cons_zero]
      linarith only [block_le hp hpq hs k i a (t 0),block_le hp hpq hs k j b (u 0)]
    · exact ih _ _ _ _

private lemma head_mixed {p q s i j a b t u t' u' : ℕ} (hq : 0 < q) (ne : i ≠ j)
    (sum : t+u=t'+u') (raw : block p q s i a t+block p q s j b u=block p q s i a t'+block p q s j b u') :
    t=t' ∧ u=u' := by
  have raw' : ((s:ℤ)+i*q)*t+((s:ℤ)+j*q)*u=((s:ℤ)+i*q)*t'+((s:ℤ)+j*q)*u' := by
    dsimp [block] at raw
    exact_mod_cast (show (s+i*q)*t+(s+j*q)*u=(s+i*q)*t'+(s+j*q)*u' by omega)
  have sum' : (t:ℤ)+u=t'+u' := by exact_mod_cast sum
  have prod : ((i:ℤ)-j)*q*((t:ℤ)-t')=0 := by
    linear_combination raw'-((s:ℤ)+j*q)*sum'
  have ni : ((i:ℤ)-j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne)
  have nq : (q:ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have h := sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left (mul_ne_zero ni nq))
  omega

private lemma recover {p q s : ℕ} [Fact p.Prime] (hp : 2<p) (hq : 0<q) (unit : IsUnit (s : ZMod q))
    (i j d a b : ℕ) (t u t' u' : Word q s d)
    (raw : ∀ h, sums p q s i j d a b t u h=sums p q s i j d a b t' u' h)
    (addQ : ∀ h, ((t h).val+(u h).val)/q=((t' h).val+(u' h).val)/q)
    (order : ∀ h, ((t h).val%p ≤ (u h).val%p) ↔ ((t' h).val%p ≤ (u' h).val%p))
    (top : ∀ h, (t h).val/p=(t' h).val/p) (endEq : last d a t=last d a t') :
    t=t' ∧ u=u' := by
  induction d generalizing a b with
  | zero => exact ⟨Subsingleton.elim ..,Subsingleton.elim ..⟩
  | succ d ih =>
    have head := raw 0
    simp only [sums,Fin.cons_zero] at head
    have sum := same_total unit head (addQ 0)
    have htu : (t 0).val=(t' 0).val ∧ (u 0).val=(u' 0).val := by
      by_cases ne : i≠j
      · exact head_mixed (by omega) ne sum head
      · have ij := not_ne_iff.mp ne
        subst j
        cases d with
        | zero =>
          change (t 0).val=(t' 0).val at endEq
          omega
        | succ d =>
          have next := raw (0 : Fin (d+1)).succ
          simp only [sums,Fin.cons_succ,Fin.cons_zero] at next
          have sn := same_total unit next (addQ (0 : Fin (d+1)).succ)
          have e : (t 0).val^2%p+(u 0).val^2%p=(t' 0).val^2%p+(u' 0).val^2%p := by
            dsimp [block] at next
            change ((Fin.tail t 0).val+(Fin.tail u 0).val)=
              ((Fin.tail t' 0).val+(Fin.tail u' 0).val) at sn
            apply Nat.eq_of_mul_eq_mul_left (by omega : 0<q)
            nlinarith only [next, congrArg (fun z => (s+i*q)*z) sn]
          exact square_signature hp sum e (order 0) (top 0)
    obtain ⟨ht,hu⟩ := htu
    have rr (h : Fin d) := raw h.succ
    simp only [sums,Fin.cons_succ] at rr
    rw [←ht,←hu] at rr
    change last d (t 0).val (Fin.tail t)=last d (t' 0).val (Fin.tail t') at endEq
    rw [←ht] at endEq
    obtain ⟨tails,tailu⟩ := ih _ _ (Fin.tail t) (Fin.tail u) (Fin.tail t') (Fin.tail u') rr
      (fun h => addQ h.succ) (fun h => order h.succ) (fun h => top h.succ) endEq
    exact ⟨funext (Fin.cases (Fin.ext ht) (congrFun tails)),funext (Fin.cases (Fin.ext hu) (congrFun tailu))⟩

private lemma last_lt {q s : ℕ} (d : ℕ) (a : ℕ) (ha : a<q+s) (t : Word q s d) :
    last d a t < q+s := by
  induction d generalizing a with
  | zero => exact ha
  | succ d ih => exact ih _ (t 0).isLt _

private lemma mark_injective {p q s k d width : ℕ} [Fact p.Prime] (hp : 2<p) (hpq : p≤q)
    (unit : IsUnit (s : ZMod q)) (hsq : s<q) (wide : q+s ≤ width*p)
    (i j : Fin k) (t u t' u' : Word q s d)
    (res : encode p q s i d 0 t+encode p q s j d 0 u ≡
      encode p q s i d 0 t'+encode p q s j d 0 u' [MOD (q^2)^d])
    (tag : mark (by omega) wide hsq i j 0 0 t u = mark (by omega) wide hsq i j 0 0 t' u')
    (finalDigit : last d 0 t=last d 0 t') : t=t' ∧ u=u' := by
  have hq : 0 < q := by omega
  have bound (t u : Word q s d) (h) : sums p q s i j d 0 0 t u h/q^2 < 4*k+7 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    have hpos : 0<q^2 := by positivity
    nlinarith only [sums_le (by omega) hpq hsq i j d 0 0 t u h,hpos]
  have first (h) := congrArg (fun z : Mark k width => z.1.val) (congrFun tag h)
  simp only [mark,Nat.mod_eq_of_lt (bound _ _ _)] at first
  apply recover hp (by omega) unit i j d 0 0 _ _ _ _ (aligned (by omega) d 0 0 0 0 _ _ _ _ first res)
  · exact fun h => congrArg (fun z : Mark k width => z.2.1.val) (congrFun tag h)
  · intro h
    have eq := congrArg (fun z : Mark k width => z.2.2.2) (congrFun tag h)
    simpa only [mark,decide_eq_decide] using eq
  · exact fun h => congrArg (fun z : Mark k width => z.2.2.1.val) (congrFun tag h)
  · exact finalDigit

open Green33StrictReduction Green33Multiplicity

private def modulus (M : ℕ+) (q d : ℕ) (hq : 0<q) : ℕ+ :=
  ⟨M.val*(q^2)^d,Nat.mul_pos M.pos (pow_pos (pow_pos hq _) _)⟩

private abbrev Param (k q s d : ℕ) := Fin k × Word q s d

private def value (primeMod : ℕ) {M : ℕ+} {k q s d : ℕ} (label : Fin k → ZMod M) (p : Param k q s d) : ℕ :=
  (label p.1).val+M.val*encode primeMod q s p.1 d 0 p.2

private def lift (primeMod : ℕ) {M : ℕ+} {k : ℕ} (label : Fin k → ZMod M) (q s d : ℕ) (hq : 0<q) :
    Finset (ZMod (modulus M q d hq)) :=
  univ.image (fun p : Param k q s d => (value primeMod label p : ZMod (modulus M q d hq)))

private lemma quotient_res (primeMod : ℕ) {M : ℕ+} {k q s d : ℕ} (label : Fin k → ZMod M) (hq : 0<q)
    (i j : Fin k) (t u t' u' : Word q s d)
    (he : ((value primeMod label (i,t)+value primeMod label (j,u) : ℕ) : ZMod (modulus M q d hq)) =
      ((value primeMod label (i,t')+value primeMod label (j,u') : ℕ) : ZMod (modulus M q d hq))) :
    encode primeMod q s i d 0 t+encode primeMod q s j d 0 u ≡
      encode primeMod q s i d 0 t'+encode primeMod q s j d 0 u' [MOD (q^2)^d] := by
  have h := (ZMod.natCast_eq_natCast_iff ..).mp he
  change _ ≡ _ [MOD M.val*(q^2)^d] at h
  simp only [value,show ∀ a x b y : ℕ, a+M.val*x+(b+M.val*y)=(a+b)+M.val*(x+y) by intros; ring] at h
  exact Nat.ModEq.mul_left_cancel' M.pos.ne' (Nat.ModEq.add_left_cancel' _ h)

private lemma lift_cap {M : ℕ+} {k primeMod q s d width : ℕ} [Fact primeMod.Prime] (label : Fin k → ZMod M)
    (hp : 2<primeMod) (hpq : primeMod≤q) (unit : IsUnit (s : ZMod q))
    (hsq : s<q) (wide : q+s ≤ width*primeMod) :
    maxReps (lift primeMod label q s d (by omega)) ≤ k^2*((8*width)*(4*k+7))^d*(q+s) := by
  classical
  let N := modulus M q d (by omega)
  let A := lift primeMod label q s d (by omega)
  apply Finset.sup_le
  intro z _
  let X := (A ×ˢ A).filter fun r => r.1+r.2=z
  let P := Param k q s d
  have choice (x : ↥A) : ∃ p : P, (value primeMod label p : ZMod N)=x.val := by
    obtain ⟨p,_,hp⟩ := mem_image.mp x.property
    exact ⟨p,hp⟩
  let elem (x : ↥A) : P := (choice x).choose
  have spec (x : ↥A) : (value primeMod label (elem x) : ZMod N)=x.val := (choice x).choose_spec
  let left (r : ↥X) := elem ⟨r.val.1,(mem_product.mp (mem_filter.mp r.property).1).1⟩
  let right (r : ↥X) := elem ⟨r.val.2,(mem_product.mp (mem_filter.mp r.property).1).2⟩
  have lspec (r : ↥X) : (value primeMod label (left r) : ZMod N)=r.val.1 :=
    spec ⟨_,(mem_product.mp (mem_filter.mp r.property).1).1⟩
  have rspec (r : ↥X) : (value primeMod label (right r) : ZMod N)=r.val.2 :=
    spec ⟨_,(mem_product.mp (mem_filter.mp r.property).1).2⟩
  have he (r : ↥X) : ((value primeMod label (left r)+value primeMod label (right r) : ℕ) : ZMod N)=z := by
    rw [Nat.cast_add,lspec,rspec]; exact (mem_filter.mp r.property).2
  let code (r : ↥X) : (Fin k × Fin k) × (Fin d → Mark k width) × Fin (q+s) :=
    let l := left r; let h := right r
    ((l.1,h.1),mark (by omega) wide hsq l.1 h.1 0 0 l.2 h.2,⟨last d 0 l.2,last_lt d 0 (by omega) l.2⟩)
  have inj : Function.Injective code := by
    intro x y eq
    have hi := congrArg (fun v => v.1.1) eq
    have hj := congrArg (fun v => v.1.2) eq
    have tags := congrArg (fun v => v.2.1) eq
    have ends := congrArg (fun v => v.2.2.val) eq
    have hxy := (he x).trans (he y).symm
    obtain ⟨i,t,hil⟩ : ∃ i t, left x=(i,t) := ⟨_,_,rfl⟩
    obtain ⟨j,u,hjr⟩ : ∃ j u, right x=(j,u) := ⟨_,_,rfl⟩
    obtain ⟨i',t',hil'⟩ : ∃ i' t', left y=(i',t') := ⟨_,_,rfl⟩
    obtain ⟨j',u',hjr'⟩ : ∃ j' u', right y=(j',u') := ⟨_,_,rfl⟩
    simp only [code,hil,hjr,hil',hjr'] at hi hj tags ends hxy
    subst i'; subst j'
    obtain ⟨rfl,rfl⟩ := mark_injective hp hpq unit hsq wide i j _ _ _ _
      (quotient_res primeMod label (by omega) i j _ _ _ _ hxy) tags ends
    apply Subtype.ext
    apply Prod.ext
    · calc
        x.val.1 = (value primeMod label (left x) : ZMod N) := (lspec x).symm
        _ = _ := by rw [hil,←hil']; exact lspec y
    · calc
        x.val.2 = (value primeMod label (right x) : ZMod N) := (rspec x).symm
        _ = _ := by rw [hjr,←hjr']; exact rspec y
  have bound := Fintype.card_le_of_injective code inj
  change X.card ≤ _
  simpa [Mark,Fintype.card_prod,Fintype.card_fun,sq,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bound

private lemma lift_cover (primeMod : ℕ) {M : ℕ+} {k q s l : ℕ} (label : Fin k → ZMod M)
    (inj : Function.Injective label) (cover : ∀ x, ∃ i j, i < j ∧ label i+label j=x)
    (hs : 0<s) (gaps : ∀ i j : Fin k, i<j → j.val-i.val ∣ s) (primeform : s*l+1=q)
    (d : ℕ) : StrictCover (lift primeMod label q s d (by omega)) := by
  intro z
  have qp : 0<q := by omega
  let N := modulus M q d qp
  obtain ⟨i,j,hij,hlabel⟩ := cover (z.val : ZMod M)
  have hlow : (label i).val+(label j).val ≡ z.val [MOD M.val] :=
    (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using hlabel)
  obtain ⟨X,hX⟩ := hlow.dvd
  obtain ⟨t,u,e,hX'⟩ := twisted_pair primeMod hs hij (gaps i j hij) primeform d 0 0 X
  let v := value primeMod label (i,t)
  let w := value primeMod label (j,u)
  have hv : (v : ZMod N) ∈ lift primeMod label q s d qp := mem_image.mpr ⟨(i,t),mem_univ _,rfl⟩
  have hw : (w : ZMod N) ∈ lift primeMod label q s d qp := mem_image.mpr ⟨(j,u),mem_univ _,rfl⟩
  refine ⟨v,hv,w,hw,?_,?_⟩
  · intro eq
    have small := ((ZMod.natCast_eq_natCast_iff v w N.val).mp eq).of_dvd
      (show M.val ∣ N.val from dvd_mul_right ..)
    have he := (ZMod.natCast_eq_natCast_iff v w M.val).mpr small
    exact (ne_of_lt hij) (inj (by simpa [v,w,value] using he))
  · rw [← Nat.cast_add,← ZMod.natCast_zmod_val z]
    apply (ZMod.natCast_eq_natCast_iff ..).mpr
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨e,?_⟩
    change (z.val:ℤ)-((v+w:ℕ):ℤ)=(M.val*(q^2)^d:ℕ)*e
    dsimp [v,w,value]
    push_cast at hX ⊢
    linear_combination hX+(M.val:ℤ)*hX'

/-- The radix q and the prime p used for the quadratic correction may differ.
The width bounds the number of p-blocks that a single parameter can occupy. -/
theorem finite_lift {M : ℕ+} (A : Finset (ZMod M)) (hA : StrictCover A)
    (p q l d width : ℕ) [Fact p.Prime] (hp : 2<p) (hpq : p≤q) (hsq : A.card.factorial<q)
    (wide : q+A.card.factorial ≤ width*p)
    (form : A.card.factorial*l+1=q) :
    let N : ℕ+ := ⟨M.val*(q^2)^d,Nat.mul_pos M.pos (pow_pos (pow_pos (by omega : 0<q) _) _)⟩
    ∃ B : Finset (ZMod N), StrictCover B ∧ B.card ≤ A.card*(q+A.card.factorial)^d ∧
      maxReps B ≤ A.card^2*(8*width*(4*A.card+7))^d*(q+A.card.factorial) := by
  classical
  let k := A.card
  let e : ↥A ≃ Fin k := A.equivFin
  let label (i : Fin k) := (e.symm i).val
  have inj : Function.Injective label := fun _ _ he => e.symm.injective (Subtype.ext he)
  have h (x : ZMod M) : ∃ i j : Fin k, i < j ∧ label i+label j=x := by
    obtain ⟨a,ha,b,hb,hab,eq⟩ := hA x
    let i := e ⟨a,ha⟩
    let j := e ⟨b,hb⟩
    have hi : label i=a := by simp [label,i]
    have hj : label j=b := by simp [label,j]
    rcases lt_trichotomy i j with lt|same|gt
    · exact ⟨i,j,lt,by rwa [hi,hj]⟩
    · exact False.elim (hab (hi.symm.trans ((congrArg label same).trans hj)))
    · exact ⟨j,i,gt,by rwa [add_comm,hi,hj]⟩
  have gaps (i j : Fin k) (lt : i<j) : j.val-i.val ∣ k.factorial :=
    Nat.dvd_factorial (Nat.sub_pos_of_lt lt) ((Nat.sub_le ..).trans j.isLt.le)
  have unit : IsUnit (k.factorial : ZMod q) := (ZMod.isUnit_iff_coprime ..).2 (by rw [←form]; simp [k])
  let B := lift p label q k.factorial d (by omega)
  refine ⟨B,lift_cover p label inj h (Nat.factorial_pos _) gaps form d,?_,
    lift_cap label hp hpq unit hsq wide⟩
  have hc := card_image_le (s := (univ : Finset (Param k q k.factorial d)))
    (f := fun v => (value p label v : ZMod (modulus M q d (by omega))))
  change (lift p label q k.factorial d (by omega)).card ≤ k*(q+k.factorial)^d
  exact hc.trans (by simp [Param,Word])

/-- Every sufficiently large radix in the seed progression is admissible.
Bertrand's postulate supplies an auxiliary prime greater than half the radix. -/
theorem finite_lift_all_radices {M : ℕ+} (A : Finset (ZMod M)) (hA : StrictCover A)
    (q l d : ℕ) (hq : 6≤q) (hsq : A.card.factorial<q) (form : A.card.factorial*l+1=q) :
    let N : ℕ+ := ⟨M.val*(q^2)^d,Nat.mul_pos M.pos (pow_pos (pow_pos (by omega : 0<q) _) _)⟩
    ∃ B : Finset (ZMod N), StrictCover B ∧ B.card ≤ A.card*(q+A.card.factorial)^d ∧
      maxReps B ≤ A.card^2*(32*(4*A.card+7))^d*(q+A.card.factorial) := by
  obtain ⟨p,prime,lo,hi⟩ := Nat.exists_prime_lt_and_le_two_mul (q/2) (by omega)
  let : Fact p.Prime := ⟨prime⟩
  exact finite_lift A hA p q l d 4 (by omega) (by omega) hsq (by omega) form

#print axioms quadratic_pair
#print axioms twisted_pair
#print axioms finite_lift
#print axioms finite_lift_all_radices

end Green33QuadraticRadix
