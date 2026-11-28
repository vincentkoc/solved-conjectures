import Green33StrictReduction
import Green33Divergence
import Mathlib.NumberTheory.PrimesCongruentOne

/-! Cyclic lifts with a quadratic correction from the preceding digit. -/

open Finset
open scoped Pointwise

namespace Green33SubpowerRepresentations

/-- The high half of a base-q² digit tests the squares of the preceding coordinates. -/
def block (q s i prev t : ℕ) : ℕ :=
  (s+i*q)*t + q*(prev^2 % q)

/-- Base-q² encoding before reduction modulo its d-digit modulus. -/
def encode (q s i : ℕ) : (d prev : ℕ) → (Fin d → Fin (q+s)) → ℕ
  | 0, _, _ => 0
  | d+1, prev, t => block q s i prev (t 0) + q^2 * encode q s i d (t 0) (Fin.tail t)

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
theorem twisted_pair {q s i j l : ℕ} (hs : 0<s) (hij : i<j) (gap : j-i ∣ s)
    (hq : s*l+1=q) (d : ℕ) (a b : ℕ) (z : ℤ) :
    ∃ t u : Fin d → Fin (q+s), ∃ e : ℤ,
      z = encode q s i d a t + (encode q s j d b u : ℤ) + ((q:ℤ)^2)^d*e := by
  obtain ⟨h,hdh⟩ := gap
  have hd : 0<j-i := Nat.sub_pos_of_lt hij
  have hh : 0<h := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hdh; omega
  have hhs : h ≤ s := hdh ▸ Nat.le_mul_of_pos_left h hd
  have hi : (i:ℤ)+((j-i:ℕ):ℤ)=j := by exact_mod_cast Nat.add_sub_of_le hij.le
  induction d generalizing a b z with
  | zero => exact ⟨Fin.elim0,Fin.elim0,z,by simp [encode]⟩
  | succ d ih =>
    let off := q*(a^2%q)+q*(b^2%q)
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

private lemma same_total {q s i j a b a' b' t u t' u' : ℕ}
    [Fact q.Prime] (hs : 0 < s) (hsq : s < q)
    (hb : block q s i a t + block q s j b u = block q s i a' t' + block q s j b' u')
    (hbucket : (t+u)/q=(t'+u')/q) : t+u=t'+u' := by
  have nz : (s : ZMod q) ≠ 0 := by
    rw [ne_eq,ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hs hsq
  have he := congrArg (fun x : ℕ => (x : ZMod q)) hb
  simp [block] at he
  have ht : (t : ZMod q)+u=(t' : ZMod q)+u' := by
    apply mul_left_cancel₀ nz
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

private def sums (q s i j : ℕ) : (d a b : ℕ) → Word q s d → Word q s d → Fin d → ℕ
  | 0, _, _, _, _ => Fin.elim0
  | d+1, a, b, t, u => Fin.cons (block q s i a (t 0)+block q s j b (u 0))
      (sums q s i j d (t 0) (u 0) (Fin.tail t) (Fin.tail u))

private def last {q s : ℕ} : (d prev : ℕ) → Word q s d → ℕ
  | 0, prev, _ => prev
  | d+1, _, t => last d (t 0) (Fin.tail t)

private lemma aligned {q s i j : ℕ} (hq : 0 < q) (d a b a' b' : ℕ)
    (t u t' u' : Word q s d)
    (code : ∀ h, sums q s i j d a b t u h/q^2=sums q s i j d a' b' t' u' h/q^2)
    (res : encode q s i d a t+encode q s j d b u ≡
      encode q s i d a' t'+encode q s j d b' u' [MOD (q^2)^d]) :
    ∀ h, sums q s i j d a b t u h=sums q s i j d a' b' t' u' h := by
  induction d generalizing a b a' b' with
  | zero => intro h; exact h.elim0
  | succ d ih =>
    simp only [encode,show ∀ x X y Y : ℕ, x+q^2*X+(y+q^2*Y)=x+y+q^2*(X+Y) by intros; ring] at res
    have c := code 0
    simp only [sums,Fin.cons_zero] at c
    obtain ⟨low,tail⟩ := strip (by positivity : 0 < q^2) res c
    exact Fin.cases low (ih _ _ _ _ _ _ _ _ (fun h => by
      simpa only [sums,Fin.cons_succ] using code h.succ) tail)

private def Mark (k : ℕ) := Fin (4*k+7) × Fin 4 × Fin 2 × Bool
private instance (k : ℕ) : Fintype (Mark k) := inferInstanceAs (Fintype (_ × _ × _ × Bool))

private lemma block_le {q s : ℕ} (hs : s < q) (k : ℕ) (i : Fin k) (a : ℕ) (t : Fin (q+s)) :
    block q s i a t ≤ (2*k+3)*q^2 := by
  have hq : 0 < q := by omega
  have ht : t.val ≤ 2*q := by have := t.isLt; omega
  have hw : s+i.val*q ≤ (k+1)*q := by
    have h := Nat.mul_le_mul_right q i.isLt.le
    nlinarith only [h,hs]
  have hm := (Nat.mod_lt (a^2) hq).le
  dsimp [block]
  calc
    _ ≤ (k+1)*q*(2*q)+q*q := Nat.add_le_add (Nat.mul_le_mul hw ht) (Nat.mul_le_mul_left q hm)
    _ = _ := by ring

private def mark {q s k d : ℕ} (hs : s < q) (i j : Fin k) (a b : ℕ)
    (t u : Word q s d) (h : Fin d) : Mark k :=
  (⟨(sums q s i j d a b t u h/q^2)%(4*k+7),Nat.mod_lt _ (by omega)⟩,
   ⟨((t h).val+(u h).val)/q,Nat.div_lt_iff_lt_mul (by omega) |>.mpr (by have := (t h).isLt; have := (u h).isLt; omega)⟩,
   ⟨(t h).val/q,Nat.div_lt_iff_lt_mul (by omega) |>.mpr (by have := (t h).isLt; omega)⟩,
   decide ((t h).val%q ≤ (u h).val%q))

private lemma sums_le {q s k : ℕ} (hs : s < q) (i j : Fin k) (d a b : ℕ) (t u : Word q s d) :
    ∀ h, sums q s i j d a b t u h ≤ (4*k+6)*q^2 := by
  induction d generalizing a b with
  | zero => intro h; exact h.elim0
  | succ d ih =>
    apply Fin.cases
    · simp only [sums,Fin.cons_zero]
      linarith only [block_le hs k i a (t 0),block_le hs k j b (u 0)]
    · exact ih _ _ _ _

private lemma head_mixed {q s i j a b t u t' u' : ℕ} (hq : 0 < q) (ne : i ≠ j)
    (sum : t+u=t'+u') (raw : block q s i a t+block q s j b u=block q s i a t'+block q s j b u') :
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

private lemma recover {q s : ℕ} [Fact q.Prime] (hq : 2<q) (hs : 0<s) (hsq : s<q)
    (i j d a b : ℕ) (t u t' u' : Word q s d)
    (raw : ∀ h, sums q s i j d a b t u h=sums q s i j d a b t' u' h)
    (addQ : ∀ h, ((t h).val+(u h).val)/q=((t' h).val+(u' h).val)/q)
    (order : ∀ h, ((t h).val%q ≤ (u h).val%q) ↔ ((t' h).val%q ≤ (u' h).val%q))
    (top : ∀ h, (t h).val/q=(t' h).val/q) (endEq : last d a t=last d a t') :
    t=t' ∧ u=u' := by
  induction d generalizing a b with
  | zero => exact ⟨Subsingleton.elim ..,Subsingleton.elim ..⟩
  | succ d ih =>
    have head := raw 0
    simp only [sums,Fin.cons_zero] at head
    have sum := same_total hs hsq head (addQ 0)
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
          have sn := same_total hs hsq next (addQ (0 : Fin (d+1)).succ)
          have e : (t 0).val^2%q+(u 0).val^2%q=(t' 0).val^2%q+(u' 0).val^2%q := by
            dsimp [block] at next
            change ((Fin.tail t 0).val+(Fin.tail u 0).val)=
              ((Fin.tail t' 0).val+(Fin.tail u' 0).val) at sn
            apply Nat.eq_of_mul_eq_mul_left (by omega : 0<q)
            nlinarith only [next, congrArg (fun z => (s+i*q)*z) sn]
          exact square_signature hq sum e (order 0) (top 0)
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

private lemma mark_injective {q s k d : ℕ} [Fact q.Prime] (hq : 2<q) (hs : 0<s) (hsq : s<q)
    (i j : Fin k) (t u t' u' : Word q s d)
    (res : encode q s i d 0 t+encode q s j d 0 u ≡
      encode q s i d 0 t'+encode q s j d 0 u' [MOD (q^2)^d])
    (tag : mark hsq i j 0 0 t u = mark hsq i j 0 0 t' u')
    (finalDigit : last d 0 t=last d 0 t') : t=t' ∧ u=u' := by
  have bound (t u : Word q s d) (h) : sums q s i j d 0 0 t u h/q^2 < 4*k+7 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    have hpos : 0<q^2 := by positivity
    nlinarith only [sums_le hsq i j d 0 0 t u h,hpos]
  have first (h) := congrArg (fun z : Mark k => z.1.val) (congrFun tag h)
  simp only [mark,Nat.mod_eq_of_lt (bound _ _ _)] at first
  apply recover hq hs hsq i j d 0 0 _ _ _ _ (aligned (by omega) d 0 0 0 0 _ _ _ _ first res)
  · exact fun h => congrArg (fun z : Mark k => z.2.1.val) (congrFun tag h)
  · intro h
    have eq := congrArg (fun z : Mark k => z.2.2.2) (congrFun tag h)
    simpa only [mark,decide_eq_decide] using eq
  · exact fun h => congrArg (fun z : Mark k => z.2.2.1.val) (congrFun tag h)
  · exact finalDigit

open Green33StrictReduction Green33Multiplicity

private def modulus (M : ℕ+) (q d : ℕ) (hq : 0<q) : ℕ+ :=
  ⟨M.val*(q^2)^d,Nat.mul_pos M.pos (pow_pos (pow_pos hq _) _)⟩

private abbrev Param (k q s d : ℕ) := Fin k × Word q s d

private def value {M : ℕ+} {k q s d : ℕ} (label : Fin k → ZMod M) (p : Param k q s d) : ℕ :=
  (label p.1).val+M.val*encode q s p.1 d 0 p.2

private def lift {M : ℕ+} {k : ℕ} (label : Fin k → ZMod M) (q s d : ℕ) (hq : 0<q) :
    Finset (ZMod (modulus M q d hq)) :=
  univ.image (fun p : Param k q s d => (value label p : ZMod (modulus M q d hq)))

private lemma quotient_res {M : ℕ+} {k q s d : ℕ} (label : Fin k → ZMod M) (hq : 0<q)
    (i j : Fin k) (t u t' u' : Word q s d)
    (he : ((value label (i,t)+value label (j,u) : ℕ) : ZMod (modulus M q d hq)) =
      ((value label (i,t')+value label (j,u') : ℕ) : ZMod (modulus M q d hq))) :
    encode q s i d 0 t+encode q s j d 0 u ≡
      encode q s i d 0 t'+encode q s j d 0 u' [MOD (q^2)^d] := by
  have h := (ZMod.natCast_eq_natCast_iff ..).mp he
  change _ ≡ _ [MOD M.val*(q^2)^d] at h
  simp only [value,show ∀ a x b y : ℕ, a+M.val*x+(b+M.val*y)=(a+b)+M.val*(x+y) by intros; ring] at h
  exact Nat.ModEq.mul_left_cancel' M.pos.ne' (Nat.ModEq.add_left_cancel' _ h)

private lemma lift_cap {M : ℕ+} {k q s d : ℕ} [Fact q.Prime] (label : Fin k → ZMod M)
    (hq : 2<q) (hs : 0<s) (hsq : s<q) :
    maxReps (lift label q s d (by omega)) ≤ k^2*(16*(4*k+7))^d*(q+s) := by
  classical
  let N := modulus M q d (by omega)
  let A := lift label q s d (by omega)
  apply Finset.sup_le
  intro z _
  let X := (A ×ˢ A).filter fun r => r.1+r.2=z
  let P := Param k q s d
  have choice (x : ↥A) : ∃ p : P, (value label p : ZMod N)=x.val := by
    obtain ⟨p,_,hp⟩ := mem_image.mp x.property
    exact ⟨p,hp⟩
  let elem (x : ↥A) : P := (choice x).choose
  have spec (x : ↥A) : (value label (elem x) : ZMod N)=x.val := (choice x).choose_spec
  let left (r : ↥X) := elem ⟨r.val.1,(mem_product.mp (mem_filter.mp r.property).1).1⟩
  let right (r : ↥X) := elem ⟨r.val.2,(mem_product.mp (mem_filter.mp r.property).1).2⟩
  have lspec (r : ↥X) : (value label (left r) : ZMod N)=r.val.1 :=
    spec ⟨_,(mem_product.mp (mem_filter.mp r.property).1).1⟩
  have rspec (r : ↥X) : (value label (right r) : ZMod N)=r.val.2 :=
    spec ⟨_,(mem_product.mp (mem_filter.mp r.property).1).2⟩
  have he (r : ↥X) : ((value label (left r)+value label (right r) : ℕ) : ZMod N)=z := by
    rw [Nat.cast_add,lspec,rspec]; exact (mem_filter.mp r.property).2
  let code (r : ↥X) : (Fin k × Fin k) × (Fin d → Mark k) × Fin (q+s) :=
    let l := left r; let h := right r
    ((l.1,h.1),mark hsq l.1 h.1 0 0 l.2 h.2,⟨last d 0 l.2,last_lt d 0 (by omega) l.2⟩)
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
    obtain ⟨rfl,rfl⟩ := mark_injective hq hs hsq i j _ _ _ _
      (quotient_res label (by omega) i j _ _ _ _ hxy) tags ends
    apply Subtype.ext
    apply Prod.ext
    · calc
        x.val.1 = (value label (left x) : ZMod N) := (lspec x).symm
        _ = _ := by rw [hil,←hil']; exact lspec y
    · calc
        x.val.2 = (value label (right x) : ZMod N) := (rspec x).symm
        _ = _ := by rw [hjr,←hjr']; exact rspec y
  have bound := Fintype.card_le_of_injective code inj
  change X.card ≤ _
  simpa [Mark,Fintype.card_prod,Fintype.card_fun,sq,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bound

private lemma lift_cover {M : ℕ+} {k q s l : ℕ} [Fact q.Prime] (label : Fin k → ZMod M)
    (inj : Function.Injective label) (cover : ∀ x, ∃ i j, i < j ∧ label i+label j=x)
    (hs : 0<s) (gaps : ∀ i j : Fin k, i<j → j.val-i.val ∣ s) (primeform : s*l+1=q)
    (d : ℕ) : StrictCover (lift label q s d (by omega)) := by
  intro z
  have qp : 0<q := by omega
  let N := modulus M q d qp
  obtain ⟨i,j,hij,hlabel⟩ := cover (z.val : ZMod M)
  have hlow : (label i).val+(label j).val ≡ z.val [MOD M.val] :=
    (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using hlabel)
  obtain ⟨X,hX⟩ := hlow.dvd
  obtain ⟨t,u,e,hX'⟩ := twisted_pair hs hij (gaps i j hij) primeform d 0 0 X
  let v := value label (i,t)
  let w := value label (j,u)
  have hv : (v : ZMod N) ∈ lift label q s d qp := mem_image.mpr ⟨(i,t),mem_univ _,rfl⟩
  have hw : (w : ZMod N) ∈ lift label q s d qp := mem_image.mpr ⟨(j,u),mem_univ _,rfl⟩
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

/-- Any finite strict cyclic seed lifts through a d-digit prime radix.
The cardinality grows in degree d while the ordered representation cap
grows only linearly in q for a fixed dimension and seed. -/
theorem finite_lift {M : ℕ+} (A : Finset (ZMod M)) (hA : StrictCover A)
    (q l d : ℕ) [Fact q.Prime] (hq : 2<q) (hsq : A.card.factorial<q)
    (form : A.card.factorial*l+1=q) :
    let N : ℕ+ := ⟨M.val*(q^2)^d,by positivity⟩
    ∃ B : Finset (ZMod N), StrictCover B ∧ B.card ≤ A.card*(q+A.card.factorial)^d ∧
      maxReps B ≤ A.card^2*(16*(4*A.card+7))^d*(q+A.card.factorial) := by
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
  let B := lift label q k.factorial d (by omega)
  refine ⟨B,lift_cover label inj h (Nat.factorial_pos _) gaps form d,?_,
    lift_cap label hq (Nat.factorial_pos _) hsq⟩
  have hc := card_image_le (s := (univ : Finset (Param k q k.factorial d)))
    (f := fun v => (value label v : ZMod (modulus M q d (by omega))))
  change (lift label q k.factorial d (by omega)).card ≤ k*(q+k.factorial)^d
  exact hc.trans (by simp [Param,Word])

open Filter
open scoped Topology

/-- A seed-dependent constant controls the peak at the sharper scale
exp(C sqrt(log N)). The same C works for every density tolerance at that seed. -/
theorem seed_sqrt_log {M : ℕ+} (A : Finset (ZMod M)) (hA : StrictCover A) :
    ∃ C : ℝ, 0<C ∧ ∀ ε : ℝ, 0<ε → ∃ᶠ N : ℕ+ in atTop, ∃ B : Finset (ZMod N),
      StrictCover B ∧ (B.card : ℝ)/Real.sqrt N < (A.card : ℝ)/Real.sqrt M+ε ∧
      (maxReps B : ℝ) ≤ Real.exp (C*Real.sqrt (Real.log N)) := by
  let k := A.card
  let s := k.factorial
  let K := 16*(4*k+7)
  let C : ℝ := 2*(k:ℝ)^2+K+1
  let v := (k:ℝ)/Real.sqrt M
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ε hε
  have small : Tendsto (fun q : ℕ => Real.log q/(q:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have lim : Tendsto (fun q : ℕ => v*Real.exp ((s:ℝ)*(Real.log q/q))) atTop (𝓝 v) := by
    simpa using ((small.const_mul (s:ℝ)).rexp).const_mul v
  have lg : Tendsto (fun q : ℕ => Real.log (q:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp ((lim.eventually_lt_const (show v<v+ε by linarith)).and
    (lg.eventually (eventually_ge_atTop 2)))
  apply frequently_atTop.mpr
  intro T
  obtain ⟨q,prime,big,one⟩ := Nat.exists_prime_gt_modEq_one (Q+T.val+s+2) (Nat.factorial_pos k).ne'
  have : Fact q.Prime := ⟨prime⟩
  have hq : 2<q := by omega
  have hsq : s<q := by omega
  obtain ⟨l,hl⟩ := (Nat.modEq_iff_dvd' (by omega : 1≤q)).mp one.symm
  change q-1=s*l at hl
  have form : s*l+1=q := by omega
  obtain ⟨density,Lbig⟩ := hQ q (by omega)
  let L := Real.log (q:ℝ)
  let d := ⌊L⌋₊
  change 2 ≤ L at Lbig
  have dlow : L < (d:ℝ)+1 := Nat.lt_floor_add_one _
  have dup : (d:ℝ) ≤ L := Nat.floor_le (by linarith)
  have dpos : 0<d := by
    by_contra! hh
    have he : d=0 := by omega
    rw [he] at dlow
    norm_num at dlow
    linarith only [Lbig,dlow]
  let N := modulus M q d prime.pos
  obtain ⟨B,hB,size,peak⟩ := finite_lift A hA q l d hq hsq form
  change B.card ≤ k*(q+s)^d at size
  change maxReps B ≤ k^2*K^d*(q+s) at peak
  have hm : 0<(M:ℝ) := by exact_mod_cast M.pos
  have qp : 0<(q:ℝ) := by exact_mod_cast prime.pos
  have ord : q^(2*d) ≤ N.val := by
    dsimp [N,modulus]; rw [pow_mul]; exact Nat.le_mul_of_pos_left _ M.pos
  refine ⟨N,(show T.val ≤ q by omega).trans ((Nat.le_self_pow (by omega) _).trans ord),B,hB,?_,?_⟩
  · have root : Real.sqrt (N:ℝ)=Real.sqrt M*(q:ℝ)^d := by
      change Real.sqrt ((M.val*(q^2)^d:ℕ):ℝ)=_
      push_cast
      rw [Real.sqrt_mul hm.le,←pow_mul,Nat.mul_comm 2 d,pow_mul,Real.sqrt_sq (by positivity)]
    have card : (B.card:ℝ) ≤ (k:ℝ)*((q:ℝ)+s)^d := by exact_mod_cast size
    have hv : 0≤v := div_nonneg (by positivity) (Real.sqrt_nonneg _)
    change (B.card:ℝ)/Real.sqrt (N:ℝ)<v+ε
    rw [root]
    calc
      _ ≤ ((k:ℝ)*((q:ℝ)+s)^d)/(Real.sqrt M*(q:ℝ)^d) := by gcongr
      _ = v*(1+(s:ℝ)/q)^d := by
        have eq : 1+(s:ℝ)/q=((q:ℝ)+s)/q := by field_simp
        rw [eq,div_pow]; dsimp [v]; ring
      _ ≤ v*(Real.exp ((s:ℝ)/q))^d := by
        gcongr; linarith only [Real.add_one_le_exp ((s:ℝ)/q)]
      _ ≤ v*Real.exp ((s:ℝ)*(L/q)) := by
        rw [← Real.exp_nat_mul]
        apply mul_le_mul_of_nonneg_left _ hv
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ L*((s:ℝ)/q) := mul_le_mul_of_nonneg_right dup (by positivity)
          _ = _ := by ring
      _ < _ := density
  · have nreal : ((q:ℝ)^(2*d)) ≤ (N:ℝ) := by exact_mod_cast ord
    have logord := Real.log_le_log (by positivity) nreal
    rw [Real.log_pow] at logord
    push_cast at logord
    change 2*(d:ℝ)*L ≤ Real.log (N:ℝ) at logord
    have sq : L^2 ≤ Real.log (N:ℝ) := by
      have : L ≤ 2*(d:ℝ) := by linarith only [dlow,Lbig]
      nlinarith only [logord,mul_le_mul_of_nonneg_right this (by linarith only [Lbig] : 0≤L)]
    have root := Real.le_sqrt_of_sq_le sq
    have hsize : (maxReps B:ℝ) ≤ (k:ℝ)^2*(K:ℝ)^d*((q:ℝ)+s) := by exact_mod_cast peak
    have h2 : (q:ℝ)+s ≤ 2*q := by exact_mod_cast (show q+s≤2*q by omega)
    have e1 : 2*(k:ℝ)^2 ≤ Real.exp (2*(k:ℝ)^2) := by linarith only [Real.add_one_le_exp (2*(k:ℝ)^2)]
    have e2 : (K:ℝ) ≤ Real.exp K := by linarith only [Real.add_one_le_exp (K:ℝ)]
    calc
      _ ≤ (k:ℝ)^2*(K:ℝ)^d*(2*q) := hsize.trans (by gcongr)
      _ = (2*(k:ℝ)^2)*(K:ℝ)^d*q := by ring
      _ ≤ Real.exp (2*(k:ℝ)^2)*(Real.exp K)^d*q := by gcongr
      _ = Real.exp (2*(k:ℝ)^2+(d:ℝ)*K+L) := by rw [Real.exp_add,Real.exp_add,Real.exp_nat_mul,Real.exp_log qp]
      _ ≤ Real.exp (C*L) := by
        apply Real.exp_le_exp.mpr
        dsimp [C]
        nlinarith only [mul_le_mul_of_nonneg_left (show 1≤L by linarith only [Lbig]) (sq_nonneg (k:ℝ)),
          mul_le_mul_of_nonneg_right dup (Nat.cast_nonneg K)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left root hC.le)

/-- A strict seed keeps its normalized size to any tolerance on arbitrarily
large cyclic lifts whose peak ordered count satisfies any fixed power cap. -/
theorem seed_power_cap {M : ℕ+} (A : Finset (ZMod M)) (hA : StrictCover A)
    (h : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ᶠ N : ℕ+ in atTop, ∃ B : Finset (ZMod N),
    StrictCover B ∧ (B.card : ℝ)/Real.sqrt N < (A.card : ℝ)/Real.sqrt M+ε ∧
      (maxReps B)^h ≤ N.val := by
  obtain ⟨C,_,lifted⟩ := seed_sqrt_log A hA
  have tend : Tendsto (fun N : ℕ+ => Real.sqrt (Real.log (N:ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop))
  apply ((lifted ε hε).and_eventually (tend.eventually (eventually_ge_atTop ((h:ℝ)*C)))).mono
  rintro N ⟨⟨B,hB,size,cap⟩,large⟩
  refine ⟨B,hB,size,?_⟩
  have hn : 0<(N:ℝ) := by exact_mod_cast N.pos
  have ln : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast N.pos)
  have bound : ((maxReps B:ℝ)^h) ≤ (N:ℝ) := calc
    _ ≤ (Real.exp (C*Real.sqrt (Real.log N)))^h := pow_le_pow_left₀ (by positivity) cap h
    _ = Real.exp ((h:ℝ)*C*Real.sqrt (Real.log N)) := by rw [←Real.exp_nat_mul,mul_assoc]
    _ ≤ Real.exp (Real.log N) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.sqrt (Real.log N)*Real.sqrt (Real.log N) :=
          mul_le_mul_of_nonneg_right large (Real.sqrt_nonneg _)
        _ = _ := Real.mul_self_sqrt ln
    _ = _ := Real.exp_log hn
  exact_mod_cast bound

/-- Green 33 is equivalent to its strict form with subpolynomial peak ordered
representation count: the same witness meets both the size tolerance and
the prescribed power cap at arbitrarily large orders. -/
theorem ordinary_iff_subpower : OrdinaryLimit ↔ ∀ (h : ℕ) (ε : ℝ), 0<ε →
    ∃ᶠ N : ℕ+ in atTop, ∃ B : Finset (ZMod N), StrictCover B ∧
      |(B.card:ℝ)/Real.sqrt N-Real.sqrt 2| < ε ∧ (maxReps B)^h ≤ N.val := by
  constructor
  · intro green h ε hε
    obtain ⟨M,A,hA,small⟩ := ordinary_iff_finite_strict.mp green (ε/2) (by positivity)
    apply (seed_power_cap A hA h (ε/2) (by positivity)).mono
    rintro N ⟨B,hB,size,cap⟩
    have hn : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast N.pos)
    have lo : Real.sqrt 2 ≤ (B.card:ℝ)/Real.sqrt N := (le_div_iff₀ hn).mpr (by linarith only [strict_size_gap hB])
    refine ⟨B,hB,?_,cap⟩
    rw [abs_of_nonneg (sub_nonneg.mpr lo)]
    linarith only [size,small]
  · intro cond
    apply ordinary_iff_strict.mpr
    intro ε hε
    exact (cond 1 ε hε).mono (fun _ ⟨B,hB,size,_⟩ => ⟨B,hB,size⟩)

/-- A single conditional family simultaneously has diverging peak multiplicity
and a peak below every fixed positive power of the cyclic order. -/
theorem subpower_family (green : OrdinaryLimit) :
    ∃ (N : ℕ → ℕ+) (A : (t : ℕ) → Finset (ZMod (N t))),
      Tendsto (fun t => (N t).val) atTop atTop ∧ (∀ t, StrictCover (A t)) ∧
      Tendsto (fun t => ((A t).card:ℝ)/Real.sqrt (N t)) atTop (𝓝 (Real.sqrt 2)) ∧
      Tendsto (fun t => maxReps (A t)) atTop atTop ∧
      ∀ h : ℕ, ∀ᶠ t : ℕ in atTop, (maxReps (A t))^h ≤ (N t).val := by
  have ex (t : ℕ) : ∃ N : ℕ+, t+1≤N.val ∧ ∃ A : Finset (ZMod N),
      StrictCover A ∧ |(A.card:ℝ)/Real.sqrt N-Real.sqrt 2| < 1/((t:ℝ)+1) ∧
        (maxReps A)^t ≤ N.val := by
    have f := ordinary_iff_subpower.mp green t (1/((t:ℝ)+1)) (by positivity)
    exact frequently_atTop.mp f ⟨t+1,by omega⟩
  choose N big A cover err cap using ex
  have tend : Tendsto (fun t => (N t).val) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with t ht
    exact ht.trans ((Nat.le_succ _).trans (big t))
  have size : Tendsto (fun t => ((A t).card:ℝ)/Real.sqrt (N t)) atTop (𝓝 (Real.sqrt 2)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using squeeze_zero (fun t => abs_nonneg _)
      (fun t => (err t).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have ordinary (t : ℕ) : A t + A t = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨a,ha,b,hb,_,e⟩ := cover t z
    exact mem_add.mpr ⟨a,ha,b,hb,e⟩
  have divg := tendsto_maxReps_atTop N A tend ordinary size
  refine ⟨N,A,tend,cover,size,divg,?_⟩
  intro h
  filter_upwards [eventually_ge_atTop h,divg.eventually (eventually_ge_atTop 1)] with t ht hpos
  exact (Nat.pow_le_pow_right hpos ht).trans (cap t)

#print axioms subpower_family
#print axioms ordinary_iff_subpower
#print axioms seed_sqrt_log
#print axioms seed_power_cap
#print axioms finite_lift
#print axioms twisted_pair
#print axioms quadratic_pair

end Green33SubpowerRepresentations
