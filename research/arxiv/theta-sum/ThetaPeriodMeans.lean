import ThetaDenominatorTails
import Mathlib.Data.ZMod.Units
/-! Finite-period averaging for the prime sieve. -/
namespace Arxiv.«2501.03234».ThetaPeriodMeans
open Finset
/-- A discrete average over one complete period. -/
noncomputable def mean (d : ℕ) (f : ℕ → ℝ) := (∑ n ∈ range d, f n)/(d:ℝ)

/-- A function whose value depends only on the residue class modulo d. -/
def OnMod {α : Type*} (d : ℕ) (f : ℕ → α) : Prop := ∀ n, f (n%d)=f n

theorem sum_crt {d e : ℕ} (hd : 0<d) (he : 0<e) (hc : d.Coprime e)
    {A : Type*} [AddCommMonoid A] (f : ℕ → ℕ → A) :
    ∑ k ∈ range (d*e), f (k%d) (k%e) = ∑ i ∈ range d, ∑ j ∈ range e, f i j := by
  rw [← sum_product']
  apply sum_bij (fun k _ => (k%d,k%e))
  · intro k _; exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hd),mem_range.mpr (Nat.mod_lt _ he)⟩
  · intro k hk l hl h
    have ha : k≡l [MOD d] := congrArg Prod.fst h
    have hb : k≡l [MOD e] := congrArg Prod.snd h
    have hc' := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨ha,hb⟩
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt (mem_range.mp hk),Nat.mod_eq_of_lt (mem_range.mp hl)] using hc'
  · rintro ⟨i,j⟩ hh; obtain ⟨hi,hj⟩ := mem_product.mp hh
    let a := Nat.chineseRemainder hc i j
    refine ⟨a.val,mem_range.mpr (Nat.chineseRemainder_lt_mul hc i j hd.ne' he.ne'),?_⟩
    exact Prod.ext (Eq.trans a.property.1 (Nat.mod_eq_of_lt (mem_range.mp hi))) (Eq.trans a.property.2 (Nat.mod_eq_of_lt (mem_range.mp hj)))
  · intro k _; rfl

/-- Complete averages of products factor for coprime periods. -/
theorem mean_mul_coprime {d e : ℕ} (hd : 0<d) (he : 0<e) (hc : d.Coprime e)
    {f g : ℕ → ℝ} (hf : OnMod d f) (hg : OnMod e g) :
    mean (d*e) (fun n => f n*g n) = mean d f*mean e g := by
  unfold mean
  have eq (n : ℕ) : f n*g n=f (n%d)*g (n%e) := by rw [hf,hg]
  simp_rw [eq]
  rw [sum_crt hd he hc (fun i j => f i*g j)]
  simp_rw [← mul_sum]; rw [← sum_mul,Nat.cast_mul]; ring

/-- Partition a whole number of periods into residue fibers. -/
theorem sum_fibers {A : Type*} [AddCommMonoid A] {d : ℕ} (hd : 0<d) (m : ℕ) (f : ℕ → A) :
    ∑ k ∈ range (d*m), f k = ∑ i ∈ range d, ∑ j ∈ range m, f (i+d*j) := by
  rw [← sum_product']
  apply sum_bij (fun k _ => (k%d,k/d))
  · intro k hk
    exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hd),mem_range.mpr
      ((Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [mul_comm m d] using mem_range.mp hk))⟩
  · intro k _ l _ h
    have ha := congrArg Prod.fst h; have hb := congrArg Prod.snd h
    calc k = k%d+d*(k/d) := (Nat.mod_add_div ..).symm
         _ = l%d+d*(l/d) := by rw [show k%d=l%d from ha,show k/d=l/d from hb]
         _ = l := Nat.mod_add_div ..
  · rintro ⟨i,j⟩ hij
    obtain ⟨hi,hj⟩ := mem_product.mp hij
    have hi' : i<d := mem_range.mp hi; have hj' : j < m := mem_range.mp hj
    have hlt := Nat.mul_le_mul_left d (show j+1 ≤ m by omega)
    refine ⟨i+d*j,mem_range.mpr (by nlinarith),Prod.ext ?_ ?_⟩
    · simp [Nat.mod_eq_of_lt hi']
    · simp [Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt hi']
  · intro k _; exact congrArg f (Nat.mod_add_div k d).symm

theorem mean_lift {d P : ℕ} (hd : 0<d) (hP : 0<P) (h : d∣P) {f : ℕ → ℝ}
    (hf : OnMod d f) : mean P f=mean d f := by
  obtain ⟨m,rfl⟩ := h
  have hm : 0 < m := Nat.pos_of_mul_pos_left hP
  unfold mean
  rw [sum_fibers hd]
  have H (i j : ℕ) : f (i+d*j)=f i := by rw [← hf (i+d*j),Nat.add_mul_mod_self_left,hf]
  simp_rw [H,sum_const,card_range,nsmul_eq_mul]
  rw [← mul_sum,Nat.cast_mul]
  field_simp

theorem onMod_lift {α : Type*} {d P : ℕ} {f : ℕ → α} (h : d∣P) (hf : OnMod d f) :
    OnMod P f := by
  intro n; rw [← hf (n%P),Nat.mod_mod_of_dvd n h,hf]

theorem onMod_prod {s : Finset ℕ} (F : ℕ → ℕ → ℝ) (hf : ∀ p∈s, OnMod p (F p)) :
    OnMod (∏ p ∈ s, p) (fun n => ∏ p ∈ s, F p n) := by
  intro n; apply prod_congr rfl; intro p hp
  exact onMod_lift (dvd_prod_of_mem (fun i : ℕ => i) hp) (hf p hp) n

/-- Independence of the individual residue coordinates in a squarefree modulus. -/
theorem mean_prime_product (s : Finset ℕ) (F : ℕ → ℕ → ℝ)
    (hs : ∀ p∈s, Nat.Prime p) (hf : ∀ p∈s, OnMod p (F p)) :
    mean (∏ p ∈ s, p) (fun n => ∏ p ∈ s, F p n) = ∏ p ∈ s, mean p (F p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mean]
  | @insert p s hp ih =>
    have hs' (j) (hj : j∈s) := hs j (mem_insert_of_mem hj)
    have hf' (j) (hj : j∈s) := hf j (mem_insert_of_mem hj)
    have hprime := hs p (mem_insert_self ..)
    have hcop : p.Coprime (∏ j ∈ s, j) := by
      apply Nat.Coprime.prod_right
      intro j hj
      exact (Nat.coprime_primes hprime (hs' j hj)).mpr (fun e => hp (e ▸ hj))
    simp only [prod_insert hp]
    rw [mean_mul_coprime hprime.pos (prod_pos (fun j hj => (hs' j hj).pos)) hcop
      (hf p (mem_insert_self ..)) (onMod_prod F hf'), ih hs' hf']

private theorem euler_prod_le (s : Finset ℕ) (h : ∀ p∈s, 2≤p) :
    ∏ p ∈ s, ((p:ℝ)/((p:ℝ)-1)) ≤ s.card+1 := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert p s hlt ih =>
    have hp := h p (mem_insert_self ..)
    have hnot : p∉s := fun h => (lt_irrefl p) (hlt p h)
    have hs (j) (hj : j∈s) := h j (mem_insert_of_mem hj)
    have hc := card_le_card (show s⊆Ico 2 p from fun j hj => mem_Ico.mpr ⟨hs j hj,hlt j hj⟩)
    rw [Nat.card_Ico] at hc
    have hkp : (s.card:ℝ)+2 ≤ p := by exact_mod_cast (show s.card+2≤p by omega)
    rw [prod_insert hnot,card_insert_of_notMem hnot,Nat.cast_add_one]
    have hp' : (0:ℝ)<p-1 := by linarith [show (2:ℝ)≤p by exact_mod_cast hp]
    apply (mul_le_mul_of_nonneg_left (ih hs) (by positivity)).trans
    rw [div_mul_eq_mul_div,div_le_iff₀ hp']; nlinarith

/-- The cost of restricting a complete period to its unit classes is at most
one plus the number of distinct prime factors. -/
theorem unit_density_cost {L : ℕ} (hL : 0<L) :
    (L:ℝ)/L.totient ≤ L.primeFactors.card+1 := by
  have hφ := Nat.totient_pos.mpr hL
  have hd : ∏ p ∈ L.primeFactors, ((p:ℝ)-1) ≠ 0 := by
    apply prod_ne_zero_iff.mpr; intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (2:ℝ)≤p := by exact_mod_cast this
    linarith
  have H := Nat.totient_mul_prod_primeFactors L
  have h' : (L.totient:ℝ)*(∏ p ∈ L.primeFactors, (p:ℝ)) =
      L*(∏ p ∈ L.primeFactors, ((p:ℝ)-1)) := by
    have hc := congrArg (fun n:ℕ => (n:ℝ)) H
    simp only [Nat.cast_mul,Nat.cast_prod] at hc
    rw [hc]; congr 1; apply prod_congr rfl; intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le,Nat.cast_one]
  calc
    _ = ∏ p ∈ L.primeFactors, ((p:ℝ)/((p:ℝ)-1)) := by
      rw [prod_div_distrib, div_eq_div_iff (Nat.cast_ne_zero.mpr hφ.ne') hd]
      linarith only [h']
    _ ≤ _ := euler_prod_le _ (fun _ hp => (Nat.prime_of_mem_primeFactors hp).two_le)

/-- A unit-invariant weight sees a function supported on units through its
ordinary sum over unit residue classes. -/
theorem unit_orbit_sum {q P : ℕ} [NeZero q] [NeZero P] (hd : q∣P)
    (W : ZMod P → ℝ) (h : ZMod q → ℝ)
    (hW : ∀ (u : (ZMod P)ˣ) x, W ((u:ZMod P)*x)=W x)
    (hh : ∀ y, ¬IsUnit y → h y=0) :
    (q.totient:ℝ)*(∑ x : ZMod P, W x*h (ZMod.castHom hd (ZMod q) x)) =
      (∑ x : ZMod P, if IsUnit (ZMod.castHom hd (ZMod q) x) then W x else 0)*
        (∑ v : (ZMod q)ˣ, h (v:ZMod q)) := by
  classical
  let ρ := ZMod.castHom hd (ZMod q)
  have shift (v : (ZMod q)ˣ) : ∑ x : ZMod P, W x*h ((v:ZMod q)*ρ x) =
      ∑ x : ZMod P, W x*h (ρ x) := by
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hd v
    apply Fintype.sum_bijective (fun x : ZMod P => (u:ZMod P)*x) u.mulLeft_bijective
    intro x
    have hv : ρ (u:ZMod P)=(v:ZMod q) := congrArg Units.val hu
    rw [hW,map_mul,hv]
  have average (y : ZMod q) :
      (∑ v : (ZMod q)ˣ, h ((v:ZMod q)*y)) =
        if IsUnit y then ∑ v : (ZMod q)ˣ, h (v:ZMod q) else 0 := by
    split_ifs with hy
    · obtain ⟨u,rfl⟩ := hy
      apply Fintype.sum_bijective (fun v : (ZMod q)ˣ => v*u) (Equiv.mulRight u).bijective
      intro v; rfl
    · apply sum_eq_zero; intro v _
      exact hh _ (fun H => hy (isUnit_of_mul_isUnit_right H))
  calc
    _ = ∑ _v : (ZMod q)ˣ, ∑ x : ZMod P, W x*h (ρ x) := by
      simp [ZMod.card_units_eq_totient,ρ]
    _ = ∑ v : (ZMod q)ˣ, ∑ x : ZMod P, W x*h ((v:ZMod q)*ρ x) := by
      apply sum_congr rfl; intro v _; exact (shift v).symm
    _ = _ := by
      rw [sum_comm,sum_mul]
      apply sum_congr rfl; intro x _
      rw [← mul_sum,average]; split_ifs <;> simp

private lemma onMod_progression {g m : ℕ} {f : ℕ → ℝ} (hf : OnMod (g*m) f) (k : ℕ) :
    OnMod m (fun i => f (k+g*i)) := by
  intro i
  have h := ((Nat.mod_modEq i m).mul_left' g).add_left k
  change f (k+g*(i%m))=f (k+g*i)
  rw [← hf (k+g*(i%m)),← hf (k+g*i)]; exact congrArg f h

/-- For coprime quotient periods, the product average factors inside each
residue class of the common modulus. -/
theorem mean_fiber_product {g m n : ℕ} (hg : 0<g) (hm : 0 < m) (hn : 0 < n)
    (hc : m.Coprime n) {f h : ℕ → ℝ} (hf : OnMod (g*m) f) (hh : OnMod (g*n) h) :
    mean (g*(m*n)) (fun j => f j*h j) =
      (∑ k∈range g, (∑ i∈range m, f (k+g*i))*(∑ j∈range n, h (k+g*j)))/(g*(m:ℝ)*n) := by
  unfold mean
  rw [sum_fibers hg]
  simp only [Nat.cast_mul,mul_assoc]
  congr 1; apply sum_congr rfl; intro k _
  have H (i) : f (k+g*i)*h (k+g*i)=f (k+g*(i%m))*h (k+g*(i%n)) := by
    exact congrArg₂ (·*·) (onMod_progression hf k i).symm (onMod_progression hh k i).symm
  simp_rw [H]
  rw [sum_crt hm hn hc (fun i j => f (k+g*i)*h (k+g*j))]
  simp_rw [← mul_sum]; rw [← sum_mul]

/-- A fixed small power absorbs the unit-density cost for every modulus. -/
theorem unit_density_power {L : ℕ} (hL : 0<L) :
    (L:ℝ)/L.totient ≤ (1+8/Real.log 2)*(L:ℝ)^(1/8:ℝ) := by
  have hc : 2^L.primeFactors.card ≤ L := by
    calc
      _ = ∏ _p∈L.primeFactors, (2:ℕ) := by simp
      _ ≤ ∏ p∈L.primeFactors,p := prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ L := Nat.le_of_dvd hL (Nat.prod_primeFactors_dvd L)
  have hh : Real.log ((2:ℝ)^L.primeFactors.card) ≤ Real.log L := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hc)
  rw [Real.log_pow] at hh
  have hlog := Real.log_natCast_le_rpow_div L (show (0:ℝ)<1/8 by norm_num)
  have htwo := Real.log_pos (show (1:ℝ)<2 by norm_num)
  have hpow := Real.one_le_rpow (show (1:ℝ)≤L by exact_mod_cast hL) (show (0:ℝ)≤1/8 by norm_num)
  apply (unit_density_cost hL).trans
  have ha : (L.primeFactors.card:ℝ) ≤ (8/Real.log 2)*(L:ℝ)^(1/8:ℝ) := by
    rw [div_mul_eq_mul_div,le_div_iff₀ htwo]
    linarith only [hh,hlog]
  linarith only [ha,hpow]

private theorem sum_residue {q : ℕ} [NeZero q] (f : ℕ → ℝ) :
    ∑ n∈range q, f n = ∑ x : ZMod q, f x.val := by
  apply sum_bij (fun (n : ℕ) _ => (n:ZMod q))
  · simp
  · intro x hx y hy he
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp hx),ZMod.val_natCast_of_lt (mem_range.mp hy)]
      using congrArg ZMod.val he
  · intro y _; exact ⟨y.val,mem_range.mpr y.val_lt,ZMod.natCast_zmod_val _⟩
  · intro n hn; rw [ZMod.val_natCast_of_lt (mem_range.mp hn)]

private theorem units_sum {q : ℕ} [NeZero q] (f : ZMod q → ℝ)
    (hf : ∀ y, ¬IsUnit y → f y=0) :
    ∑ u : (ZMod q)ˣ, f (u:ZMod q) = ∑ x : ZMod q, f x := by
  classical
  calc
    _ = ∑ x ∈ univ.filter IsUnit, f x := by
      apply sum_bij (fun (u : (ZMod q)ˣ) _ => (u:ZMod q))
      · intro u _; exact mem_filter.mpr ⟨mem_univ _,u.isUnit⟩
      · intro u _ v _ huv; exact Units.ext huv
      · intro y hy; obtain ⟨u,rfl⟩ := (mem_filter.mp hy).2; exact ⟨u,mem_univ _,rfl⟩
      · intros; rfl
    _ = _ := by
      rw [sum_filter]; apply sum_congr rfl; intro y _; split_ifs with hu
      · rfl
      · exact (hf y hu).symm

/-- Averaging a nonnegative unit-invariant weight against a periodic function
supported on the units costs at most the reciprocal unit density. -/
theorem weighted_unit_mean {q P : ℕ} (hq : 0<q) (hP : 0<P) (hd : q∣P)
    (W h : ℕ → ℝ) (hn : ∀ n, 0≤W n)
    (hinv : ∀ (u : (ZMod P)ˣ) (x : ZMod P), W ((u:ZMod P)*x).val=W x.val)
    (hmod : OnMod q h) (hs : ∀ n, ¬n.Coprime q → h n=0) :
    |mean P (fun n => W n*h n)| ≤ mean P W * ((q:ℝ)/q.totient) * |mean q h| := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let : NeZero P := ⟨hP.ne'⟩
  let ρ := ZMod.castHom hd (ZMod q)
  have hs' (y : ZMod q) (hy : ¬IsUnit y) : h y.val=0 := by
    apply hs; intro hc
    exact hy (by simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime ..).mpr hc)
  have H := unit_orbit_sum hd (fun x => W x.val) (fun y => h y.val) hinv hs'
  have Hcast (x : ZMod P) : h (ρ x).val=h x.val := by
    have he : ρ x=(x.val:ZMod q) := by rw [← ZMod.natCast_zmod_val x,map_natCast,ZMod.natCast_zmod_val]
    rw [he,ZMod.val_natCast,hmod]
  change (q.totient:ℝ)*(∑ x : ZMod P,W x.val*h (ρ x).val) =
    (∑ x : ZMod P,if IsUnit (ρ x) then W x.val else 0)*(∑ v : (ZMod q)ˣ,h (v:ZMod q).val) at H
  simp_rw [Hcast] at H
  rw [units_sum _ hs'] at H
  let M := ∑ x : ZMod P, if IsUnit (ρ x) then W x.val else 0
  have hM : 0≤M := sum_nonneg (by intro x _; split_ifs <;> simp [hn])
  have hle : M≤∑ x : ZMod P,W x.val := sum_le_sum (by intro x _; split_ifs <;> simp [hn])
  have ha := congrArg abs H
  change |(q.totient:ℝ)*(∑ x : ZMod P,W x.val*h x.val)| = |M*(∑ x : ZMod q,h x.val)| at ha
  rw [abs_mul,abs_mul,abs_of_nonneg (show (0:ℝ)≤q.totient by positivity),abs_of_nonneg hM] at ha
  have hφ : (0:ℝ)<q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have H' : |∑ x : ZMod P,W x.val*h x.val| ≤
      (∑ x : ZMod P,W x.val)/q.totient * |∑ x : ZMod q,h x.val| := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hφ,mul_comm _ (q.totient:ℝ)]
    exact ha.trans_le (mul_le_mul_of_nonneg_right hle (abs_nonneg _))
  unfold mean
  rw [sum_residue,sum_residue,sum_residue,abs_div,abs_div,abs_of_nonneg (show (0:ℝ)≤P by positivity),
    abs_of_nonneg (show (0:ℝ)≤q by positivity)]
  apply (div_le_div_of_nonneg_right H' (Nat.cast_nonneg P)).trans_eq
  field_simp [Nat.cast_ne_zero.mpr hq.ne']

private lemma partial_bound {f : ℕ → ℝ} {B : ℝ} (hf : ∀ n, |f n|≤B) (k r : ℕ) :
    |∑ n∈range r,f (k+n)| ≤ r*B := by
  apply (abs_sum_le_sum_abs ..).trans
  simpa using (sum_le_sum (s:=range r) (fun i _ => hf (k+i)))

/-- An incomplete period costs at most twice its length times the uniform norm. -/
theorem finite_period_error {d P : ℕ} (hd : 0<d) (hP : 0<P) (hdiv : d∣P)
    {f : ℕ → ℝ} (hf : OnMod d f) {B : ℝ} (hB : ∀ n, |f n|≤B) (X : ℕ) :
    |(∑ n∈range X,f n)-(X:ℝ)*mean P f| ≤ 2*d*B := by
  rw [mean_lift hd hP hdiv hf]
  let q := X/d
  let r := X%d
  have hX : d*q+r=X := Nat.div_add_mod X d
  have hB₀ := (abs_nonneg _).trans (hB 0)
  have hd' : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hmean : |mean d f| ≤ B := by
    rw [mean,abs_div,abs_of_pos hd',div_le_iff₀ hd',mul_comm]
    simpa only [zero_add] using partial_bound hB 0 d
  have hwhole : ∑ n∈range (d*q),f n=(d*q:ℕ)*mean d f := by
    rw [sum_fibers hd]
    have hh (i j : ℕ) : f (i+d*j)=f i := by rw [← hf (i+d*j),Nat.add_mul_mod_self_left,hf]
    simp_rw [hh,sum_const,card_range,nsmul_eq_mul]
    rw [← mul_sum,mean,Nat.cast_mul]; field_simp
  rw [← hX,sum_range_add,hwhole,Nat.cast_add,add_mul,add_sub_add_left_eq_sub]
  have htail := (abs_sub _ _).trans (add_le_add (partial_bound hB (d*q) r)
    (show |(r:ℝ)*mean d f|≤r*B by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg r (α:=ℝ))];
                                   exact mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)))
  have hr : (r:ℝ)≤d := by exact_mod_cast (Nat.mod_lt X hd).le
  linarith only [htail,mul_le_mul_of_nonneg_right hr hB₀]

/-- Bound the endpoint cost of squaring a finite sum of periodic functions.
Each pair uses only the product of its own two periods. -/
theorem finite_period_square {ι : Type*} (s : Finset ι) (period : ι → ℕ)
    (f : ι → ℕ → ℝ) {P D : ℕ} (hP : 0<P) (hp : ∀ i∈s, 0<period i ∧ period i≤D)
    (hdiv : ∀ i∈s, ∀ j∈s, period i*period j∣P)
    (hf : ∀ i∈s, OnMod (period i) (f i)) {B : ℝ} (hB : 0≤B)
    (hb : ∀ i∈s, ∀ n, |f i n|≤B) (X : ℕ) :
    (∑ n∈range X,(∑ i∈s,f i n)^2) ≤ (X:ℝ)*mean P (fun n => (∑ i∈s,f i n)^2)
      + (s.card:ℝ)^2*(2*(D:ℝ)^2*B^2) := by
  classical
  have H (i) (hi : i∈s) (j) (hj : j∈s) : ∑ n∈range X, f i n*f j n ≤
      (X:ℝ)*mean P (fun n => f i n*f j n) + 2*(D:ℝ)^2*B^2 := by
    have ht : OnMod (period i*period j) (fun n => f i n*f j n) := by
      intro n
      exact congrArg₂ (·*·) (onMod_lift (Nat.dvd_mul_right (period i) (period j)) (hf i hi) n)
        (onMod_lift (Nat.dvd_mul_left (period j) (period i)) (hf j hj) n)
    have hsup (n) : |f i n*f j n|≤B^2 := by rw [abs_mul,pow_two]; gcongr <;> apply hb <;> assumption
    have h := (le_abs_self _).trans (finite_period_error (Nat.mul_pos (hp _ hi).1 (hp _ hj).1)
      hP (hdiv i hi j hj) ht hsup X)
    have hper : ((period i*period j:ℕ):ℝ)≤(D:ℝ)^2 := by
      exact_mod_cast (show period i*period j≤D^2 by rw [pow_two]; exact Nat.mul_le_mul (hp _ hi).2 (hp _ hj).2)
    linarith only [h,mul_le_mul_of_nonneg_right hper (sq_nonneg B)]
  have expand (Q : ℕ) : ∑ n∈range Q,(∑ i∈s,f i n)^2 =
      ∑ i∈s, ∑ j∈s, ∑ n∈range Q,f i n*f j n := by
    simp_rw [pow_two,sum_mul_sum]; rw [sum_comm]
    apply sum_congr rfl; intro i _; rw [sum_comm]
  rw [expand,mean,expand]
  calc
    _ ≤ ∑ i∈s,∑ j∈s,((X:ℝ)*mean P (fun n => f i n*f j n)+2*(D:ℝ)^2*B^2) :=
      sum_le_sum (fun i hi => sum_le_sum (fun j hj => H i hi j hj))
    _ = _ := by
      simp only [sum_add_distrib,mean,← mul_sum,← sum_div,sum_const,nsmul_eq_mul]; ring

end Arxiv.«2501.03234».ThetaPeriodMeans
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.finite_period_error
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.finite_period_square
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.weighted_unit_mean
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.sum_crt
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.mean_mul_coprime
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.sum_fibers
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.mean_lift
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.onMod_lift
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.onMod_prod
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.mean_prime_product
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.unit_density_cost
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.unit_orbit_sum
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.mean_fiber_product
#print axioms Arxiv.«2501.03234».ThetaPeriodMeans.unit_density_power
