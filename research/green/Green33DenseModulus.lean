import Green33QuarticSeed

/-! Lifting a finite cyclic strict cover on a full arithmetic progression of orders. -/

open Finset Filter Green33StrictReduction
open scoped Pointwise Topology

namespace Green33DenseModulus

private lemma high_digit (d l q x : ℤ) (hq : 0 < q) (hd : d*l = q+1) :
    ∃ v e : ℤ, 0 ≤ v ∧ v < q ∧ x = d*v+q*e := by
  let y := l*x
  refine ⟨y%q,d*(y/q)-x,Int.emod_nonneg _ hq.ne',Int.emod_lt_of_pos _ hq,?_⟩
  calc
    x = d*y-q*x := by dsimp only [y]; linear_combination -x*hd
    _ = d*(y%q+q*(y/q))-q*x := by rw [Int.emod_add_mul_ediv]
    _ = _ := by ring

/-- The carry from the low digit p is absorbed even when p and q differ.
The two coefficients lie in a common interval of length p+h. -/
theorem rectangular_pair {i d h l p q : ℤ} (hq : 0 < q) (hpq : q ≤ p) (hh : 0 < h)
    (hcarry : d*h = i*(p-q)+1) (hunit : d*l=q+1) (x : ℤ) :
    ∃ t u : ℤ, 0 ≤ t ∧ t < p+h ∧ 0 ≤ u ∧ u < p+h ∧
      ∃ e : ℤ, x = (1+i*p)*t+(1+(i+d)*p)*u+p*q*e := by
  have hp : 0 < p := lt_of_lt_of_le hq hpq
  let a := x%p
  let b := x/p
  have ha : 0 ≤ a := Int.emod_nonneg _ hp.ne'
  have hap : a < p := Int.emod_lt_of_pos _ hp
  have hx : x = a+p*b := (Int.emod_add_mul_ediv x p).symm
  obtain ⟨v,e,hv,hvq,hb⟩ := high_digit d l q (b-i*a-d*h) hq hunit
  by_cases hw : v+h ≤ a
  · refine ⟨a-v-h,v+h,by omega,by omega,by omega,by omega,e,?_⟩
    linear_combination hx+p*hb
  · refine ⟨a+p-v,v,by omega,by omega,hv,by omega,e-i,?_⟩
    linear_combination hx+p*hb+p*hcarry

/-- Replacing pq by any modulus congruent to it modulo the slope gap costs
an explicit shift of the two coefficients. Both error and winding are signed. -/
theorem correct_winding {p q n i j t u e v x : ℤ}
    (herr : n-p*q=(j-i)*v) (hx : x=(1+i*p)*t+(1+j*p)*u+p*q*e) :
    x=(1+i*p)*(t-j*e*v)+(1+j*p)*(u+i*e*v)+n*e := by
  linear_combination hx-e*herr

/-- A uniform winding bound for targets in the perturbed modulus. -/
theorem winding_bound {p q n H i j t u x e : ℤ}
    (hq : 0 < q) (hpq : q ≤ p) (hp : p ≤ 2*q) (hn : n ≤ 2*(p*q))
    (hi : 0 ≤ i) (hij : i ≤ j) (hj : j ≤ H)
    (ht : 0 ≤ t) (htp : t ≤ 2*p) (hu : 0 ≤ u) (hup : u ≤ 2*p)
    (hx : 0 ≤ x) (hxn : x < n) (he : x=(1+i*p)*t+(1+j*p)*u+p*q*e) :
    |e| ≤ 8*(H+1) := by
  have hpp : 1 ≤ p := by omega
  have hppos : 0 < p := by omega
  have hH : 0 ≤ H := hi.trans (hij.trans hj)
  have hpqpos : 0 < p*q := mul_pos (by omega) hq
  have hw (a : ℤ) (ha : 0 ≤ a) (haH : a ≤ H) (b : ℤ) (hb : 0 ≤ b) (hbp : b ≤ 2*p) :
      (1+a*p)*b ≤ 4*(H+1)*(p*q) := by
    have h1 : 1+a*p ≤ (H+1)*p := by
      have := mul_le_mul_of_nonneg_right haH (by omega : 0 ≤ p)
      linarith
    have h2 := mul_le_mul h1 hbp hb (by positivity : 0 ≤ (H+1)*p)
    have h3 := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (H+1)*p)
    nlinarith only [h2,h3]
  have hiw := hw i hi (hij.trans hj) t ht htp
  have hjw := hw j (hi.trans hij) hj u hu hup
  have hlow : -(8*(H+1))*(p*q) ≤ e*(p*q) := by linarith [he,hiw,hjw]
  have hhigh : e*(p*q) ≤ 2*(p*q) := by
    have a : 0 ≤ (1+i*p)*t := by positivity
    have hj0 : 0 ≤ j := hi.trans hij
    have b : 0 ≤ (1+j*p)*u := by positivity
    linarith
  have hL := (le_of_mul_le_mul_right hlow hpqpos)
  have hU := (le_of_mul_le_mul_right hhigh hpqpos)
  exact abs_le.mpr ⟨hL,by omega⟩

private lemma rounded_multiple (L : ℤ) (hL : 0 < L) (x : ℤ) :
    ∃ c : ℤ, L ∣ c ∧ x < c ∧ c ≤ x+L := by
  refine ⟨L*(x/L+1), dvd_mul_right _ _, ?_⟩
  have he := Int.emod_add_mul_ediv x L
  have h₁ := Int.emod_nonneg x hL.ne'
  have h₂ := Int.emod_lt_of_pos x hL
  constructor <;> linarith

private lemma sqrt_bounds (v : ℤ) (hv : 0 ≤ v) :
    ∃ b : ℤ, 0 ≤ b ∧ b^2 ≤ v ∧ v < (b+1)^2 := by
  lift v to ℕ using hv
  refine ⟨v.sqrt, by positivity, ?_, ?_⟩
  · exact_mod_cast Nat.sqrt_le' v
  · exact_mod_cast Nat.lt_succ_sqrt' v

/-- For every input n the two factors have the requested congruences.
The side difference and the product deficit are O_L(n^(1/4)+1). -/
theorem close_factors (L : ℤ) (hL : 0 < L) :
    ∃ C : ℤ, 1 ≤ C ∧ ∀ n : ℕ,
      let r : ℤ := n.sqrt
      let u : ℤ := n.sqrt.sqrt + 1
      ∃ p q : ℤ, L ∣ p ∧ L ∣ q+1 ∧ r ≤ p ∧ p-r ≤ C*u ∧
        1 ≤ p-q ∧ p-q ≤ C*u ∧ 0 ≤ n-p*q ∧ n-p*q ≤ C*u := by
  let K := 2*(L+1)
  let C := (2*L+1)*K + L^2 + 4*K + 5*L + 3
  have hK : 0 < K := by dsimp [K]; omega
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_pos (by omega : 0 < 2*L+1) hK, sq_nonneg L]
  refine ⟨C,hC,?_⟩
  intro n r u
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hu : 1 ≤ u := by dsimp [u]; exact le_add_of_nonneg_left (Int.natCast_nonneg _)
  have hrn : r^2 ≤ n := by dsimp [r]; exact_mod_cast Nat.sqrt_le' n
  have hnr : (n:ℤ) < (r+1)^2 := by dsimp [r]; exact_mod_cast Nat.lt_succ_sqrt' n
  have hru : r < u^2 := by dsimp [r,u]; exact_mod_cast Nat.lt_succ_sqrt' n.sqrt
  obtain ⟨c₀,hc₀,hc₁,hc₂⟩ := rounded_multiple L hL r
  let c := c₀+L
  have hc : L ∣ c := dvd_add hc₀ (dvd_refl L)
  have hcmin : r+2 ≤ c := by dsimp [c]; omega
  have hcmax : c ≤ r+2*L := by dsimp [c]; omega
  let B := c*(c-1)-n
  have hB : 0 ≤ B := by
    have := mul_le_mul (show r+1 ≤ c by omega) (show r+1 ≤ c-1 by omega)
      (by omega : 0 ≤ r+1) (by omega : 0 ≤ c)
    dsimp [B]; nlinarith
  obtain ⟨b,hb,hbs,hbs'⟩ := sqrt_bounds B hB
  have hBmax : B ≤ 4*L*(r+L) := by
    have h := mul_self_le_mul_self (by omega : 0 ≤ c) hcmax
    dsimp [B]; nlinarith only [h,hrn,hcmin,hr]
  have hU : 1 ≤ u^2 := by nlinarith [sq_nonneg (u-1)]
  have hbig : r+L ≤ (L+1)*u^2 := by
    nlinarith only [hru,mul_le_mul_of_nonneg_left hU hL.le]
  have hbKU : b ≤ K*u := by
    have a := mul_le_mul_of_nonneg_left hbig (by omega : 0 ≤ 4*L)
    have bnd : 4*L*((L+1)*u^2) ≤ (K*u)^2 := by
      dsimp [K]; nlinarith only [mul_nonneg (by omega : 0 ≤ L+1) (sq_nonneg u)]
    have hsq := hbs.trans (hBmax.trans (a.trans bnd))
    have hKu : 0 ≤ K*u := mul_nonneg hK.le (by omega)
    exact (sq_le_sq₀ hb hKu).mp hsq
  obtain ⟨z,hzL,hbz,hzmax⟩ := rounded_multiple L hL b
  let p := c+z
  let q := c-1-z
  have hp : L ∣ p := dvd_add hc hzL
  have hq : L ∣ q+1 := by simpa [q,sub_add_eq_add_sub] using dvd_sub hc hzL
  have hδ : (n:ℤ)-p*q = z^2+z-B := by dsimp only [p,q,B]; ring
  have hlδ : 0 ≤ (n:ℤ)-p*q := by
    rw [hδ]
    have h := mul_self_le_mul_self (by omega : 0 ≤ b+1) (show b+1 ≤ z by omega)
    nlinarith only [h,hbs',hbz,hb]
  have hδ' : (n:ℤ)-p*q ≤ (2*L+1)*b+L^2+L := by
    rw [hδ]
    have h := mul_self_le_mul_self (by omega : 0 ≤ z) hzmax
    nlinarith only [h,hbs,hzmax]
  have hlim : (2*L+1)*b ≤ (2*L+1)*K*u := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hbKU (by omega)
  have hconst : L^2+5*L+3 ≤ (L^2+5*L+3)*u :=
    le_mul_of_one_le_right (by positivity) hu
  have hprod : 0 ≤ (2*L+1)*K*u := by positivity
  have hKu : 0 ≤ K*u := by positivity
  refine ⟨p,q,hp,hq,by dsimp [p]; omega,?_,by dsimp [p,q]; omega,?_,hlδ,?_⟩
  · dsimp only [p,C]; nlinarith only [hcmax,hzmax,hbKU,hconst,hprod,hKu,sq_nonneg L,hL]
  · dsimp only [p,q,C]; nlinarith only [hzmax,hbKU,hconst,hprod,hKu,sq_nonneg L,hL]
  · dsimp only [C]; nlinarith only [hδ',hlim,hconst,hprod,hKu,hL]

/-- A single interval for both coefficients, with overhead linear in the
side difference and the product deficit, uniformly for slopes up to H. -/
theorem perturbed_pair {p q n i j H E : ℤ}
    (hq : 0 < q) (hpq : q ≤ p) (hp : p ≤ 2*q) (hn : n ≤ 2*(p*q))
    (hi : 0 ≤ i) (hij : i < j) (hj : j ≤ H)
    (hdp : j-i ∣ p) (hdq : j-i ∣ q+1) (hdi : j-i ∣ i+1) (hdn : j-i ∣ n)
    (hside : 1 ≤ p-q) (hE : p-q ≤ E) (hδ : 0 ≤ n-p*q) (hδE : n-p*q ≤ E)
    (hfit : (H+1)*E ≤ p) (x : ℤ) :
    let R := (8*(H+1)^2+H+1)*E
    ∃ t u e : ℤ, -R ≤ t ∧ t < p+R ∧ -R ≤ u ∧ u < p+R ∧
      x=(1+i*p)*t+(1+j*p)*u+n*e := by
  intro R
  let d := j-i
  have hd : 0 < d := by dsimp [d]; omega
  have hH : 0 ≤ H := hi.trans (hij.le.trans hj)
  have hEp : 0 < E := by omega
  have hpp : 0 < p := by omega
  have hnp : 0 < n := by nlinarith only [hδ,mul_pos hpp hq]
  have hcarry : d ∣ i*(p-q)+1 := by
    rw [show i*(p-q)+1 = i*(p-(q+1))+(i+1) by ring]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_sub hdp hdq) _) hdi
  obtain ⟨h,hh⟩ := hcarry
  obtain ⟨l,hl⟩ := hdq
  obtain ⟨v,hv⟩ := dvd_sub hdn (dvd_mul_of_dvd_left hdp q)
  have hpos : 0 < h := by
    by_contra! he
    have := mul_nonpos_of_nonneg_of_nonpos hd.le he
    nlinarith only [this,hh,mul_nonneg hi (show 0 ≤ p-q by omega)]
  have hsmall : h ≤ (H+1)*E := by
    have h₀ : h ≤ d*h := le_mul_of_one_le_left hpos.le (by omega)
    have h₂ := mul_le_mul_of_nonneg_right (hij.le.trans hj) (by omega : 0 ≤ p-q)
    nlinarith only [h₀,hh,h₂,mul_le_mul_of_nonneg_left hE hH,hEp]
  have hv₀ : 0 ≤ v := by
    by_contra! h
    have := mul_neg_of_pos_of_neg (show 0 < j-i by omega) h
    omega
  have hvE : v ≤ E := by
    have := le_mul_of_one_le_left hv₀ (show 1 ≤ j-i by omega)
    omega
  let y := x%n
  have hy : 0 ≤ y := Int.emod_nonneg _ hnp.ne'
  have hyn : y < n := Int.emod_lt_of_pos _ hnp
  obtain ⟨t,u,ht,ht',hu,hu',e,he⟩ := rectangular_pair hq hpq hpos hh.symm hl.symm y
  have hid : i+d=j := by dsimp [d]; omega
  rw [hid] at he
  have heB := winding_bound hq hpq hp hn hi hij.le hj ht (by omega) hu (by omega) hy hyn he
  have hcorrect := correct_winding hv he
  have herr (a : ℤ) (ha : 0 ≤ a) (haH : a ≤ H) :
      |a*e*v| ≤ 8*(H+1)^2*E := by
    rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hv₀]
    calc
      _ ≤ (H+1)*(8*(H+1))*E := by gcongr; omega
      _ = _ := by ring
  have hte := abs_le.mp (herr j (hi.trans hij.le) hj)
  have hue := abs_le.mp (herr i hi (hij.le.trans hj))
  have hHE : 0 ≤ (H+1)*E := by positivity
  have hsplit : R = 8*(H+1)^2*E+(H+1)*E := by dsimp [R]; ring
  refine ⟨t-j*e*v,u+i*e*v,e+x/n,by omega,by omega,by omega,by omega,?_⟩
  have hxy := Int.emod_add_mul_ediv x n
  change y+n*(x/n)=x at hxy
  linear_combination hcorrect-hxy

private lemma eventually_root_small (W : ℕ) :
    ∀ᶠ n : ℕ in atTop, W*(n.sqrt.sqrt+1) ≤ n.sqrt := by
  filter_upwards [eventually_ge_atTop (((2*W+2)^2)^2)] with n hn
  have h₁ := Nat.le_sqrt'.mpr hn
  have h₂ := Nat.le_sqrt'.mpr h₁
  have h₃ := Nat.sqrt_le' n.sqrt
  nlinarith only [h₃,Nat.mul_le_mul_right (n.sqrt.sqrt+1) h₂,
    Nat.mul_le_mul_left (n.sqrt.sqrt) h₂,h₂]

/-- Assemble weighted digit sets over the labels of a strict cyclic seed. -/
theorem cyclic_box {M P : ℕ+} {A : Finset (ZMod M)} (hA : StrictCover A)
    (W : A → ℤ) (I : Finset ℤ) (hit : ∀ a b : A, a ≠ b → ∀ z : ℤ,
      ∃ t ∈ I, ∃ u ∈ I, ∃ e : ℤ, z=W a*t+W b*u+P.val*e) :
    ∃ B : Finset (ZMod (M*P)), StrictCover B ∧ B.card ≤ A.card*I.card := by
  classical
  let rep (a : A) (t : ℤ) : ℤ := a.val.val + M.val*(W a*t)
  let arm (v : A × ℤ) : ZMod (M*P) := (rep v.1 v.2 : ℤ)
  let B := (univ ×ˢ I).image arm
  have memB (a : A) {t : ℤ} (ht : t ∈ I) : arm (a,t) ∈ B :=
    mem_image_of_mem _ (mem_product.mpr ⟨mem_univ _,ht⟩)
  let π : ZMod (M*P) →+* ZMod M := ZMod.castHom (show M.val ∣ (M*P).val from dvd_mul_right _ _) _
  have red (a : A) (t : ℤ) : π (arm (a,t)) = a.val := by
    change π ((rep a t : ℤ) : ZMod (M*P)) = _
    rw [map_intCast]
    simp [rep]
  refine ⟨B,?_,by simpa [B,card_product] using (card_image_le (s := univ ×ˢ I) (f := arm))⟩
  intro x
  obtain ⟨a,ha,b,hb,hab,hs⟩ := hA (x.val : ZMod M)
  let i : A := ⟨a,ha⟩
  let j : A := ⟨b,hb⟩
  have hd : (M.val : ℤ) ∣ (x.val : ℤ)-(a.val+b.val : ℤ) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
    simpa using hs
  obtain ⟨v,hv⟩ := hd
  obtain ⟨t,ht,u,hu,e,he⟩ := hit i j (fun h => hab (congrArg Subtype.val h)) v
  refine ⟨_,memB i ht,_,memB j hu,fun h => hab ((red i t).symm.trans ((congrArg π h).trans (red j u))),?_⟩
  have heq : rep i t+rep j u+((M*P).val : ℤ)*e = x.val := by
    change (a.val+M.val*(W i*t) : ℤ)+(b.val+M.val*(W j*u))+((M.val*P.val : ℕ):ℤ)*e=x.val
    push_cast
    linear_combination -hv-(M.val:ℤ)*he
  have h := congrArg (fun z : ℤ => (z : ZMod (M*P))) heq
  have hz : ((M*P).val : ZMod (M*P)) = 0 := ZMod.natCast_self _
  simpa only [arm,Int.cast_natCast,Int.cast_add,Int.cast_mul,ZMod.natCast_zmod_val,hz,zero_mul,add_zero] using h

/-- Bounded injective slopes with a common multiple of all gaps. -/
theorem slopes (A : Type*) [Fintype A] :
    ∃ L H : ℕ, 0 < L ∧ ∃ f : A → ℤ, Function.Injective f ∧
      (∀ a, 0 ≤ f a ∧ f a ≤ H) ∧
      ∀ a b, f a < f b → (f b-f a ∣ (L:ℤ)) ∧ (f b-f a ∣ f a+1) := by
  classical
  obtain ⟨S,hk,hpos,hgap⟩ := Green33DivisibleOrder.height_family (Fintype.card A)
  let E : A ≃ S := (Fintype.equivFin A).trans ((finCongr hk.symm).trans S.equivFin.symm)
  let g (a : A) : ℕ := (E a).val
  let H := S.sup id
  let f (a : A) : ℤ := g a-1
  have hg (a : A) : 0 < g a := hpos _ (E a).property
  have hb (a : A) : g a ≤ H := le_sup (f := id) (E a).property
  refine ⟨H.factorial,H,Nat.factorial_pos _,f,?_,?_,?_⟩
  · intro a b he
    apply E.injective
    apply Subtype.ext
    change g a = g b
    dsimp only [f] at he
    omega
  · intro a
    dsimp only [f]
    have := hg a
    have := hb a
    omega
  · intro a b hab
    have hlt : g a < g b := by dsimp only [f] at hab; omega
    have heq : f b-f a = ((g b-g a:ℕ):ℤ) := by dsimp [f]; rw [Nat.cast_sub hlt.le]; ring
    rw [heq,show f a+1=(g a:ℤ) by dsimp [f]; ring]
    constructor
    · exact_mod_cast Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) ((Nat.sub_le _ _).trans (hb b))
    · exact_mod_cast hgap _ (E a).property _ (E b).property hlt

/-- Every sufficiently large cofactor divisible by L works. Both L and the
fourth-root error coefficient K depend only on the seed. -/
theorem seed_progression {M : ℕ+} {A : Finset (ZMod M)} (hA : StrictCover A) :
    ∃ L K : ℕ, 0 < L ∧ ∀ᶠ P : ℕ+ in atTop, L ∣ P.val →
      ∃ B : Finset (ZMod (M*P)), StrictCover B ∧
        B.card ≤ A.card*(P.val.sqrt + K*(P.val.sqrt.sqrt+1)) := by
  classical
  obtain ⟨L,H,hL,f,hfi,hf,hgap⟩ := slopes A
  obtain ⟨C,hC,rect⟩ := close_factors L (by exact_mod_cast hL)
  let F := 8*(H+1)^2+H+1
  let K := (1+2*F)*C.toNat
  refine ⟨L,K,hL,?_⟩
  filter_upwards [tendsto_PNat_val_atTop_atTop.eventually (eventually_root_small ((H+4)*C.toNat))]
    with P hlarge
  intro hdiv
  let r : ℤ := P.val.sqrt
  let u : ℤ := P.val.sqrt.sqrt + 1
  let E := C*u
  obtain ⟨p,q,hpL,hqL,hrp,hper,hside,hside',hδ,hδ'⟩ := rect P.val
  change r ≤ p at hrp
  change p-r ≤ E at hper
  change p-q ≤ E at hside'
  change (P.val:ℤ)-p*q ≤ E at hδ'
  have hnat : ((C.toNat:ℕ):ℤ)=C := Int.toNat_of_nonneg (by omega)
  have hEpos : 0 < E := by
    dsimp [E,u]; positivity
  have hlarge' : ((H:ℤ)+4)*E ≤ r := by
    dsimp only [E,r,u]
    rw [← hnat]
    exact_mod_cast (by simpa [Nat.mul_assoc] using hlarge :
      (H+4)*(C.toNat*(P.val.sqrt.sqrt+1)) ≤ P.val.sqrt)
  have hHE : 0 ≤ (H:ℤ)*E := mul_nonneg (Int.natCast_nonneg _) hEpos.le
  have hfit : ((H:ℤ)+1)*E ≤ p := by linarith
  have hq : 0 < q := by linarith
  have hpp : p ≤ 2*q := by linarith
  have hnn : (P.val:ℤ) ≤ 2*(p*q) := by
    have := mul_le_mul_of_nonneg_left (show 1 ≤ q by omega) (show 0 ≤ p by omega)
    nlinarith only [this,hδ',hrp,hlarge',hHE,hEpos]
  have hdv : (L:ℤ) ∣ P.val := by exact_mod_cast hdiv
  let R := (F:ℤ)*E
  let I := Ico (-R) (p+R)
  let w (a : A) := 1+f a*p
  have hit {a b : A} (hab : f a < f b) (x : ℤ) :
      ∃ t ∈ I, ∃ u ∈ I, ∃ e : ℤ, x=w a*t+w b*u+P.val*e := by
    obtain ⟨hdL,hdi⟩ := hgap a b hab
    obtain ⟨t,v,e,h₁,h₂,h₃,h₄,he⟩ := perturbed_pair hq (by omega) hpp hnn
      (hf a).1 hab (hf b).2 (hdL.trans hpL) (hdL.trans hqL) hdi (hdL.trans hdv)
      hside hside' hδ hδ' hfit x
    have hR : R=(8*((H:ℤ)+1)^2+H+1)*E := by simp [R,F]
    exact ⟨t,mem_Ico.mpr (by simpa only [hR] using And.intro h₁ h₂),
      v,mem_Ico.mpr (by simpa only [hR] using And.intro h₃ h₄),e,he⟩
  obtain ⟨B,hB,hk⟩ := cyclic_box (P := P) hA w I (fun a b hab x => by
    rcases lt_or_gt_of_ne (fun he => hab (hfi he)) with h | h
    · exact hit h x
    · obtain ⟨v,hv,t,ht,e,he⟩ := hit h x
      exact ⟨t,ht,v,hv,e,by simpa only [add_comm (w b*v) (w a*t)] using he⟩)
  refine ⟨B,hB,hk.trans (Nat.mul_le_mul_left _ ?_)⟩
  have hwidth : p+R-(-R) ≤ r+K*u := by
    have hK : (K:ℤ)=(1+2*(F:ℤ))*C := by simp [K,hnat]
    dsimp only [R]
    rw [hK]
    dsimp only [E] at *
    nlinarith only [hper]
  change (Ico (-R) (p+R)).card ≤ _
  rw [Int.card_Ico]
  apply Int.toNat_le.mpr
  simpa [r,u] using hwidth

private lemma padded_ratios {M : ℕ+} (k K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ P : ℕ+ in atTop,
      let r := P.val.sqrt
      let b := k*(r+1+K*(r.sqrt+1))
      b ≤ (M*P).val ∧ |(b:ℝ)/Real.sqrt (M*P : ℕ+) - (k:ℝ)/Real.sqrt M| < ε := by
  let c := (k:ℝ)/Real.sqrt M
  have hm : 0 < (M:ℝ) := by exact_mod_cast M.pos
  have hm' : 0 < Real.sqrt M := Real.sqrt_pos.mpr hm
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hm'.le
  obtain ⟨J,hJ⟩ := exists_nat_gt (c / ε)
  have hJ' := (div_lt_iff₀ hε).mp hJ
  have H := tendsto_PNat_val_atTop_atTop
  filter_upwards [H.eventually (eventually_root_small (J*(K+1))),
    H.eventually (eventually_root_small (K+1)), H.eventually (eventually_ge_atTop ((2*k)^2))]
    with P h₁ h₂ h₃
  let r := P.val.sqrt
  let u := r.sqrt+1
  let a := 1+K*u
  have ha : a ≤ (K+1)*u := by dsimp [a,u]; nlinarith
  have ha₁ : J*a ≤ r := (Nat.mul_le_mul_left J ha).trans (by simpa [r,u,Nat.mul_assoc] using h₁)
  have ha₂ : a ≤ r := ha.trans h₂
  have hk₂ : 2*k ≤ r := Nat.le_sqrt'.mpr h₃
  have hr := Nat.sqrt_le' P.val
  change r^2 ≤ P.val at hr
  have hb : k*(r+a) ≤ (M*P).val := calc
    k*(r+a) ≤ k*(r+r) := by gcongr
    _ = (2*k)*r := by ring
    _ ≤ r^2 := by rw [sq]; gcongr
    _ ≤ P.val := hr
    _ ≤ (M*P).val := Nat.le_mul_of_pos_left _ M.pos
  have heqb : k*(r+1+K*u)=k*(r+a) := by dsimp only [a]; ring
  change k*(r+1+K*u) ≤ _ ∧ _
  rw [heqb]
  refine ⟨hb,?_⟩
  have hp : 0 < (P:ℝ) := by exact_mod_cast P.pos
  have hp' : 0 < Real.sqrt P := Real.sqrt_pos.mpr hp
  have hlow : (r:ℝ) ≤ Real.sqrt P := Real.le_sqrt_of_sq_le (by exact_mod_cast hr)
  have hhigh : Real.sqrt P ≤ (r:ℝ)+1 := (Real.sqrt_le_iff).mpr ⟨by positivity,
    by exact_mod_cast (Nat.lt_succ_sqrt' P.val).le⟩
  have hroot : Real.sqrt ((M*P:ℕ+):ℝ) = Real.sqrt M * Real.sqrt P := by
    change Real.sqrt ((M.val*P.val:ℕ):ℝ) = _
    rw [Nat.cast_mul,Real.sqrt_mul hm.le]
  have hca : c*(a:ℝ) < ε*Real.sqrt P := calc
    c*(a:ℝ) < ((J:ℝ)*ε)*a := mul_lt_mul_of_pos_right hJ' (by dsimp only [a]; positivity)
    _ = ε*((J*a:ℕ):ℝ) := by push_cast; ring
    _ ≤ ε*(r:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast ha₁) hε.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hε.le
  have hscale : c*Real.sqrt M = k := div_mul_cancel₀ _ hm'.ne'
  have hrew : ((k*(r+a):ℕ):ℝ)/Real.sqrt ((M*P:ℕ+):ℝ) =
      c*((r:ℝ)+a)/Real.sqrt P := by
    rw [hroot]; push_cast; field_simp; linear_combination -((r:ℝ)+a)*hscale
  rw [hrew]
  change |c*((r:ℝ)+a)/Real.sqrt P - c| < ε
  have ham : (1:ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by dsimp [a]; omega)
  have hl : c ≤ c*((r:ℝ)+a)/Real.sqrt P := (le_div_iff₀ hp').mpr
    (mul_le_mul_of_nonneg_left (by linarith) hc)
  have hh : c*((r:ℝ)+a)/Real.sqrt P < c+ε := (div_lt_iff₀ hp').mpr (by
    nlinarith only [hca,mul_le_mul_of_nonneg_left hlow hc])
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- A fourth-root size bound yields exact normalized-size approximation on
the same progression. Padding permits the two-sided tolerance. -/
theorem ratio_on_multiples {M L : ℕ+} {k K : ℕ}
    (H : ∀ᶠ P : ℕ+ in atTop, L.val ∣ P.val → ∃ B : Finset (ZMod (M*P)),
      StrictCover B ∧ B.card ≤ k*(P.val.sqrt+K*(P.val.sqrt.sqrt+1))) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ+ in atTop, (M*L).val ∣ N.val → ∃ B : Finset (ZMod N), StrictCover B ∧
      |(B.card:ℝ)/Real.sqrt N-(k:ℝ)/Real.sqrt M| < ε := by
  classical
  obtain ⟨P₀,hP₀⟩ := eventually_atTop.mp (H.and (padded_ratios (M := M) k K ε hε))
  filter_upwards [eventually_ge_atTop (M*P₀)] with N hN
  rintro ⟨t,ht⟩
  have hn : N.val = M.val*(L.val*t) := by simpa [Nat.mul_assoc] using ht
  have hpos : 0 < L.val*t := by
    by_contra! h
    have := N.pos
    rw [Nat.eq_zero_of_le_zero h,Nat.mul_zero] at hn
    omega
  let P : ℕ+ := ⟨L.val*t,hpos⟩
  have heq : N=M*P := Subtype.ext hn
  subst N
  have hh := hP₀ P (by exact Nat.le_of_mul_le_mul_left hN M.pos)
  obtain ⟨B,hB,hk⟩ := hh.1 (dvd_mul_right L.val t)
  let r := P.val.sqrt
  let b := k*(r+1+K*(r.sqrt+1))
  have hbudget : B.card ≤ b := hk.trans (Nat.mul_le_mul_left _ (by dsimp [r]; omega))
  obtain ⟨T,hBT,_,hTk⟩ := exists_subsuperset_card_eq (subset_univ B) hbudget
    (show b ≤ (univ : Finset (ZMod (M*P))).card by simpa [ZMod.card] using hh.2.1)
  refine ⟨T,?_,hTk ▸ hh.2.2⟩
  intro z
  obtain ⟨a,ha,b,hb,hab,he⟩ := hB z
  exact ⟨a,hBT ha,b,hBT hb,hab,he⟩

/-- Each finite strict seed attains its normalized size at every sufficiently
large multiple of a divisor fixed before the tolerance is chosen. -/
theorem seed_dense_ratio {M : ℕ+} {A : Finset (ZMod M)} (hA : StrictCover A) :
    ∃ D : ℕ+, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ+ in atTop, D.val ∣ N.val →
      ∃ B : Finset (ZMod N), StrictCover B ∧
        |(B.card:ℝ)/Real.sqrt N - (A.card:ℝ)/Real.sqrt M| < ε := by
  obtain ⟨L,K,hL,H⟩ := seed_progression hA
  let l : ℕ+ := ⟨L,hL⟩
  exact ⟨M*l,ratio_on_multiples (M := M) (L := l) H⟩

/-- The quartic seed gives a positive-density progression at coefficient 18/√130. -/
theorem quartic_dense :
    ∃ D : ℕ+, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ+ in atTop, D.val ∣ N.val →
      ∃ B : Finset (ZMod N), StrictCover B ∧
        |(B.card:ℝ)/Real.sqrt N-18/Real.sqrt 130| < ε := by
  have h := seed_dense_ratio (M := (130:ℕ+)) Green33QuarticSeed.seed_strict
  change ∃ D : ℕ+, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ+ in atTop, D.val ∣ N.val →
    ∃ B : Finset (ZMod N), StrictCover B ∧
      |(B.card:ℝ)/Real.sqrt N-(Green33QuarticSeed.seed.card:ℝ)/Real.sqrt 130| < ε at h
  simpa only [Green33QuarticSeed.seed_card,Nat.cast_ofNat] using h

/-- Green 33 is equivalent to near-optimal strict covers on a positive-density
progression for every tolerance. The progression may depend on the tolerance. -/
theorem green_iff_dense_progressions : OrdinaryLimit ↔
    ∀ ε : ℝ, 0 < ε → ∃ D : ℕ+, ∀ᶠ N : ℕ+ in atTop, D.val ∣ N.val →
      ∃ B : Finset (ZMod N), StrictCover B ∧ |(B.card:ℝ)/Real.sqrt N-Real.sqrt 2| < ε := by
  constructor
  · intro h ε hε
    obtain ⟨M,A,hA,hk⟩ := (ordinary_iff_finite_strict.mp h) (ε/2) (by positivity)
    obtain ⟨D,H⟩ := seed_dense_ratio hA
    refine ⟨D,?_⟩
    filter_upwards [H (ε/2) (by positivity)] with N hN
    intro hd
    obtain ⟨B,hB,hr⟩ := hN hd
    have hp : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast N.pos)
    have hmin : Real.sqrt 2 ≤ (B.card:ℝ)/Real.sqrt N :=
      (le_div_iff₀ hp).mpr (by linarith [strict_size_gap hB])
    exact ⟨B,hB,abs_lt.mpr ⟨by linarith,by linarith [(abs_lt.mp hr).2]⟩⟩
  · intro h
    apply ordinary_iff_finite_strict.mpr
    intro ε hε
    obtain ⟨D,H⟩ := h ε hε
    obtain ⟨J,hJ⟩ := eventually_atTop.mp H
    obtain ⟨B,hB,hr⟩ := hJ (D*J) (Nat.le_mul_of_pos_left _ D.pos) (dvd_mul_right _ _)
    exact ⟨D*J,B,hB,by linarith [(abs_lt.mp hr).2]⟩

open Classical in
/-- Positive orders up to X admitting a strict cover within ε of c. -/
noncomputable def goodOrders (c ε : ℝ) (X : ℕ) : Finset ℕ :=
  (range (X+1)).filter fun n => ∃ hn : 0<n, ∃ B : Finset (ZMod (⟨n,hn⟩:ℕ+)),
    StrictCover B ∧ |(B.card:ℝ)/Real.sqrt (n:ℝ)-c| < ε

/-- In every initial segment the number of good orders is at least
floor(X/D) minus a constant depending on the tolerance. -/
theorem quartic_count :
    ∃ D : ℕ+, ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ X : ℕ,
      X/D.val ≤ (goodOrders (18/Real.sqrt 130) ε X).card+C := by
  classical
  obtain ⟨D,H⟩ := quartic_dense
  refine ⟨D,?_⟩
  intro ε hε
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (H ε hε)
  refine ⟨J.val,?_⟩
  intro X
  let f : ℕ ↪ ℕ := ⟨(D.val*·),fun _ _ h => Nat.eq_of_mul_eq_mul_left D.pos h⟩
  have hsub : (Ico J.val (X/D.val+1)).map f ⊆ goodOrders (18/Real.sqrt 130) ε X := by
    intro m hm
    obtain ⟨l,hl,rfl⟩ := mem_map.mp hm
    obtain ⟨hl₁,hl₂⟩ := mem_Ico.mp hl
    have hlpos := lt_of_lt_of_le J.pos hl₁
    let N : ℕ+ := ⟨D.val*l,Nat.mul_pos D.pos hlpos⟩
    have hJN : J ≤ N := hl₁.trans (Nat.le_mul_of_pos_left _ D.pos)
    obtain ⟨B,hB,hr⟩ := hJ N hJN (dvd_mul_right _ _)
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_,N.pos,B,hB,hr⟩
    change D.val*l < X+1
    have hbound := (Nat.le_div_iff_mul_le D.pos).mp (by omega : l ≤ X/D.val)
    exact Nat.lt_succ_of_le (by simpa [Nat.mul_comm] using hbound)
  have hcard := card_le_card hsub
  rw [card_map,Nat.card_Ico] at hcard
  omega

#print axioms rectangular_pair
#print axioms correct_winding
#print axioms winding_bound
#print axioms close_factors
#print axioms perturbed_pair
#print axioms cyclic_box
#print axioms slopes
#print axioms seed_progression
#print axioms ratio_on_multiples
#print axioms seed_dense_ratio
#print axioms quartic_dense
#print axioms green_iff_dense_progressions
#print axioms quartic_count

end Green33DenseModulus
