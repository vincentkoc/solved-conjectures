import Green33DenseModulus

/-! Strict cyclic covers with arbitrary cofactors of the seed modulus. -/

open Finset Filter Green33StrictReduction
open scoped Pointwise Topology

namespace Green33SeedMultiples

private lemma digit {c l p : ℤ} (hp : 0 < p) (hc : c*l=p+1) (x : ℤ) :
    ∃ a b : ℤ, 0 ≤ a ∧ a < p ∧ x=c*a+p*b := by
  let y := l*x
  refine ⟨y%p,c*(y/p)-x,Int.emod_nonneg _ hp.ne',Int.emod_lt_of_pos _ hp,?_⟩
  calc
    x = c*y-p*x := by dsimp only [y]; linear_combination -x*hc
    _ = c*(y%p+p*(y/p))-p*x := by rw [Int.emod_add_mul_ediv]
    _ = _ := by ring

/-- Varying the low digit accommodates a cofactor in any residue class. -/
theorem two_digits {c i d h l m p q : ℤ} (hq : 0 < q) (hpq : q ≤ p) (hh : 0 < h)
    (hbase : c*m=p+1) (hcarry : d*h=i*(p-q)+c) (hunit : d*l=q+1) (x : ℤ) :
    ∃ t u : ℤ, 0 ≤ t ∧ t < p+h ∧ 0 ≤ u ∧ u < p+h ∧
      ∃ e : ℤ, x=(c+i*p)*t+(c+(i+d)*p)*u+p*q*e := by
  obtain ⟨a,b,ha,hap,hx⟩ := digit (lt_of_lt_of_le hq hpq) hbase x
  obtain ⟨v,e,hv,hvq,hb⟩ := digit hq hunit (b-i*a-d*h)
  by_cases hc : v+h≤a
  · refine ⟨a-v-h,v+h,by omega,by omega,by omega,by omega,e,?_⟩
    linear_combination hx+p*hb
  · refine ⟨a+p-v,v,by omega,by omega,hv,by omega,e-i,?_⟩
    linear_combination hx+p*hb+p*hcarry

/-- The determinant of the two weighted arms is c times their slope gap. -/
theorem change_modulus {c i j p q n v e t u x : ℤ}
    (hδ : n-p*q=c*(j-i)*v) (hx : x=(c+i*p)*t+(c+j*p)*u+p*q*e) :
    x=(c+i*p)*(t-j*e*v)+(c+j*p)*(u+i*e*v)+n*e := by
  linear_combination hx-e*hδ

/-- For every target residue the positive digit c has a bounded value and
gives compatible factor residues modulo cL, including nonunit target residues. -/
theorem factor_classes {L : ℤ} (hL : 0 < L) (n : ℤ) :
    ∃ c a b : ℤ, 1 ≤ c ∧ c ≤ L ∧
      ∀ p q : ℤ, c*L ∣ p-a → c*L ∣ q-b →
        c ∣ p+1 ∧ L ∣ q+1 ∧ L ∣ p-q-c ∧ c*L ∣ n-p*q := by
  let c := 1+(-n)%L
  let a := c-1
  let b := -n-c
  have h₁ := Int.emod_nonneg (-n) hL.ne'
  have h₂ := Int.emod_lt_of_pos (-n) hL
  have base : n+c-1 = L*(-((-n)/L)) := by
    have := Int.emod_add_mul_ediv (-n) L
    dsimp [c]; linarith
  refine ⟨c,a,b,by dsimp [c]; omega,by dsimp [c]; omega,?_⟩
  rintro p q ⟨v,hv⟩ ⟨w,hw⟩
  dsimp only [a] at hv
  dsimp only [b] at hw
  refine ⟨⟨1+L*v,?_⟩,⟨(-n)/L+c*w,?_⟩,⟨-((-n)/L)+c*(v-w),?_⟩,?_⟩
  · linear_combination hv
  · linear_combination hw-base
  · linear_combination hv-hw+base
  · refine ⟨-((-n)/L) - w*(c-1)-v*q,?_⟩
    linear_combination -q*hv-(c-1)*hw+c*base

private lemma next_residue (T : ℤ) (hT : 0 < T) (a r : ℤ) :
    ∃ x : ℤ, T ∣ x-a ∧ r < x ∧ x ≤ r+T := by
  let x := a+T*((r-a)/T+1)
  have h := Int.emod_add_mul_ediv (r-a) T
  have h₁ := Int.emod_nonneg (r-a) hT.ne'
  have h₂ := Int.emod_lt_of_pos (r-a) hT
  refine ⟨x,⟨(r-a)/T+1,by dsimp [x]; ring⟩,?_⟩
  dsimp [x]; constructor <;> linarith

/-- Uniform close factors in arbitrary prescribed residue classes. -/
theorem factors_in_classes (T : ℤ) (hT : 0 < T) :
    ∃ C : ℤ, 1 ≤ C ∧ ∀ (n : ℕ) (a b : ℤ),
      let r : ℤ := n.sqrt
      let u : ℤ := n.sqrt.sqrt+1
      ∃ p q : ℤ, T ∣ p-a ∧ T ∣ q-b ∧ r ≤ p ∧ p-r ≤ C*u ∧
        1 ≤ p-q ∧ p-q ≤ C*u ∧ 0 ≤ n-p*q ∧ n-p*q ≤ C*u := by
  let K := 2*(T+1)
  let C := 4*T*K+3*T^2+2*K+4*T+1
  have hK : 0 < K := by dsimp [K]; omega
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_pos hT hK,sq_nonneg T]
  refine ⟨C,hC,?_⟩
  intro n a b r u
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hu : 1 ≤ u := by dsimp [u]; exact le_add_of_nonneg_left (Int.natCast_nonneg _)
  have hrn : r^2 ≤ n := by dsimp [r]; exact_mod_cast Nat.sqrt_le' n
  have hnr : (n:ℤ) < (r+1)^2 := by dsimp [r]; exact_mod_cast Nat.lt_succ_sqrt' n
  have hru : r < u^2 := by dsimp [r,u]; exact_mod_cast Nat.lt_succ_sqrt' n.sqrt
  obtain ⟨y,hy,hry,hyT⟩ := next_residue T hT b r
  obtain ⟨x,hx,hyx,hxT⟩ := next_residue T hT a y
  -- Moving the two factors in opposite directions crosses n within one step of length T.
  let B := x*y-n
  have hB : 0 ≤ B := by
    have := mul_le_mul (by omega : r+1 ≤ x) (by omega : r+1 ≤ y)
      (by omega : 0 ≤ r+1) (by omega : 0 ≤ x)
    dsimp [B]; nlinarith only [this,hnr]
  let s : ℤ := B.toNat.sqrt
  have hs : 0 ≤ s := Int.natCast_nonneg _
  have hs2 : s^2 ≤ B := by
    rw [← Int.toNat_of_nonneg hB]; dsimp only [s]; exact_mod_cast Nat.sqrt_le' B.toNat
  have hBs : B < (s+1)^2 := by
    rw [← Int.toNat_of_nonneg hB]; dsimp only [s]; exact_mod_cast Nat.lt_succ_sqrt' B.toNat
  have hBmax : B ≤ 4*T*(r+T) := by
    have h := mul_le_mul (by omega : x ≤ r+2*T) (by omega : y ≤ r+2*T)
      (by omega : 0 ≤ y) (by omega : 0 ≤ r+2*T)
    dsimp [B]; nlinarith only [h,hrn]
  have hU : 1 ≤ u^2 := by nlinarith [sq_nonneg (u-1)]
  have hbig : r+T ≤ (T+1)*u^2 := by
    nlinarith only [hru,mul_le_mul_of_nonneg_left hU hT.le]
  have hsK : s ≤ K*u := by
    have h := mul_le_mul_of_nonneg_left hbig (by omega : 0 ≤ 4*T)
    have h₂ : 4*T*((T+1)*u^2) ≤ (K*u)^2 := by
      dsimp [K]; nlinarith only [mul_nonneg (by omega : 0 ≤ T+1) (sq_nonneg u)]
    exact (sq_le_sq₀ hs (by positivity : 0 ≤ K*u)).mp (hs2.trans (hBmax.trans (h.trans h₂)))
  obtain ⟨z,hz',hsz,hzT⟩ := next_residue T hT 0 s
  have hz : T ∣ z := by simpa using hz'
  have hgap : (x-y)*z ≤ T*z := mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hδ : (n:ℤ)-(x+z)*(y-z)=z^2+(x-y)*z-B := by dsimp [B]; ring
  have hlow : 0 ≤ (n:ℤ)-(x+z)*(y-z) := by
    rw [hδ]
    have := mul_self_le_mul_self (by omega : 0 ≤ s+1) (by omega : s+1 ≤ z)
    nlinarith only [this,hBs,mul_nonneg (by omega : 0 ≤ x-y) (by omega : 0 ≤ z)]
  have hhi : (n:ℤ)-(x+z)*(y-z) ≤ 3*T*s+2*T^2 := by
    rw [hδ]
    have := mul_self_le_mul_self (by omega : 0 ≤ z) hzT
    nlinarith only [this,hgap,hs2,mul_le_mul_of_nonneg_left hzT hT.le]
  have hconst := le_mul_of_one_le_right (show 0 ≤ 3*T^2+4*T+1 by positivity) hu
  have hTK := mul_le_mul_of_nonneg_left hsK (show 0 ≤ 3*T by omega)
  have htku : 0 ≤ T*(K*u) := by positivity
  have hku : 0 ≤ K*u := by positivity
  refine ⟨x+z,y-z,?_,?_,by omega,?_,by omega,?_,hlow,?_⟩
  · rw [show x+z-a=x-a+z by ring]; exact dvd_add hx hz
  · rw [show y-z-b=y-b-z by ring]; exact dvd_sub hy hz
  · dsimp only [C]; nlinarith only [hxT,hyT,hzT,hsK,hconst,htku,hku,sq_nonneg T,hT]
  · dsimp only [C]; nlinarith only [hxT,hzT,hsK,hconst,htku,sq_nonneg T,hT]
  · dsimp only [C]; nlinarith only [hhi,hTK,hconst,htku,hku,sq_nonneg T,hT]

private lemma winding {c p q n H i j t u x e : ℤ}
    (hc : 0 < c) (hcp : c ≤ p) (hq : 0 < q) (hp : p ≤ 2*q) (hn : n ≤ 2*(p*q))
    (hi : 0 ≤ i) (hij : i ≤ j) (hj : j ≤ H)
    (ht : 0 ≤ t) (htp : t ≤ 2*p) (hu : 0 ≤ u) (hup : u ≤ 2*p)
    (hx : 0 ≤ x) (hxn : x < n) (he : x=(c+i*p)*t+(c+j*p)*u+p*q*e) :
    |e| ≤ 8*(H+1) := by
  have hpp : 1 ≤ p := by omega
  have hppos : 0 < p := by omega
  have hH : 0 ≤ H := hi.trans (hij.trans hj)
  have hpqpos : 0 < p*q := mul_pos (by omega) hq
  have hw (a : ℤ) (ha : 0 ≤ a) (haH : a ≤ H) (b : ℤ) (hb : 0 ≤ b) (hbp : b ≤ 2*p) :
      (c+a*p)*b ≤ 4*(H+1)*(p*q) := by
    have h1 : c+a*p ≤ (H+1)*p := by
      have := mul_le_mul_of_nonneg_right haH (by omega : 0 ≤ p)
      linarith
    have h2 := mul_le_mul h1 hbp hb (by positivity : 0 ≤ (H+1)*p)
    have h3 := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (H+1)*p)
    nlinarith only [h2,h3]
  have hiw := hw i hi (hij.trans hj) t ht htp
  have hjw := hw j (hi.trans hij) hj u hu hup
  have hlow : -(8*(H+1))*(p*q) ≤ e*(p*q) := by linarith [he,hiw,hjw]
  have hhigh : e*(p*q) ≤ 2*(p*q) := by
    have a : 0 ≤ (c+i*p)*t := by positivity
    have hj0 : 0 ≤ j := hi.trans hij
    have b : 0 ≤ (c+j*p)*u := by positivity
    linarith
  have hL := (le_of_mul_le_mul_right hlow hpqpos)
  have hU := (le_of_mul_le_mul_right hhigh hpqpos)
  exact abs_le.mpr ⟨hL,by omega⟩

/-- Winding shifts of either sign fit in one interval for every slope pair. -/
theorem weighted_pair {c p q n i j H E : ℤ}
    (hc : 0 < c) (hcE : c ≤ E) (hq : 0 < q) (hpq : q ≤ p) (hp : p ≤ 2*q) (hn : n ≤ 2*(p*q))
    (hi : 0 ≤ i) (hij : i < j) (hj : j ≤ H)
    (hbase : c ∣ p+1) (hdq : j-i ∣ q+1) (hcon : j-i ∣ p-q-c)
    (hdi : j-i ∣ i+1) (hdn : c*(j-i) ∣ n-p*q)
    (hside : 1 ≤ p-q) (hE : p-q ≤ E) (hδ : 0 ≤ n-p*q) (hδE : n-p*q ≤ E)
    (hfit : (H+1)*E ≤ p) (x : ℤ) :
    let R := (8*(H+1)^2+H+1)*E
    ∃ t u e : ℤ, -R ≤ t ∧ t < p+R ∧ -R ≤ u ∧ u < p+R ∧
      x=(c+i*p)*t+(c+j*p)*u+n*e := by
  intro R
  let d := j-i
  have hd : 0 < d := by dsimp [d]; omega
  have hH : 0 ≤ H := hi.trans (hij.le.trans hj)
  have hEp : 0 < E := by omega
  have hpp : 0 < p := by omega
  have hnp : 0 < n := by nlinarith only [hδ,mul_pos hpp hq]
  have hcarry : d ∣ i*(p-q)+c := by
    rw [show i*(p-q)+c=i*(p-q-c)+(i+1)*c by ring]
    exact dvd_add (dvd_mul_of_dvd_right hcon _) (dvd_mul_of_dvd_left hdi _)
  obtain ⟨h,hh⟩ := hcarry
  obtain ⟨l,hl⟩ := hdq
  obtain ⟨m,hm⟩ := hbase
  obtain ⟨v,hv⟩ := hdn
  have hpos : 0 < h := by
    by_contra! he
    have := mul_nonpos_of_nonneg_of_nonpos hd.le he
    nlinarith only [this,hh,mul_nonneg hi (show 0 ≤ p-q by omega),hc]
  have hsmall : h ≤ (H+1)*E := by
    have h₀ : h ≤ d*h := le_mul_of_one_le_left hpos.le (by omega)
    have h₂ := mul_le_mul_of_nonneg_right (hij.le.trans hj) (by omega : 0 ≤ p-q)
    nlinarith only [h₀,hh,h₂,mul_le_mul_of_nonneg_left hE hH,hcE]
  have hv₀ : 0 ≤ v := by
    by_contra! h
    have := mul_neg_of_pos_of_neg (mul_pos hc (show 0 < j-i by omega)) h
    omega
  have hvE : v ≤ E := by
    have := le_mul_of_one_le_left hv₀ (show 1 ≤ c*(j-i) from mul_pos hc (by omega))
    omega
  let y := x%n
  have hy : 0 ≤ y := Int.emod_nonneg _ hnp.ne'
  have hyn : y < n := Int.emod_lt_of_pos _ hnp
  obtain ⟨t,u,ht,ht',hu,hu',e,he⟩ := two_digits hq hpq hpos hm.symm hh.symm hl.symm y
  have hid : i+d=j := by dsimp [d]; omega
  rw [hid] at he
  have hcp : c ≤ p := by
    have := le_mul_of_one_le_left hEp.le (by omega : 1 ≤ H+1)
    omega
  have heB := winding hc hcp hq hp hn hi hij.le hj ht (by omega) hu (by omega) hy hyn he
  have hcorrect := change_modulus hv he
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

/-- Every finite strict seed lifts to its order times any sufficiently large cofactor. -/
theorem seed_all_cofactors {M : ℕ+} {A : Finset (ZMod M)} (hA : StrictCover A) :
    ∃ K : ℕ, ∀ᶠ P : ℕ+ in atTop,
      ∃ B : Finset (ZMod (M*P)), StrictCover B ∧
        B.card ≤ A.card*(P.val.sqrt + K*(P.val.sqrt.sqrt+1)) := by
  classical
  obtain ⟨L,H,hL,f,hfi,hf,hgap⟩ := Green33DenseModulus.slopes A
  -- One grid works for the varying low digit c and keeps the overhead uniform in P.
  let T := L.factorial*L
  have hT : 0 < T := Nat.mul_pos (Nat.factorial_pos _) hL
  obtain ⟨C₀,hC₀,rect⟩ := factors_in_classes (T:ℤ) (by exact_mod_cast hT)
  let C := C₀+L
  have hC : 1 ≤ C := by dsimp [C]; omega
  let F := 8*(H+1)^2+H+1
  let K := (1+2*F)*C.toNat
  refine ⟨K,?_⟩
  filter_upwards [tendsto_PNat_val_atTop_atTop.eventually (eventually_root_small ((H+4)*C.toNat))]
    with P hlarge
  let r : ℤ := P.val.sqrt
  let u : ℤ := P.val.sqrt.sqrt + 1
  let E := C*u
  obtain ⟨c,a,b,hc,hcL,classes⟩ := factor_classes (by exact_mod_cast hL : (0:ℤ)<L) P.val
  obtain ⟨p,q,hpT,hqT,hrp,hper₀,hside,hside₀,hδ,hδ₀⟩ := rect P.val a b
  have hcast : (c.toNat:ℤ)=c := Int.toNat_of_nonneg (by omega)
  have hfac : c.toNat ∣ L.factorial := Nat.dvd_factorial (by omega) (by omega)
  have hfaci : c ∣ (L.factorial:ℤ) := by
    rw [← hcast]; exact_mod_cast hfac
  have hdT : c*(L:ℤ) ∣ (T:ℤ) := by simpa [T] using mul_dvd_mul_right hfaci (L:ℤ)
  obtain ⟨hbase,hqL,hcon,hprod⟩ := classes p q (hdT.trans hpT) (hdT.trans hqT)
  have hu : 1 ≤ u := by dsimp [u]; exact le_add_of_nonneg_left (Int.natCast_nonneg _)
  have hCL : C₀*u ≤ E := by
    dsimp only [C,E]; nlinarith only [mul_nonneg (Int.natCast_nonneg L) (show 0 ≤ u by omega)]
  have hper := hper₀.trans hCL
  have hside' := hside₀.trans hCL
  have hδ' := hδ₀.trans hCL
  have hcE : c ≤ E := by
    have h := le_mul_of_one_le_right (show 0 ≤ C by omega) hu
    change c ≤ C*u; dsimp only [C] at *; omega
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
  let R := (F:ℤ)*E
  let I := Ico (-R) (p+R)
  let w (a : A) := c+f a*p
  have hit {a b : A} (hab : f a < f b) (x : ℤ) :
      ∃ t ∈ I, ∃ u ∈ I, ∃ e : ℤ, x=w a*t+w b*u+P.val*e := by
    obtain ⟨hdL,hdi⟩ := hgap a b hab
    obtain ⟨t,v,e,h₁,h₂,h₃,h₄,he⟩ := weighted_pair (by omega) hcE hq (by omega) hpp hnn
      (hf a).1 hab (hf b).2 hbase (hdL.trans hqL) (hdL.trans hcon) hdi ((mul_dvd_mul_left c hdL).trans hprod)
      hside hside' hδ hδ' hfit x
    have hR : R=(8*((H:ℤ)+1)^2+H+1)*E := by simp [R,F]
    exact ⟨t,mem_Ico.mpr (by simpa only [hR] using And.intro h₁ h₂),
      v,mem_Ico.mpr (by simpa only [hR] using And.intro h₃ h₄),e,he⟩
  obtain ⟨B,hB,hk⟩ := Green33DenseModulus.cyclic_box (P := P) hA w I (fun a b hab x => by
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

/-- Every sufficiently large multiple of the seed order realizes the seed ratio. -/
theorem seed_ratio {M : ℕ+} {A : Finset (ZMod M)} (hA : StrictCover A)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ+ in atTop, M.val ∣ N.val →
      ∃ B : Finset (ZMod N), StrictCover B ∧
        |(B.card:ℝ)/Real.sqrt N-(A.card:ℝ)/Real.sqrt M| < ε := by
  obtain ⟨K,H⟩ := seed_all_cofactors hA
  have h := Green33DenseModulus.ratio_on_multiples (M := M) (L := 1) (k := A.card)
    (K := K) (H.mono (fun P h _ => h)) ε hε
  simpa only [mul_one] using h

/-- The Lewis eighteen-label seed works on all large multiples of 130. -/
theorem quartic_multiples (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ+ in atTop, 130 ∣ N.val →
      ∃ B : Finset (ZMod N), StrictCover B ∧
        |(B.card:ℝ)/Real.sqrt N-18/Real.sqrt 130| < ε := by
  have h := seed_ratio (M := (130:ℕ+)) Green33QuarticSeed.seed_strict ε hε
  change ∀ᶠ N : ℕ+ in atTop, 130 ∣ N.val → ∃ B : Finset (ZMod N), StrictCover B ∧
    |(B.card:ℝ)/Real.sqrt N-(Green33QuarticSeed.seed.card:ℝ)/Real.sqrt 130| < ε at h
  simpa only [Green33QuarticSeed.seed_card,Nat.cast_ofNat] using h

/-- The corresponding finite lower-density certificate has denominator 130. -/
theorem quartic_count :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ X : ℕ,
      X/130 ≤ (Green33DenseModulus.goodOrders (18/Real.sqrt 130) ε X).card+C := by
  classical
  let D : ℕ+ := 130
  intro ε hε
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (quartic_multiples ε hε)
  refine ⟨J.val,?_⟩
  intro X
  let f : ℕ ↪ ℕ := ⟨(D.val*·),fun _ _ h => Nat.eq_of_mul_eq_mul_left D.pos h⟩
  have hsub : (Ico J.val (X/130+1)).map f ⊆ Green33DenseModulus.goodOrders (18/Real.sqrt 130) ε X := by
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
    have hbound := (Nat.le_div_iff_mul_le D.pos).mp (by omega : l ≤ X/130)
    exact Nat.lt_succ_of_le (by simpa [Nat.mul_comm] using hbound)
  have hcard := card_le_card hsub
  rw [card_map,Nat.card_Ico] at hcard
  omega

#print axioms two_digits
#print axioms change_modulus
#print axioms factor_classes
#print axioms factors_in_classes
#print axioms weighted_pair
#print axioms seed_all_cofactors
#print axioms seed_ratio
#print axioms quartic_multiples
#print axioms quartic_count

end Green33SeedMultiples
