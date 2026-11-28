import Green33PieceObstruction
import Green33StrictReduction

/-! Three cyclic progressions from an integral approximation to a hexagonal tiling. -/

open Finset Filter
open scoped Pointwise Topology

namespace Green33AllModulusHexagon

/-- A unit fundamental parallelogram of the hexagonal tiling is covered by
the four hexagons centered at its corners, in integer coordinates scaled by n. -/
private lemma cell {n a b : ℤ} (an : 0 ≤ a ∧ a ≤ n) (bn : 0 ≤ b ∧ b ≤ n) :
    ∃ i j : ℤ, let x := a-i*n; let y := b-j*n
      |x| ≤ n ∧ |y| ≤ n ∧ |2*x+y| ≤ n ∧ |x+2*y| ≤ n ∧ |x-y| ≤ n := by
  let good (x y : ℤ) := |x| ≤ n ∧ |y| ≤ n ∧ |2*x+y| ≤ n ∧ |x+2*y| ≤ n ∧ |x-y| ≤ n
  have h : good a b ∨ good (a-n) b ∨ good a (b-n) ∨ good (a-n) (b-n) := by
    simp only [good, abs_le]
    omega
  rcases h with h|h|h|h
  · exact ⟨0,0,by simpa [good] using h⟩
  · exact ⟨1,0,by simpa [good] using h⟩
  · exact ⟨0,1,by simpa [good] using h⟩
  · exact ⟨1,1,by simpa [good] using h⟩

/-- An exact determinant-n lattice close to the hexagonal period lattice
has cyclic quotient. Every residue has a short hexagonal representative. -/
theorem hex_representative (n : ℕ+) (p u v : ℤ) (hp : 0 ≤ p)
    (det : (2*p+1)*v-p*u = n.val) (z : ZMod n) :
    ∃ x y : ℤ, (p*x-(2*p+1)*y : ℤ) ≡ (z.val : ℤ) [ZMOD n.val] ∧
      let R := p+1+|u-p|+|v-2*p|
      |x| ≤ R ∧ |y| ≤ R ∧ |x-y| ≤ R := by
  let N : ℤ := n.val
  have hN : 0 < N := by dsimp [N]; exact_mod_cast n.pos
  let X : ℤ := -2*(z.val : ℤ)
  let Y : ℤ := -(z.val : ℤ)
  let a := v*X-u*Y
  let b := -p*X+(2*p+1)*Y
  obtain ⟨i,j,hai,hbj,h₁,h₂,h₃⟩ := cell
    (n := N) (a := a%N) (b := b%N)
    ⟨Int.emod_nonneg _ hN.ne', (Int.emod_lt_of_pos _ hN).le⟩
    ⟨Int.emod_nonneg _ hN.ne', (Int.emod_lt_of_pos _ hN).le⟩
  let I := a/N+i
  let J := b/N+j
  let A := a%N-i*N
  let B := b%N-j*N
  let x := X-I*(2*p+1)-J*u
  let y := Y-I*p-J*v
  have ha : A = a-I*N := by dsimp [A,I]; have := Int.emod_add_ediv_mul a N; nlinarith
  have hb : B = b-J*N := by dsimp [B,J]; have := Int.emod_add_ediv_mul b N; nlinarith
  have hx : x*N = p*(2*A+B)+A+(u-p)*B := by
    rw [ha,hb]
    dsimp [x,a,b,N]
    rw [← det]
    ring
  have hy : y*N = p*(A+2*B)+(v-2*p)*B := by
    rw [ha,hb]
    dsimp [y,a,b,N]
    rw [← det]
    ring
  have hxy : (x-y)*N = p*(A-B)+A+(u-p)*B-(v-2*p)*B := by
    rw [sub_mul,hx,hy]; ring
  have mulbd (c t : ℤ) (ht : |t| ≤ N) :
      |c*t| ≤ |c| * N := by rw [abs_mul]; gcongr
  have pbd (t : ℤ) (ht : |t| ≤ N) : |p*t| ≤ p*N := by simpa [abs_of_nonneg hp] using mulbd p t ht
  have ubd := mulbd (u-p) B hbj
  have vbd := mulbd (v-2*p) B hbj
  let R := p+1+|u-p|+|v-2*p|
  have cut (s : ℤ) (hs : |s*N| ≤ R*N) : |s| ≤ R := by
    rw [abs_mul,abs_of_pos hN] at hs
    exact (mul_le_mul_iff_left₀ hN).mp hs
  refine ⟨x,y,?_,cut _ ?_,cut _ ?_,cut _ ?_⟩
  · apply Int.modEq_iff_dvd.mpr
    refine ⟨-J,?_⟩
    dsimp [x,y,X,Y]
    rw [← det]
    ring
  · rw [hx]; dsimp [R]
    calc
      _ ≤ |p*(2*A+B)| + |A| + |(u-p)*B| := (abs_add_le ..).trans (by gcongr; apply abs_add_le)
      _ ≤ _ := by nlinarith [pbd _ h₁, mul_nonneg (abs_nonneg (v-2*p)) hN.le]
  · rw [hy]; dsimp [R]
    calc
      _ ≤ |p*(A+2*B)|+|(v-2*p)*B| := abs_add_le ..
      _ ≤ _ := by nlinarith [pbd _ h₂,mul_nonneg (abs_nonneg (u-p)) hN.le]
  · rw [hxy]; dsimp [R]
    calc
      _ ≤ |p*(A-B)|+|A|+|(u-p)*B|+|(v-2*p)*B| := by
        apply (abs_sub ..).trans
        gcongr
        apply (abs_add_le ..).trans
        gcongr
        apply abs_add_le
      _ ≤ _ := by nlinarith [pbd _ h₃]

/-- An arbitrary large integer occurs as the exact lattice determinant with a
hexagonal covering radius within O(sqrt P) of P, where P = floor(sqrt(n/3)). -/
theorem hex_parameters (n : ℕ) (hn : 3 ≤ n) :
    let P := (n/3).sqrt
    ∃ p u v : ℤ, 0 < p ∧ (2*p+1)*v-p*u = n ∧
      p+1+|u-p|+|v-2*p| ≤ (P : ℤ)+120*(P.sqrt+1 : ℕ) ∧
      2*p+1 ≤ 2*((P : ℤ)+2*(P.sqrt+1 : ℕ))+1 := by
  let P := (n/3).sqrt
  let T := P.sqrt
  let L := 3*P^2+9*P-n
  let H := (L/3).sqrt
  have plo : P^2 ≤ n/3 := Nat.sqrt_le' _
  have phi : n/3 < (P+1)^2 := Nat.lt_succ_sqrt' _
  have hpos : 0 < P := by
    by_contra! h
    have e : P=0 := by omega
    rw [e] at phi
    norm_num at phi
    omega
  have low : 3*P^2 ≤ n := by omega
  have phi' : n/3 < P^2+2*P+1 := by nlinarith only [phi]
  have hi : n ≤ 3*P^2+9*P := by omega
  have hL : L+n=3*P^2+9*P := Nat.sub_add_cancel hi
  have hlo : H^2 ≤ L/3 := Nat.sqrt_le' _
  have hhi : L/3 < (H+1)^2 := Nat.lt_succ_sqrt' _
  have hhi' : L/3 < H^2+2*H+1 := by nlinarith only [hhi]
  have tupper : P < (T+1)^2 := Nat.lt_succ_sqrt' _
  have Hsmall : H ≤ 2*(T+1) := by
    by_contra! h
    have hh := Nat.pow_le_pow_left (le_of_lt h) 2
    have bound : H^2 ≤ 3*P := by omega
    nlinarith only [hh,tupper,bound]
  have sq₁ : 3*H^2 ≤ L := by omega
  have sq₂ : L ≤ 3*H^2+6*H+2 := by omega
  let p : ℤ := (P : ℤ)+H
  let q : ℤ := 3*(P : ℤ)+9-3*H
  let e : ℤ := (n : ℤ)-p*q
  let u := 4*p+2+2*e-q
  let v := 2*p+e
  have hlz : (L : ℤ)+n=3*(P : ℤ)^2+9*P := by exact_mod_cast hL
  have hs₁ : 3*(H : ℤ)^2 ≤ L := by exact_mod_cast sq₁
  have hs₂ : (L : ℤ) ≤ 3*(H : ℤ)^2+6*H+2 := by exact_mod_cast sq₂
  have hhs : (H : ℤ) ≤ 2*((T : ℤ)+1) := by exact_mod_cast Hsmall
  have ee : e = 3*(H : ℤ)^2-L-9*H := by dsimp [e,p,q]; linarith only [hlz]
  have he : |e| ≤ 15*(H : ℤ)+2 := by rw [abs_le,ee]; constructor <;> linarith
  have eu : u-p = 6*(H : ℤ)-7+2*e := by dsimp [u,p,q]; ring
  have ev : v-2*p=e := by dsimp [v]; ring
  have hu : |u-p| ≤ 36*(H : ℤ)+11 := by rw [eu,abs_le]; rw [abs_le] at he; omega
  refine ⟨p,u,v,?_,?_,?_,?_⟩
  · dsimp [p]; positivity
  · dsimp [u,v,e]; ring
  · change p+1+|u-p|+|v-2*p| ≤ (P : ℤ)+120*((T+1 : ℕ) : ℤ)
    rw [ev]; push_cast; dsimp [p] at hu ⊢; omega
  · change 2*p+1 ≤ 2*((P : ℤ)+2*((T+1 : ℕ) : ℤ))+1
    push_cast; dsimp [p]; omega

open Green33PieceObstruction Green33StrictReduction

/-- The horizontal, vertical and diagonal arms after projection to the cyclic group. -/
def direction (p : ℤ) : Fin 3 → ℤ := ![-p,2*p+1,-(p+1)]

/-- Extending both ends of each arm supplies distinct witnesses for diagonal sums. -/
def hexBasis (n : ℕ+) (p : ℤ) (R : ℕ) : Finset (ZMod n) :=
  univ.biUnion fun j => progression (-(direction p j : ZMod n)) (direction p j) (R+3)

private lemma arm_mem (n : ℕ+) (p : ℤ) (R : ℕ) (j : Fin 3) {t : ℤ}
    (ht : -1 ≤ t ∧ t ≤ R+1) : ((t*direction p j : ℤ) : ZMod n) ∈ hexBasis n p R := by
  apply mem_biUnion.mpr
  refine ⟨j,mem_univ _,mem_image.mpr ⟨(t+1).toNat, mem_range.mpr (by omega),?_⟩⟩
  have hNat : ((t+1).toNat : ℤ)=t+1 := Int.toNat_of_nonneg (by omega)
  rw [nsmul_eq_mul]
  push_cast
  have hcast : (((t+1).toNat : ℕ) : ZMod n) = (t : ZMod n)+1 := by
    exact_mod_cast congrArg (fun a : ℤ => (a : ZMod n)) hNat
  rw [hcast]; ring

private lemma split_hex (p x y r : ℤ) (hx : |x| ≤ r) (hy : |y| ≤ r) (hd : |x-y| ≤ r) :
    ∃ i j : Fin 3, ∃ a b : ℤ, (0 ≤ a ∧ a ≤ r) ∧ (0 ≤ b ∧ b ≤ r) ∧
      a*direction p i+b*direction p j = p*x-(2*p+1)*y := by
  rw [abs_le] at hx hy hd
  by_cases neg : x ≤ 0 ∧ y ≤ 0
  · exact ⟨0,1,-x,-y,by omega,by omega,by simp [direction]; ring⟩
  by_cases le : x ≤ y
  · exact ⟨0,2,y-x,y,by omega,by omega,by simp [direction]; ring⟩
  · exact ⟨1,2,x-y,x,by omega,by omega,by simp [direction]; ring⟩

private lemma cover_of_parameters (n : ℕ+) (p u v : ℤ) (R : ℕ) (hp : 0 < p)
    (short : 2*(2*p+1) < n.val) (det : (2*p+1)*v-p*u=n.val)
    (radius : p+1+|u-p|+|v-2*p| ≤ R) : StrictCover (hexBasis n p R) := by
  intro z
  obtain ⟨x,y,hz,hx,hy,hd⟩ := hex_representative n p u v hp.le det z
  obtain ⟨i,j,a,b,ha,hb,hs⟩ := split_hex p x y R (hx.trans radius) (hy.trans radius) (hd.trans radius)
  let U : ZMod n := ((a*direction p i : ℤ) : ZMod n)
  let V : ZMod n := ((b*direction p j : ℤ) : ZMod n)
  have eq : U+V=z := by
    dsimp [U,V]; rw [← Int.cast_add,hs]
    simpa using (ZMod.intCast_eq_intCast_iff _ _ n.val).mpr hz
  by_cases same : U=V
  · let d := direction p i
    have hd : ¬ (n.val : ℤ) ∣ 2*d := by
      have h : |2*d| < (n.val : ℤ) ∧ 2*d ≠ 0 := by
        rw [abs_lt]
        fin_cases i <;> simp [d,direction] <;> omega
      intro hdiv
      have hdabs : (n.val : ℤ) ∣ |2*d| := by
        rcases abs_choice (2*d) with e|e <;> rw [e]
        · exact hdiv
        · exact dvd_neg.mpr hdiv
      have := Int.le_of_dvd (abs_pos.mpr h.2) hdabs
      omega
    refine ⟨(((a-1)*d : ℤ) : ZMod n),arm_mem n p R i (by omega),
      (((a+1)*d : ℤ) : ZMod n),arm_mem n p R i (by omega),?_,?_⟩
    · intro h
      have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n.val).mp h
      apply hd
      convert hh using 1; ring
    · rw [← Int.cast_add,← eq,← same]
      dsimp [U,d]
      push_cast; ring
  · exact ⟨U,arm_mem n p R i (by omega),V,arm_mem n p R j (by omega),same,eq⟩

/-- A strict two-basis made of three progressions for every modulus at least 192.
The additive error in the number of labels is of order n^(1/4). -/
theorem three_arms (n : ℕ+) (hn : 192 ≤ n.val) :
    let P := (n.val/3).sqrt
    let R := P+120*(P.sqrt+1)
    ∃ p : ℤ, StrictCover (hexBasis n p R) ∧ (hexBasis n p R).card ≤ 3*(R+3) := by
  let P := (n.val/3).sqrt
  let R := P+120*(P.sqrt+1)
  obtain ⟨p,u,v,hp,det,rad,hstep⟩ := hex_parameters n.val (by omega)
  change p+1+|u-p|+|v-2*p| ≤ (P : ℤ)+120*(P.sqrt+1 : ℕ) at rad
  change 2*p+1 ≤ 2*((P : ℤ)+2*(P.sqrt+1 : ℕ))+1 at hstep
  have hp₈ : 8 ≤ P := Nat.le_sqrt'.mpr (by omega)
  have hsq : P^2 ≤ n.val/3 := Nat.sqrt_le' _
  have ht := Nat.sqrt_le_self P
  have hl : 12*P+10 < n.val := by
    have h₁ : 8*P ≤ P^2 := by simpa [sq] using Nat.mul_le_mul_right P hp₈
    omega
  have hshort : 2*(2*p+1) < n.val := by push_cast at hstep; omega
  refine ⟨p,cover_of_parameters n p u v R hp hshort det (by dsimp [R]; push_cast at *; exact rad),?_⟩
  let S (j : Fin 3) := progression (-(direction p j : ZMod n)) (direction p j) (R+3)
  have hc (j : Fin 3) : (S j).card ≤ R+3 := card_image_le.trans (by simp)
  exact (card_biUnion_le (s := (univ : Finset (Fin 3))) (t := S)).trans (by
    simpa using sum_le_sum (s := (univ : Finset (Fin 3))) (fun i _ => hc i))

/-- A finite lower bound for every ordinary cyclic basis made of three progressions. -/
theorem three_progression_lower {n : ℕ+} {A : Finset (ZMod n)}
    (hA : A+A=univ) (a d : Fin 3 → ZMod n) (l : Fin 3 → ℕ)
    (pieces : A=univ.biUnion fun i => progression (a i) (d i) (l i)) :
    3*n.val ≤ A.card^2+18*A.card := by
  let S (i : Fin 3) := progression (a i) (d i) (l i)
  have sub (i : Fin 3) : S i ⊆ A := by rw [pieces]; exact subset_biUnion_of_mem _ (mem_univ i)
  have cap (i : Fin 3) : (S i+S i).card ≤ 2*A.card :=
    (progression_sum_le _ _ _).trans (Nat.mul_le_mul_left 2 (card_le_card (sub i)))
  have cover (x) (hx : x ∈ A) : ∃ i, x ∈ S i := by
    rw [pieces] at hx
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    exact ⟨i,hi⟩
  have h := cover_count A S cover
  rw [hA,card_univ,ZMod.card,Fin.sum_univ_three] at h
  have := cap 0; have := cap 1; have := cap 2
  omega

private lemma ordinary {n : ℕ+} {A : Finset (ZMod n)} (h : StrictCover A) : A+A=univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨a,ha,b,hb,_,e⟩ := h z
  exact mem_add.mpr ⟨a,ha,b,hb,e⟩

set_option maxHeartbeats 900000 in
/-- The optimal three-progression coefficient is attained with distinct summands
on every sufficiently large modulus, including primes. -/
theorem all_moduli (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ+ in atTop,
    ∃ p : ℤ, ∃ R : ℕ, let A := hexBasis n p R
      StrictCover A ∧ A+A=univ ∧ |(A.card : ℝ)/Real.sqrt n-Real.sqrt 3| < ε := by
  let s (n : ℕ+) := Real.sqrt (n : ℝ)
  let t (n : ℕ+) := Real.sqrt (s n)
  have hs : Tendsto s atTop atTop := Real.tendsto_sqrt_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_PNat_val_atTop_atTop)
  have ht : Tendsto t atTop atTop := Real.tendsto_sqrt_atTop.comp hs
  have small : Tendsto (fun n => 360/t n+369/s n) atTop (𝓝 (0:ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (360:ℝ))).div_atTop ht).add
      ((tendsto_const_nhds (x := (369:ℝ))).div_atTop hs)
  filter_upwards [tendsto_PNat_val_atTop_atTop.eventually (eventually_ge_atTop 192),
    small.eventually_lt_const hε] with n hn hsmall
  let P := (n.val/3).sqrt
  let R := P+120*(P.sqrt+1)
  obtain ⟨p,hA,hk⟩ := three_arms n hn
  let A := hexBasis n p R
  change StrictCover A at hA
  change A.card ≤ 3*(R+3) at hk
  have ho := ordinary hA
  have hl := three_progression_lower ho (fun j => -(direction p j : ZMod n))
    (fun j => (direction p j : ZMod n)) (fun _ => R+3) rfl
  refine ⟨p,R,hA,ho,?_⟩
  change |(A.card : ℝ)/s n-Real.sqrt 3| < ε
  have hn' : (0:ℝ)<n := by exact_mod_cast n.pos
  have spos : 0 < s n := Real.sqrt_pos.mpr hn'
  have tpos : 0 < t n := Real.sqrt_pos.mpr spos
  have ss : (s n)^2 = (n : ℝ) := Real.sq_sqrt hn'.le
  have tt : (t n)^2 = s n := Real.sq_sqrt spos.le
  have sr : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have pp : 3*P^2 ≤ n.val := by have : P^2 ≤ n.val/3 := Nat.sqrt_le' _; omega
  have rp : (3:ℝ)*(P:ℝ)^2 ≤ (n:ℝ) := by exact_mod_cast pp
  have root3 : (3:ℝ)*P ≤ Real.sqrt 3*s n := by
    apply (sq_le_sq₀ (by positivity) (mul_nonneg (Real.sqrt_nonneg _) spos.le)).mp
    rw [mul_pow,mul_pow,sr,ss]; linarith only [rp]
  have rootP : (P:ℝ) ≤ s n := by
    apply (sq_le_sq₀ (by positivity) spos.le).mp
    linarith only [rp,ss,sq_nonneg (P:ℝ)]
  have htP : (P.sqrt:ℝ) ≤ t n := by
    apply (sq_le_sq₀ (by positivity) tpos.le).mp
    rw [tt]
    exact le_trans (by exact_mod_cast Nat.sqrt_le' P : (P.sqrt:ℝ)^2 ≤ (P:ℝ)) rootP
  have lo : Real.sqrt 3*s n ≤ (A.card:ℝ)+9 := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) spos.le) (by positivity)).mp
    rw [mul_pow,sr,ss]
    have hh : 3*(n:ℝ) ≤ (A.card:ℝ)^2+18*A.card := by exact_mod_cast hl
    linarith only [hh]
  have up : (A.card:ℝ) ≤ Real.sqrt 3*s n+360*t n+369 := by
    have hh : (A.card:ℝ) ≤ 3*((P:ℝ)+120*(P.sqrt+1 : ℕ)+3) := by exact_mod_cast hk
    push_cast at hh
    linarith only [hh,htP,root3]
  change 360/t n+369/s n < ε at hsmall
  have cost : 360*t n+369 < ε*s n := by
    calc
      360*t n+369 = (360/t n+369/s n)*s n := by field_simp [ne_of_gt tpos,ne_of_gt spos]; nlinarith only [tt]
      _ < _ := mul_lt_mul_of_pos_right hsmall spos
  rw [abs_lt]
  constructor
  · have h9 : 9 < ε*s n := by linarith only [cost,tpos]
    have hh : (Real.sqrt 3-ε)*s n < A.card := by linarith only [lo,h9]
    linarith only [(lt_div_iff₀ spos).mpr hh]
  · have hh : (A.card:ℝ) < (Real.sqrt 3+ε)*s n := by linarith only [up,cost]
    linarith only [(div_lt_iff₀ spos).mpr hh]

#print axioms all_moduli
#print axioms three_progression_lower
#print axioms three_arms
#print axioms hex_representative
#print axioms hex_parameters

end Green33AllModulusHexagon
