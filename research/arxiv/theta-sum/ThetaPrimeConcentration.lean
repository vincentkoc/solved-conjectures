import ThetaPrimeMeanSquare
import ThetaDenominatorTails

/-! Stretched-exponential prime deviation bounds for the signed theta sum. -/

namespace Arxiv.«2501.03234».ThetaPrimeConcentration

open Finset ThetaReciprocalInversion ThetaDenominatorTails

private noncomputable def err (p : ℕ) : ℝ := |(S p:ℝ)/p-Real.log p/2|
private lemma counting_band : ∃ A : ℝ, 0<A ∧ ∃ B : ℝ, 0≤B ∧ ∀ {N T : ℕ}, 2≤N → 1≤T →
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ N^56≤p ∧ p≤N^64 ∧
      A*(1+Real.log T)^2≤err p) → (s.card:ℝ) ≤ B*(N:ℝ)^64/(T:ℝ)^(1/64:ℝ) := by
  obtain ⟨C,hC,h⟩ := ThetaPrimeMeanSquare.scale_window_control
  obtain ⟨D,hD,hlow⟩ := small_rows_bound
  obtain ⟨B,hB,hvar⟩ := cut_variance
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨C+c*(D+1),by positivity,B,hB,?_⟩
  intro N T hN hT s hs
  obtain ⟨L,hL,hctrl⟩ := h N hN
  let Y := 2*N^52
  let H := above T L
  have hzero (d : ℕ) (hd : d≤T) : H d=0 := by simp [H,above,hd]
  let F := windowExtension H Y
  have hlarge (p : ℕ) (hp : p ∈ s) : 1≤‖F p‖ := by
    obtain ⟨hpr,hlo,hhi,hbad⟩ := hs p hp
    have hY := ThetaPrimeDensity.cutoff_inside hN hlo
    have hcop (d : ℕ) (hd : d ∈ Icc 1 Y) : p.Coprime d :=
      hpr.coprime_iff_not_dvd.mpr (fun hdiv => (lt_of_le_of_lt (mem_Icc.mp hd).2 hY).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 hdiv))
    have hl := hlow hT L hL hcop
    have ht' : ‖windowExtension L Y p‖ ≤ D*(1+Real.log T)^2+‖F p‖ := by
      calc
        _ = ‖(windowExtension L Y p-F p)+F p‖ := by rw [sub_add_cancel]
        _ ≤ _ := (norm_add_le ..).trans (add_le_add hl le_rfl)
    have hh := hctrl p hpr hlo hhi
    change err p≤C+c*‖windowExtension L Y p‖ at hh
    have hV : 1≤(1+Real.log T)^2 := one_le_pow₀ (by linarith [Real.log_nonneg (show 1≤(T:ℝ) by exact_mod_cast hT)])
    by_contra! H'
    nlinarith only [hh,hbad,mul_le_mul_of_nonneg_left ht' hc.le,mul_lt_mul_of_pos_left H' hc,
      mul_le_mul_of_nonneg_left hV hC.le,mul_le_mul_of_nonneg_left hV hc.le]
  have hsub : s ⊆ range (N^64+1) := fun p hp => mem_range.mpr (Nat.lt_succ_of_le (hs p hp).2.2.1)
  calc
    _ = ∑ _ ∈ s, (1:ℝ)^2 := by simp
    _ ≤ ∑ p ∈ s, ‖F p‖^2 := sum_le_sum (fun p hp => pow_le_pow_left₀ zero_le_one (hlarge p hp) 2)
    _ ≤ _ := (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans (hvar hT H hzero N (by omega))

lemma dyadic_cover {X : ℕ} (hX : (256:ℕ)^64≤X) :
    ∃ N : ℕ, 2≤N ∧ N^56≤X/2 ∧ X≤N^64 ∧ N^64≤2^64*X := by
  let r := Nat.nthRoot 64 X
  let N := r+1
  have hr : 256≤r := (Nat.le_nthRoot_iff (by decide : (64:ℕ)≠0)).mpr hX
  have hN : 2≤N := by dsimp [N]; omega
  have hN' : N≤2*r := by dsimp [N]; omega
  have h64 : r^64≤X := Nat.pow_nthRoot_le (Or.inl (by decide))
  refine ⟨N,hN,?_,(Nat.lt_pow_nthRoot_add_one (by decide) X).le,?_⟩
  · have h8 : 2^57≤r^8 := (show (2:ℕ)^57≤256^8 by decide).trans (Nat.pow_le_pow_left hr 8)
    have hh : 2*N^56 ≤ X := calc
      _ ≤ 2*(2*r)^56 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN' _)
      _ = 2^57*r^56 := by ring
      _ ≤ r^8*r^56 := Nat.mul_le_mul_right _ h8
      _ = r^64 := by ring
      _ ≤ _ := h64
    omega
  · exact (Nat.pow_le_pow_left hN' 64).trans ((Nat.mul_pow ..) ▸ Nat.mul_le_mul_left (2^64) h64)

open ThetaPrimeDensity
private lemma primeSet_entry {P : ℕ → Prop} {X p : ℕ} : p ∈ primeSet P X ↔ p≤X ∧ p.Prime ∧ P p := by
  classical simp only [primeSet,mem_filter,Nat.mem_primesLE,and_assoc]

/-- Absolute constants work at every endpoint and every reduced-modulus cutoff. -/
theorem cutoff_count : ∃ A : ℝ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∀ T : ℕ, 1≤T → ∀ X : ℕ,
    ((primeSet (fun p => A*(1+Real.log T)^2≤err p) X).card:ℝ) ≤ B*X/(T:ℝ)^(1/64:ℝ) := by
  classical
  obtain ⟨a,ha,b,hb,hband⟩ := counting_band
  let Z := (256:ℕ)^64
  let M := ∑ p ∈ range Z, err p
  have hM : 0≤M := sum_nonneg (fun p _ => abs_nonneg _)
  let A := a+M+1
  let B := 2*(b*2^64+1)
  have hA : 0<A := by dsimp [A]; linarith
  have hbc : 0≤b*(2:ℝ)^64 := mul_nonneg hb (by norm_num)
  have hB : 0<B := by dsimp only [B]; linarith only [hbc]
  refine ⟨A,hA,B,hB,?_⟩; intro T hT
  let t := (T:ℝ)^(1/64:ℝ)
  have ht : 0<t := Real.rpow_pos_of_pos (by exact_mod_cast hT) _
  let E (X : ℕ) := primeSet (fun p => A*(1+Real.log T)^2≤err p) X
  have hlog := Real.log_nonneg (show 1≤(T:ℝ) by exact_mod_cast hT)
  have hW : 1≤(1+Real.log T)^2 := one_le_pow₀ (by linarith)
  intro X
  change ((E X).card:ℝ)≤B*X/t
  induction X using Nat.strong_induction_on with
  | h X ih =>
    by_cases hX : Z≤X
    · obtain ⟨N,hN,hlo,hhi,hcomp⟩ := dyadic_cover hX
      let U := (E X).filter (fun p => X/2<p)
      have hdom : E X ⊆ E (X/2) ∪ U := by
        intro p hp
        obtain ⟨hpx,hpr,he⟩ := primeSet_entry.mp hp
        rcases le_or_gt p (X/2) with hl|hl
        · exact mem_union_left _ (primeSet_entry.mpr ⟨hl,hpr,he⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨hp,hl⟩)
      have hcard : ((E X).card:ℝ) ≤ (E (X/2)).card+(U.card:ℝ) := by
        exact_mod_cast (card_le_card hdom).trans (card_union_le ..)
      have hU := hband hN hT U (by
        intro p hp
        obtain ⟨he,hup⟩ := mem_filter.mp hp
        obtain ⟨hpX,hpr,herr⟩ := primeSet_entry.mp he
        refine ⟨hpr,hlo.trans hup.le,hpX.trans hhi,?_⟩
        exact (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith : a≤A) (sq_nonneg _)).trans herr)
      have hpos : 0<X := (show 0<Z by dsimp [Z]; positivity).trans_le hX
      have hi := ih (X/2) (Nat.div_lt_self hpos (by decide))
      have hhalf : 2*((X/2:ℕ):ℝ)≤(X:ℝ) := by exact_mod_cast (show 2*(X/2)≤X by omega)
      have hc : (N:ℝ)^64≤2^64*(X:ℝ) := by exact_mod_cast hcomp
      change (U.card:ℝ)≤b*(N:ℝ)^64/t at hU
      apply hcard.trans ((add_le_add hi hU).trans ?_)
      rw [← add_div,div_le_div_iff_of_pos_right ht]
      have hh := mul_le_mul_of_nonneg_left hhalf hB.le
      have hc' := mul_le_mul_of_nonneg_left hc hb
      dsimp [B] at hh ⊢
      nlinarith only [hh,hc',Nat.cast_nonneg X (α:=ℝ)]
    · have hempty : E X=∅ := by
        apply eq_empty_iff_forall_notMem.mpr; intro p hp
        obtain ⟨hl,_,he⟩ := primeSet_entry.mp hp
        have hs : err p≤M := single_le_sum (fun i _ => abs_nonneg _) (mem_range.mpr (by omega : p<Z))
        have hA' := mul_le_mul_of_nonneg_left hW hA.le
        dsimp [A] at he hA'; linarith
      rw [hempty,card_empty,Nat.cast_zero]; exact div_nonneg (mul_nonneg hB.le (Nat.cast_nonneg X)) ht.le

private lemma exponential_parameter : ∃ A : ℝ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∀ y : ℝ, 0≤y → ∀ X : ℕ,
    ((primeSet (fun p => A*(2+y)^2≤err p) X).card:ℝ) ≤ B*X*Real.exp (-y/64) := by
  classical
  obtain ⟨A,hA,B,hB,H⟩ := cutoff_count
  refine ⟨A,hA,B,hB,?_⟩; intro y hy X
  let T := ⌈Real.exp y⌉₊
  have he := Real.exp_pos y
  have he₁ := Real.one_le_exp hy
  have hceil : Real.exp y≤(T:ℝ) := Nat.le_ceil _
  have hT : 1≤T := by exact_mod_cast he₁.trans hceil
  have ht : (T:ℝ)≤2*Real.exp y := by
    have hh := Nat.ceil_lt_add_one he.le
    change (T:ℝ)<_ at hh
    linarith
  have hl := Real.log_le_log (show 0<(T:ℝ) by exact_mod_cast hT) ht
  rw [Real.log_mul (by norm_num) he.ne', Real.log_exp] at hl
  have hsmall : 1+Real.log T≤2+y := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hp : A*(1+Real.log T)^2≤A*(2+y)^2 := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [Real.log_nonneg (show 1≤(T:ℝ) by exact_mod_cast hT)]) hsmall 2) hA.le
  have hsub : primeSet (fun p => A*(2+y)^2≤err p) X ⊆ primeSet (fun p => A*(1+Real.log T)^2≤err p) X := by
    intro p h; obtain ⟨hX,hpr,he'⟩ := primeSet_entry.mp h; exact primeSet_entry.mpr ⟨hX,hpr,hp.trans he'⟩
  have hw := Real.rpow_le_rpow he.le hceil (show (0:ℝ)≤1/64 by norm_num)
  rw [← Real.exp_mul] at hw
  apply (show ((primeSet (fun p => A*(2+y)^2≤err p) X).card:ℝ) ≤ _ by exact_mod_cast card_le_card hsub).trans ((H T hT X).trans ?_)
  apply (div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hw).trans_eq
  rw [div_eq_mul_inv,← Real.exp_neg]; ring_nf

/-- Uniform upper tail for the absolute error in the original signed sum,
simultaneously in the prime endpoint and the deviation threshold. -/
theorem error_tail : ∃ C a : ℝ, 0<C ∧ 0<a ∧ ∀ X : ℕ, 2≤X → ∀ t : ℝ, 0≤t →
    ((primeSet (fun p => t≤|(S p:ℝ)/p-Real.log p/2|) X).card:ℝ) ≤ C*X*Real.exp (-a*Real.sqrt t) := by
  classical
  obtain ⟨A,hA,B,hB,H⟩ := exponential_parameter
  let c := 1/(64*Real.sqrt A)
  have hc : 0<c := by dsimp [c]; positivity
  let C := (B+2)*Real.exp (2/64)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,c,hC,hc,?_⟩; intro X hX t ht
  let u := Real.sqrt (t/A)
  have hu₀ : 0≤u := Real.sqrt_nonneg _
  have hu : A*u^2=t := by dsimp [u]; rw [Real.sq_sqrt (by positivity)]; field_simp
  have hcu : c*Real.sqrt t = u/64 := by dsimp [c,u]; rw [Real.sqrt_div ht]; ring
  have hf : Real.exp (2/64)*Real.exp (-c*Real.sqrt t)=Real.exp (-(u-2)/64) := by
    rw [← Real.exp_add,neg_mul,hcu]; congr 1; ring
  by_cases htwo : 2≤u
  · have h := H (u-2) (by linarith) X
    rw [show 2+(u-2)=u by ring,hu] at h
    change _ ≤ C*X*_
    apply h.trans
    rw [← hf]
    dsimp [C]; nlinarith only [mul_nonneg (mul_nonneg (Real.exp_pos (2/64)).le (Nat.cast_nonneg X : (0:ℝ)≤X))
      (Real.exp_pos (-c*Real.sqrt t)).le]
  · have h1 : 1≤Real.exp (-(u-2)/64) := Real.one_le_exp (by linarith)
    have hsub : primeSet (fun p => t≤err p) X ⊆ range (X+1) := by
      intro p hp; exact mem_range.mpr (Nat.lt_succ_of_le (primeSet_entry.mp hp).1)
    have hcard := card_le_card hsub; rw [card_range] at hcard
    have hcard' : ((primeSet (fun p => t≤err p) X).card:ℝ)≤X+1 := by exact_mod_cast hcard
    apply hcard'.trans
    have hx : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
    calc
      _ ≤ (B+2)*X := by nlinarith only [hx,mul_nonneg hB.le (Nat.cast_nonneg X)]
      _ ≤ (B+2)*X*Real.exp (-(u-2)/64) := le_mul_of_one_le_right (by positivity) h1
      _ = _ := by rw [← hf]; dsimp [C]; ring

private lemma sqrt_count_absorb {X : ℕ} (hX : 2≤X) (a : ℝ) :
    (X.sqrt:ℝ)+1 ≤ 2*Real.exp (a^2/2)*X*Real.exp (-a*Real.sqrt (Real.log X)) := by
  have hx : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := Real.log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  let z := Real.sqrt (Real.log X)
  have hz : z^2=Real.log X := Real.sq_sqrt hl
  have hpow : (Real.exp (Real.log X/2))^2=X := by
    rw [sq,← Real.exp_add,show Real.log X/2+Real.log X/2=Real.log X by ring,Real.exp_log hx]
  have hs := Nat.sqrt_le' X
  have hs' : (X.sqrt:ℝ)^2≤(X:ℝ) := by exact_mod_cast hs
  have hbound : (X.sqrt:ℝ)≤Real.exp (Real.log X/2) := by nlinarith only [hpow,hs',(Real.exp_pos (Real.log X/2)).le]
  have hone := Real.one_le_exp (show 0≤Real.log X/2 by positivity)
  have hsqrt : Real.log X/2+a*z ≤ a^2/2+Real.log X := by nlinarith only [sq_nonneg (a-z),hz]
  change _ ≤ 2*Real.exp (a^2/2)*X*Real.exp (-a*z)
  calc
    _ ≤ 2*Real.exp (Real.log X/2) := by linarith
    _ = (2*Real.exp (Real.log X/2+a*z))*Real.exp (-a*z) := by
      rw [mul_assoc,← Real.exp_add]; congr 2; ring
    _ ≤ _ := by
      have h := Real.exp_le_exp.mpr hsqrt
      rw [Real.exp_add (a^2/2),Real.exp_log hx] at h
      exact mul_le_mul_of_nonneg_right (by nlinarith only [h] : 2*Real.exp (Real.log X/2+a*z) ≤ 2*Real.exp (a^2/2)*X) (Real.exp_pos _).le

/-- A fixed relative deviation of the canonical signed sum has a
stretched-exponential exceptional count, uniformly over finite endpoints. -/
theorem prime_deviation_tail {ε : ℝ} (hε : 0<ε) : ∃ C a : ℝ, 0<C ∧ 0<a ∧ ∀ X : ℕ, 2≤X →
    ((ThetaPrimeAsymptotic.deviations ε X).card:ℝ) ≤ C*X*Real.exp (-a*Real.sqrt (Real.log X)) := by
  classical
  obtain ⟨B,b,hB,hb,H⟩ := error_tail
  let a := b*Real.sqrt (ε/2)
  have ha : 0<a := by dsimp [a]; positivity
  refine ⟨B+2*Real.exp (a^2/2),a,by positivity,ha,?_⟩
  intro X hX
  let E := ThetaPrimeAsymptotic.deviations ε X
  let t := (ε/2)*Real.log X
  let F := primeSet (fun p => t≤err p) X
  have hxp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := Real.log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  have hsub : E ⊆ range (X.sqrt+1) ∪ F := by
    intro p hp; obtain ⟨hpX,hpr,herr⟩ := ThetaPrimeAsymptotic.deviation_mem.mp hp
    by_cases h : p≤X.sqrt
    · exact mem_union_left _ (mem_range.mpr (by omega))
    apply mem_union_right _; apply primeSet_entry.mpr; refine ⟨hpX,hpr,?_⟩
    have hp₀ : 0<(p:ℝ) := by exact_mod_cast hpr.pos
    have hpℓ := Real.log_pos (show 1<(p:ℝ) by exact_mod_cast hpr.one_lt)
    have hX' : X<p^2 := Nat.sqrt_lt'.mp (lt_of_not_ge h)
    have hlog := Real.log_le_log hxp (show (X:ℝ)≤(p:ℝ)^2 by exact_mod_cast hX'.le)
    rw [Real.log_pow] at hlog; norm_num at hlog
    have he : err p=|(S p:ℝ)/((p:ℝ)*Real.log p)-1/2| * Real.log p := by
      dsimp only [err]
      calc
        _ = |((S p:ℝ)/((p:ℝ)*Real.log p)-1/2)*Real.log p| := by congr 1; field_simp
        _ = _ := by rw [abs_mul,abs_of_pos hpℓ]
    rw [he]
    apply le_trans _ (mul_le_mul_of_nonneg_right herr hpℓ.le)
    dsimp [t]; nlinarith only [mul_le_mul_of_nonneg_left hlog hε.le]
  have hcount := (card_le_card hsub).trans (card_union_le ..); rw [card_range] at hcount
  have hs : (E.card:ℝ) ≤ ((X.sqrt:ℝ)+1)+(F.card:ℝ) := by exact_mod_cast hcount
  have ht : 0≤t := by dsimp [t]; positivity
  have hf := H X hX t ht
  change (F.card:ℝ)≤B*X*Real.exp (-b*Real.sqrt t) at hf
  rw [show -b*Real.sqrt t = -a*Real.sqrt (Real.log X) by dsimp [a,t]; rw [Real.sqrt_mul (by positivity : 0≤ε/2)]; ring] at hf
  exact (hs.trans (add_le_add (sqrt_count_absorb hX a) hf)).trans_eq (by ring)

/-- For every c < 1/2, the primes where the canonical signed sum misses
c p log p obey a stretched-exponential exceptional count. Taking c=0
counts all nonpositive values, including zeros. -/
theorem lower_tail {c : ℝ} (hc : c<1/2) : ∃ C a : ℝ, 0<C ∧ 0<a ∧ ∀ X : ℕ, 2≤X →
    ((primeSet (fun p => (S p:ℝ)≤c*p*Real.log p) X).card:ℝ) ≤ C*X*Real.exp (-a*Real.sqrt (Real.log X)) := by
  obtain ⟨C,a,hC,ha,H⟩ := prime_deviation_tail (show 0<1/2-c by linarith)
  refine ⟨C,a,hC,ha,?_⟩; intro X hX
  apply le_trans _ (H X hX)
  apply Nat.cast_le.mpr; apply card_le_card
  intro p hp
  obtain ⟨hpx,hpr,hbad⟩ := primeSet_entry.mp hp
  have hℓ := Real.log_pos (show (1:ℝ)<p by exact_mod_cast hpr.one_lt)
  have hpos : 0<(p:ℝ) := by exact_mod_cast hpr.pos
  have hv : (S p:ℝ)/((p:ℝ)*Real.log p)≤c := (div_le_iff₀ (mul_pos hpos hℓ)).mpr (by linarith only [show c*(p:ℝ)*Real.log p=c*((p:ℝ)*Real.log p) by ring,hbad])
  apply ThetaPrimeAsymptotic.deviation_mem.mpr; refine ⟨hpx,hpr,?_⟩
  linarith [neg_le_abs ((S p:ℝ)/((p:ℝ)*Real.log p)-1/2)]


/-- At a window of order (log log X)² for S(p)/p − (log p)/2,
the exceptional count saves every fixed power of log X, with
the window constant allowed to depend on that power. -/
theorem loglog_window {D : ℝ} (hD : 0<D) : ∃ K C : ℝ, 0<K ∧ 0<C ∧ ∀ X : ℕ, 4≤X →
    ((primeSet (fun p => K*(1+Real.log (Real.log X))^2≤|(S p:ℝ)/p-Real.log p/2|) X).card:ℝ) ≤
      C*X/(Real.log X)^D := by
  obtain ⟨A,hA,B,hB,H⟩ := exponential_parameter
  refine ⟨A*(2+64*D)^2,B,by positivity,hB,?_⟩
  intro X hX
  have hl₁ : 1≤Real.log X := by
    have he : Real.exp 1≤(X:ℝ) := Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3≤X by omega))
    exact (Real.le_log_iff_exp_le (by exact_mod_cast (show 0<X by omega))).mpr he
  let l := Real.log (Real.log X)
  have hl : 0≤l := Real.log_nonneg hl₁
  let y := 64*D*l
  have hy : 0≤y := by dsimp [y]; positivity
  have hs : 2+y≤(2+64*D)*(1+l) := by dsimp [y]; nlinarith only [hD,hl]
  have harp : A*(2+y)^2≤(A*(2+64*D)^2)*(1+l)^2 := by
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0≤2+y) hs 2) hA.le).trans_eq; ring
  have hd : primeSet (fun p => (A*(2+64*D)^2)*(1+l)^2≤err p) X ⊆ primeSet (fun p => A*(2+y)^2≤err p) X := by
    intro p hp; obtain ⟨hx,hpr,h⟩ := primeSet_entry.mp hp; exact primeSet_entry.mpr ⟨hx,hpr,harp.trans h⟩
  apply (show ((primeSet (fun p => (A*(2+64*D)^2)*(1+l)^2≤err p) X).card:ℝ)≤((primeSet (fun p => A*(2+y)^2≤err p) X).card:ℝ) by exact_mod_cast card_le_card hd).trans
  apply (H y hy X).trans_eq
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hl₁),div_eq_mul_inv (B*(X:ℝ)),← Real.exp_neg]
  congr 2; dsimp [y,l]; ring

end Arxiv.«2501.03234».ThetaPrimeConcentration
#print axioms Arxiv.«2501.03234».ThetaPrimeConcentration.cutoff_count
#print axioms Arxiv.«2501.03234».ThetaPrimeConcentration.error_tail
#print axioms Arxiv.«2501.03234».ThetaPrimeConcentration.prime_deviation_tail
#print axioms Arxiv.«2501.03234».ThetaPrimeConcentration.lower_tail
#print axioms Arxiv.«2501.03234».ThetaPrimeConcentration.loglog_window
