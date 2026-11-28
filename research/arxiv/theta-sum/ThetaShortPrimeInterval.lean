import ThetaShortWindowDeviation
import ThetaStrongOriginalTail

/-! Uniform control of the original theta sum on polynomially short prime intervals. -/
namespace Arxiv.«2501.03234».ThetaShortPrimeInterval
open Finset Real Filter ThetaStrongDeviation ThetaStrongOriginalTail
noncomputable section

/-- Primes in the interval `(X,X+H]` satisfying `P`. -/
def primes (X H : ℕ) (P : ℕ → Prop) : Finset ℕ := by
  classical exact (Ioc X (X+H)).filter (fun p => p.Prime ∧ P p)

theorem mem_primes {X H p : ℕ} {P : ℕ → Prop} :
    p∈primes X H P ↔ p∈Ioc X (X+H) ∧ p.Prime ∧ P p := by
  classical simp only [primes,mem_filter]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

private theorem card_offset (X H : ℕ) (P : ℕ → Prop) :
    (primes X H P).card = ((range H).filter (fun i => (X+1+i).Prime ∧ P (X+1+i))).card := by
  classical
  apply card_bij (fun p _ => p-(X+1))
  · intro p hp
    obtain ⟨hxp,hhi,hpr,hP⟩ : X<p ∧ p≤X+H ∧ p.Prime ∧ P p := by simpa [primes,and_assoc] using hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [show X+1+(p-(X+1))=p by omega, and_iff_right hpr]⟩
  · intro p hp q hq hh
    have h1 := (mem_Ioc.mp (mem_filter.mp hp).1).1
    have h2 := (mem_Ioc.mp (mem_filter.mp hq).1).1
    omega
  · intro i hi
    obtain ⟨hi,hpr,hP⟩ := mem_filter.mp hi
    have hi' := mem_range.mp hi
    refine ⟨X+1+i,mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,hpr,hP⟩,by omega⟩

/-- A finite two-term estimate valid in every translated interval of length at
most X. The second term is independent of that length. -/
def ExceptionalPower (θ : ℝ) : Prop := ∀ {ε : ℝ}, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X →
    ((primes X H (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card:ℝ) ≤
      (H:ℝ)/log X*exp (-rate X/1536)+C*(X:ℝ)^(θ)*(1+log X)^8

/-- Transfer any relative error profile on a power band to translated prime
intervals. The term independent of the interval length comes from the band energy. -/
theorem from_band {e : ℕ} {ε D : ℝ} (hD : 0<D) (v w : ℕ → ℝ) (hv : ∀ N, 0≤v N)
    (hb : ∀ᶠ N : ℕ in atTop, ∀ M H : ℕ, ∀ s : Finset ℕ,
      (∀ i∈s,i<H ∧ (M+i).Prime ∧ N^56≤M+i ∧ M+i≤N^64 ∧
        ε*log (M+i:ℕ)≤|(S (M+i):ℝ)/(M+i:ℕ)-log (M+i:ℕ)/2|) →
      (s.card:ℝ) ≤ D*(1+log N)^8*((H:ℝ)*v N+(N:ℝ)^e))
    (cost : ∀ᶠ X : ℕ in atTop, ∀ N : ℕ, 0<N → 0<X → X≤N^64 → 1≤log N →
      1≤log X → log 64≤log (log N) → D*(1+log X)^9*v N≤w X) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X →
      ((primes X H (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card:ℝ) ≤
        (H:ℝ)/log X*w X+C*(X:ℝ)^((e:ℝ)/64)*(1+log X)^8 := by
  classical
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨N₀,h₀⟩ := eventually_atTop.mp
    (hb.and ((hlog.eventually_ge_atTop 1).and ((tendsto_log_atTop.comp hlog).eventually_ge_atTop (log 64))))
  let K := ((2:ℝ)^65)^((e:ℝ)/64)
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨D*K,mul_pos hD hK,?_⟩
  filter_upwards [eventually_ge_atTop ((256:ℕ)^64),eventually_ge_atTop (N₀^64),hlog.eventually_ge_atTop 1, cost] with X hbig hsize hlogX hcost
  intro H hHX
  have hX : 0<X := (show 0<(256:ℕ)^64 by positivity).trans_le hbig
  have hXp : 0<(X:ℝ) := by exact_mod_cast hX
  obtain ⟨N,hN,hlo,hhi,hcap⟩ := ThetaPrimeConcentration.dyadic_cover (X:=2*X) (by omega)
  have hN₀ : N₀≤N := by
    by_contra! lt
    exact (Nat.pow_lt_pow_left lt (by norm_num : 64≠0)).not_ge (hsize.trans (by omega))
  obtain ⟨band,hlogN,hloglog⟩ := h₀ N hN₀
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hNX : N^56≤X := by omega
  have hNX' : N≤X := (Nat.le_self_pow (by norm_num : 56≠0) N).trans hNX
  have hlogNX := log_le_log hNp (show (N:ℝ)≤(X:ℝ) by exact_mod_cast hNX')
  have hscale : (N:ℝ)^64≤2^65*(X:ℝ) := by
    have hh : 2^64*(2*X)=2^65*X := by ring
    exact_mod_cast hcap.trans_eq hh
  have hW : (N:ℝ)^e≤K*(X:ℝ)^((e:ℝ)/64) := calc
    _ = ((N:ℝ)^64)^((e:ℝ)/64) := by rw [←rpow_natCast_mul hNp.le,show ((64:ℕ):ℝ)*((e:ℝ)/64)=e by norm_num;ring,rpow_natCast]
    _ ≤ ((2:ℝ)^65*(X:ℝ))^((e:ℝ)/64) := rpow_le_rpow (by positivity) hscale (by positivity)
    _ = _ := mul_rpow (by positivity) hXp.le
  let P (p : ℕ) := ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|
  let U := (range H).filter (fun i => (X+1+i).Prime ∧ P (X+1+i))
  have he := band (X+1) H U (by
    intro i hi
    obtain ⟨hi,hp,hdev⟩ := mem_filter.mp hi
    have hil := mem_range.mp hi
    refine ⟨hil,hp,by omega,by omega,?_⟩
    let p := X+1+i
    have hrp : 0<(p:ℝ) := by exact_mod_cast hp.pos
    have id : ((S p:ℝ)/p-log p/2)*p=(S p:ℝ)-p*log p/2 := by field_simp
    apply (mul_le_mul_iff_left₀ hrp).mp
    calc ε*log p*(p:ℝ) = ε*(p:ℝ)*log p := by ring
         _ ≤ _ := hdev
         _ = _ := by rw [← id,abs_mul,abs_of_pos hrp])
  change 1≤log (X:ℝ) at hlogX
  have hxl : 0<log (X:ℝ) := by linarith
  have hv' : (1+log (N:ℝ))^8≤(1+log (X:ℝ))^8 :=
    pow_le_pow_left₀ (by change 1≤log (N:ℝ) at hlogN;linarith) (by linarith only [hlogNX]) _
  have hpoly : D*(1+log (X:ℝ))^8*log X≤D*(1+log X)^9 := by
    rw [pow_succ _ 8,←mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpo := (mul_le_mul_of_nonneg_right hpoly (hv N)).trans
    (hcost N (by omega) hX (by omega) hlogN hlogX hloglog)
  rw [card_offset]
  change (U.card:ℝ)≤_
  apply he.trans
  have hsum := add_le_add_right hW ((H:ℝ)*v N)
  calc
    _ ≤ D*(1+log (X:ℝ))^8*((H:ℝ)*v N+K*(X:ℝ)^((e:ℝ)/64)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hv' hD.le) hsum (by positivity [hv N]) (by positivity)
    _ = ((H:ℝ)/log X)*(D*(1+log (X:ℝ))^8*log X*v N)+D*K*(X:ℝ)^((e:ℝ)/64)*(1+log X)^8 := by field_simp
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hpo (by positivity)) _

theorem exceptional_for {e : ℕ} (h32 : 32≤e) (h48 : e≤48) (kernel : ThetaCalibratedCone.Kernel e) : ExceptionalPower ((e:ℝ)/64) := by
  intro ε hε
  classical
  obtain ⟨D,hD,hb⟩ := ThetaShortWindowDeviation.band h32 h48 kernel hε
  apply from_band hD (fun N => exp (-rate N/64)) _ (fun _ => (exp_pos _).le) hb
  filter_upwards [absorb_log_power hD (by norm_num : (0:ℝ)<3072) 9] with X h
  intro N hN hX hx hLn hLx h64
  have hr := ThetaStrongPrimeTail.compare_rate hN hX hx hLn hLx h64
  have hn : exp (-rate N/64)≤exp (-rate X/1024) := exp_le_exp.mpr (by linarith)
  apply (mul_le_mul h hn (exp_pos _).le (exp_pos _).le).trans_eq
  rw [←exp_add]
  congr 1
  ring

theorem elementary : ExceptionalPower (3/4:ℝ) := by
  rw [show (3/4:ℝ)=((48:ℕ):ℝ)/64 by norm_num]
  exact @exceptional_for 48 (by decide) (by decide) ThetaCalibratedCone.elementary_kernel

theorem exceptional {ε : ℝ} (hε : 0<ε) : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X →
    ((primes X H (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card:ℝ) ≤
      (H:ℝ)/log X*exp (-rate X/1536)+C*(X:ℝ)^(3/4:ℝ)*(1+log X)^8 := elementary hε

private theorem lower_subset {c : ℝ} (X H : ℕ) : primes X H (fun p => (S p:ℝ)≤c*p*log p) ⊆
    primes X H (fun p => (1/2-c)*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|) := by
  intro p hp
  obtain ⟨hm,hpr,hp⟩ := mem_primes.mp hp
  refine mem_primes.mpr ⟨hm,hpr,?_⟩
  exact (show (1/2-c)*(p:ℝ)*log p≤-((S p:ℝ)-p*log p/2) by linarith only [hp]).trans (neg_le_abs _)

/-- Beyond the spacing threshold by a subpower factor, the short intervals
satisfy the stretched-exponential exceptional bound. -/
theorem original_of_bound {θ : ℝ} (hex : ExceptionalPower θ) {ε : ℝ} (hε : 0<ε) : ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
    (X:ℝ)^(θ)*exp (rate X/512)≤H → H≤X →
    ((primes X H (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card:ℝ) ≤
      (H:ℝ)/log X*exp (-rate X/2048) := by
  obtain ⟨C,hC,bound⟩ := hex hε
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [bound,hlog.eventually_ge_atTop 1,absorb_log_power hC (by norm_num : (0:ℝ)<768) 9,
    absorb_log_power (by norm_num : (0:ℝ)<2) (by norm_num : (0:ℝ)<6144) 0] with X hb hl hpoly htwo
  intro H hsize hH
  change 1≤log (X:ℝ) at hl
  have hxl : 0<log (X:ℝ) := by linarith
  let V := 1+log (X:ℝ)
  let W := (X:ℝ)^(θ)
  have hW : 0≤W := by dsimp [W];positivity
  have hV : 0≤V := by dsimp [V];linarith
  have hp : C*V^8*log X≤exp (rate X/768) := calc
    _ ≤ C*V^8*V := mul_le_mul_of_nonneg_left (by dsimp [V];linarith) (by positivity)
    _ = C*V^9 := by ring
    _ ≤ _ := hpoly
  have hoff : C*W*V^8 ≤ (H:ℝ)/log X*exp (-rate X/1536) := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hxl]
    have h := mul_le_mul_of_nonneg_right hsize (exp_pos (-rate X/1536)).le
    rw [mul_assoc,←exp_add,show rate X/512+ -(rate X)/1536=rate X/768 by ring] at h
    linarith only [h,mul_le_mul_of_nonneg_left hp hW]
  simp only [pow_zero,mul_one] at htwo
  have ht := mul_le_mul_of_nonneg_right htwo (exp_pos (-rate X/1536)).le
  rw [← exp_add,show rate X/6144 + -(rate X)/1536= -(rate X)/2048 by ring] at ht
  have hscale := mul_le_mul_of_nonneg_left ht (div_nonneg (Nat.cast_nonneg H (α:=ℝ)) hxl.le)
  apply (hb H hH).trans
  change _+C*W*V^8≤_
  linarith only [hoff,hscale]

theorem lower_of_bound {θ : ℝ} (hex : ExceptionalPower θ) {c : ℝ} (hc : c<1/2) : ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
    (X:ℝ)^(θ)*exp (rate X/512)≤H → H≤X →
    ((primes X H (fun p => (S p:ℝ)≤c*p*log p)).card:ℝ) ≤ (H:ℝ)/log X*exp (-rate X/2048) := by
  filter_upwards [original_of_bound hex (sub_pos.mpr hc)] with X hx
  intro H hh hH
  exact (Nat.cast_le.mpr (card_le_card (lower_subset X H))).trans (hx H hh hH)

theorem total_count (X H : ℕ) :
    (primes X H (fun _ => True)).card=Nat.primeCounting (X+H)-Nat.primeCounting X := by
  classical
  have h : primes X H (fun _ => True)=Nat.primesLE (X+H) \ Nat.primesLE X := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      obtain ⟨hm,hpr,_⟩ := mem_primes.mp hp
      obtain ⟨hl,hr⟩ := mem_Ioc.mp hm
      exact mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hr,hpr⟩,fun hx => hl.not_ge (Nat.mem_primesLE.mp hx).1⟩
    · intro hp
      obtain ⟨h1,h2⟩ := mem_sdiff.mp hp
      obtain ⟨hr,hpr⟩ := Nat.mem_primesLE.mp h1
      exact mem_primes.mpr ⟨mem_Ioc.mpr ⟨lt_of_not_ge (fun hx => h2 (Nat.mem_primesLE.mpr ⟨hx,hpr⟩)),hr⟩,hpr,trivial⟩
  have sub : Nat.primesLE X⊆Nat.primesLE (X+H) := by
    intro p hp
    obtain ⟨hx,hpr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨by omega,hpr⟩
  rw [h,card_sdiff_of_subset sub,
    Nat.primesLE_card_eq_primeCounting,Nat.primesLE_card_eq_primeCounting]

/-- A polylogarithmic factor above the spacing threshold suffices for at least
H/(4 log X) large positive values, given the stated local count of ordinary primes. -/
theorem good_count_of_bound {θ : ℝ} (hex : ExceptionalPower θ) {c : ℝ} (hc : c<1/2) : ∃ K : ℝ, 0<K ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
    K*(X:ℝ)^(θ)*(1+log X)^9≤H → H≤X →
    (H:ℝ)/log X/2≤(Nat.primeCounting (X+H)-Nat.primeCounting X:ℕ) →
    (H:ℝ)/log X/4≤((primes X H (fun p => c*p*log p<(S p:ℝ))).card:ℝ) := by
  classical
  obtain ⟨C,hC,hdev⟩ := hex (sub_pos.mpr hc)
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  refine ⟨8*C,by positivity,?_⟩
  filter_upwards [hdev,absorb_log_power (by norm_num : (0:ℝ)<8) (by norm_num : (0:ℝ)<1536) 0,
    hlog.eventually_ge_atTop 1] with X hX he hxl
  simp only [pow_zero,mul_one] at he
  have hsmall : exp (-rate X/1536)≤1/8 := by
    rw [show -rate X/1536= -(rate X/1536) by ring,exp_neg,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) he
  intro H hlo hhi hcount
  change 1≤log (X:ℝ) at hxl
  have hlogp : 0<log (X:ℝ) := by linarith
  have hbad := (Nat.cast_le.mpr (card_le_card (lower_subset (c:=c) X H))).trans (hX H hhi)
  let V := 1+log (X:ℝ)
  let W := (X:ℝ)^(θ)
  have hV : 0≤V := by dsimp [V];linarith
  have hW : 0≤W := by dsimp [W];positivity
  have hcost : C*W*V^8 ≤ (H:ℝ)/log X/8 := by
    rw [le_div_iff₀ (by norm_num),le_div_iff₀ hlogp]
    change 8*C*W*V^9≤(H:ℝ) at hlo
    rw [show V^9=V^8*V from pow_succ _ 8] at hlo
    linarith only [hlo,mul_le_mul_of_nonneg_left (show log (X:ℝ)≤V by dsimp [V];linarith) (show 0≤8*C*W*V^8 by positivity)]
  change _≤_+C*W*V^8 at hbad
  have cover : primes X H (fun _ => True)⊆primes X H (fun p => (S p:ℝ)≤c*p*log p) ∪
      primes X H (fun p => c*p*log p<(S p:ℝ)) := by
    intro p hp
    obtain ⟨hm,hp,_⟩ := mem_primes.mp hp
    rcases le_or_gt (S p:ℝ) (c*p*log p) with hb|hg
    · exact mem_union_left _ (mem_primes.mpr ⟨hm,hp,hb⟩)
    · exact mem_union_right _ (mem_primes.mpr ⟨hm,hp,hg⟩)
  have hh := (card_le_card cover).trans (card_union_le ..)
  rw [total_count] at hh
  have hh' := (Nat.cast_le (α:=ℝ)).mpr hh
  rw [Nat.cast_add] at hh'
  have hfrac := mul_le_mul_of_nonneg_left hsmall (div_nonneg (Nat.cast_nonneg H (α:=ℝ)) hlogp.le)
  linarith only [hcount,hh',hbad,hfrac,hcost]

theorem original {ε : ℝ} (hε : 0<ε) : ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
    (X:ℝ)^(3/4:ℝ)*exp (rate X/512)≤H → H≤X →
    ((primes X H (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card:ℝ) ≤
      (H:ℝ)/log X*exp (-rate X/2048) :=
  original_of_bound elementary hε

theorem lower {c : ℝ} (hc : c<1/2) : ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
    (X:ℝ)^(3/4:ℝ)*exp (rate X/512)≤H → H≤X →
    ((primes X H (fun p => (S p:ℝ)≤c*p*log p)).card:ℝ) ≤ (H:ℝ)/log X*exp (-rate X/2048) :=
  lower_of_bound elementary hc

theorem good_count {c : ℝ} (hc : c<1/2) : ∃ K : ℝ, 0<K ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
    K*(X:ℝ)^(3/4:ℝ)*(1+log X)^9≤H → H≤X →
    (H:ℝ)/log X/2≤(Nat.primeCounting (X+H)-Nat.primeCounting X:ℕ) →
    (H:ℝ)/log X/4≤((primes X H (fun p => c*p*log p<(S p:ℝ))).card:ℝ) :=
  good_count_of_bound elementary hc

#print axioms exceptional_for
#print axioms good_count
#print axioms lower
#print axioms original
#print axioms exceptional
end
end Arxiv.«2501.03234».ThetaShortPrimeInterval
