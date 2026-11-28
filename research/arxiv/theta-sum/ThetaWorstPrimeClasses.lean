import ThetaProgressionOccupancy
import ThetaOccupancyScales

/-! The total worst-class contribution of exceptional primes past the square-root modulus range. -/
namespace Arxiv.«2501.03234».ThetaWorstPrimeClasses
open Filter Finset Real ThetaPrimeDensity ThetaOccupancyScales ThetaProgressionOccupancy
noncomputable section

def count (E : Finset ℕ) (q b : ℕ) := (E.filter (fun p => p%q=b)).card
def worst (E : Finset ℕ) (q : ℕ) := (range q).sup (count E q)
def total (E : Finset ℕ) (Q : ℕ) : ℝ := ∑ q∈Icc 1 Q,(worst E q:ℝ)

private theorem selected (E : Finset ℕ) (Q : ℕ) : ∃ a : ℕ → ℕ,total E Q = occupancy E 0 Q a := by
  classical
  have H (q : ℕ) (hq : 0<q) : ∃ b,b<q ∧ worst E q=count E q b := by
    simpa only [worst,mem_range] using exists_mem_eq_sup (range q) (nonempty_range_iff.mpr hq.ne') (count E q)
  let a (q : ℕ) := if hq : 0<q then (H q hq).choose else 0
  refine ⟨a,sum_congr rfl ?_⟩
  intro q hq
  have hp : 0<q := (mem_Icc.mp hq).1
  have h := (H q hp).choose_spec.2
  simp only [zero_add]
  exact_mod_cast (show worst E q=count E q (a q) by simpa [a,hp] using h)

private theorem translated {E : Finset ℕ} {u H Q : ℕ} (hE : ∀ p∈E,u≤ p ∧ p≤ u+H) :
    (total E Q)^2 ≤ E.card*(H*(ThetaProgressionIncidence.harmonicSum Q)^3+(Q:ℝ)^2) := by
  classical
  let F := E.image (fun p => p-u)
  have hinj : Set.InjOn (fun p : ℕ => p-u) E := by
    intro p hp r hr hh
    have hp' := (hE p hp).1
    have hr' := (hE r hr).1
    change p-u=r-u at hh;omega
  have hcard : F.card=E.card := card_image_of_injOn hinj
  have hF : F⊆range (H+1) := by
    intro j hj;obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
    have hl := (hE p hp).2;exact mem_range.mpr (by omega)
  obtain ⟨a,ha⟩ := selected E Q
  have he : occupancy E 0 Q a=occupancy F u Q a := by
    apply sum_congr rfl;intro q _
    have hset : F.filter (fun j => (u+j)%q=a q) =
        (E.filter (fun p => (0+p)%q=a q)).image (fun p => p-u) := by
      ext j
      constructor
      · intro h;obtain ⟨hh,he⟩ := mem_filter.mp h;obtain ⟨p,hp,rfl⟩ := mem_image.mp hh
        have hsum : u+(p-u)=p := by have h := (hE p hp).1;omega
        exact mem_image.mpr ⟨p,mem_filter.mpr ⟨hp,by simpa only [zero_add,hsum] using he⟩,rfl⟩
      · intro h;obtain ⟨p,hp,rfl⟩ := mem_image.mp h;obtain ⟨hh,he⟩ := mem_filter.mp hp
        have hsum : u+(p-u)=p := by have h := (hE p hh).1;omega
        exact mem_filter.mpr ⟨mem_image.mpr ⟨p,hh,rfl⟩,by simpa only [zero_add,hsum] using he⟩
    rw [hset,card_image_of_injOn (hinj.mono (by intro p h;exact (mem_filter.mp h).1))]
  rw [ha,he,←hcard]
  exact bound hF a

theorem sparse {E : Finset ℕ} {u H Q : ℕ} {M s : ℝ} (hM : 0≤M) (hs : 1≤ s)
    (hset : ∀ p∈E,u≤ p ∧ p≤ u+H) (he : (E.card:ℝ) ≤ M*exp (-(8*s)))
    (hQ : (Q:ℝ)^2≤H*exp s) (hsum : (ThetaProgressionIncidence.harmonicSum Q)^3 ≤ exp s)
    (hπ : (H:ℝ)≤M*exp s) : total E Q ≤ M*exp (-(2*s)) := by
  have hx : 0≤(H:ℝ) := Nat.cast_nonneg H
  have hxE : (H:ℝ)*(ThetaProgressionIncidence.harmonicSum Q)^3+(Q:ℝ)^2 ≤ M*exp (3*s) := by
    have h := mul_le_mul_of_nonneg_left hsum hx
    have he : (2:ℝ) ≤ exp s := by linarith only [add_one_le_exp s,hs]
    calc _ ≤ 2*((H:ℝ)*exp s) := by linarith only [h,hQ]
         _ ≤ (M*exp s)*exp s*exp s := by
           calc _ ≤ exp s*((M*exp s)*exp s) := mul_le_mul he (mul_le_mul_of_nonneg_right hπ (exp_pos _).le) (by positivity) (exp_pos _).le
                _ = _ := by ring
         _ = _ := by rw [mul_assoc,mul_assoc,←exp_add,←exp_add];congr 2;ring
  have h₁ := translated (Q:=Q) hset
  have hsq : (total E Q)^2 ≤ (M*exp (-(2*s)))^2 := by
    apply h₁.trans
    apply (mul_le_mul he hxE (by positivity [show 0≤ThetaProgressionIncidence.harmonicSum Q from sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i))]) (by positivity)).trans
    rw [mul_pow,mul_mul_mul_comm,←exp_add,←exp_nat_mul]
    norm_num only [Nat.cast_ofNat];rw [←sq M];apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
    apply exp_le_exp.mpr;linarith only [hs]
  exact le_of_pow_le_pow_left₀ (by decide : (2:ℕ)≠0) (by positivity) hsq

theorem transfer {P : ℕ → Prop} (hP : ∀ᶠ X : ℕ in atTop,((primeSet P X).card:ℝ) ≤
    X.primeCounting*exp (-(log X/(1+log (log X))/33554432))) :
    ∀ᶠ X : ℕ in atTop,∀ Q : ℕ,(Q:ℝ)^2 ≤ X*exp (saving X) →
      total (primeSet P X) Q ≤ X.primeCounting*exp (-(2*saving X)) := by
  classical
  filter_upwards [hP,bounds] with X hE hX Q hQ
  obtain ⟨hx,hL,hs,hsL,hcube,hπ⟩ := hX
  let E := primeSet P X
  let s := saving X
  let M := (X.primeCounting:ℝ)
  have hM : 0≤M := Nat.cast_nonneg _
  have hQX : (Q:ℝ)≤X := by
    have he := exp_le_exp.mpr hsL;rw [exp_log hx] at he
    have hsq := hQ.trans (mul_le_mul_of_nonneg_left he hx.le)
    exact le_of_pow_le_pow_left₀ (by decide : (2:ℕ)≠0) hx.le (by simpa only [sq] using hsq)
  have hsum : (ThetaProgressionIncidence.harmonicSum Q)^3 ≤ exp s := by
    have hlog : log (Q:ℝ) ≤ log X := by
      by_cases h : Q=0
      · simp [h];linarith only [hL]
      · exact log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)) hQX
    have h := (ThetaProgressionIncidence.harmonic_bound Q).trans (add_le_add le_rfl hlog)
    have hn : 0≤ThetaProgressionIncidence.harmonicSum Q := sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i))
    exact (pow_le_pow_left₀ hn h _).trans hcube
  have he : (E.card:ℝ) ≤ M*exp (-(8*s)) := by
    have hrate : log (X:ℝ)/(1+log (log X))/33554432 = 8*s := by dsimp [s,saving];ring
    rw [←hrate];exact hE
  exact sparse (u:=0) hM hs (fun p hp => ⟨Nat.zero_le _,by simpa only [Nat.zero_add] using (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1⟩) he hQ hsum hπ

theorem centered : ∃ A : ℝ,0<A ∧ ∀ᶠ X : ℕ in atTop,∀ Q : ℕ,(Q:ℝ)^2 ≤ X*exp (saving X) →
    total (primeSet (fun p => A*(1+log (log p))^2≤|(S p:ℝ)/p-log p/2|) X) Q ≤
      X.primeCounting*exp (-(2*saving X)) := by
  obtain ⟨A,hA,h⟩ := ThetaMultiscaleExceptions.original_centered
  exact ⟨A,hA,transfer h⟩

theorem slope (k : ℕ) : ∀ᶠ X : ℕ in atTop,∀ Q : ℕ,(Q:ℝ)^2 ≤ X*exp (saving X) →
    total (primeSet (fun p => S p≤(k:ℤ)*p) X) Q ≤ X.primeCounting*exp (-(2*saving X)) :=
  transfer (ThetaMultiscaleExceptions.original_slope k)

#print axioms sparse
#print axioms transfer
#print axioms centered
#print axioms slope
end
end Arxiv.«2501.03234».ThetaWorstPrimeClasses
