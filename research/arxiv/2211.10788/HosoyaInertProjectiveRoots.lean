import research.arxiv.«2211.10788».LucasFibonacciFixedDivisors
import HosoyaProjectiveRoots
import HosoyaProjectivePowerFibers

/-! Nonzero elements of the inert quadratic algebra and projective representatives. -/

namespace Arxiv.«2211.10788»

private abbrev QP (R : Type*) [CommRing R] := QuadraticAlgebra R 1 1

private def point {R : Type*} [Field R] : Option R → QP R
  | none => 1
  | some x => ⟨x,1⟩

private lemma point_ne_zero {R : Type*} [Field R] (z : Option R) : point z ≠ 0 := by
  cases z with
  | none => exact one_ne_zero
  | some x =>
    intro he
    exact one_ne_zero (congrArg QuadraticAlgebra.im he : (1:R)=0)

private lemma scaled_ne_zero {R : Type*} [Field R] (z : Option R) (t : Rˣ) :
    (t:R) • point z ≠ 0 := smul_ne_zero t.ne_zero (point_ne_zero z)

private noncomputable def projectiveScaleEquiv {R : Type*} [Field R] :
    Option R × Rˣ ≃ {q : QP R // q≠0} := by
  classical
  let f (v : Option R × Rˣ) : {q : QP R // q≠0} :=
    ⟨(v.2:R) • point v.1,scaled_ne_zero v.1 v.2⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨x,s⟩ ⟨y,t⟩ he
    have h := congrArg Subtype.val he
    change (s:R) • point x=(t:R) • point y at h
    have hr := congrArg QuadraticAlgebra.re h
    have hi := congrArg QuadraticAlgebra.im h
    cases x <;> cases y <;> simp [point,QuadraticAlgebra.re_smul,QuadraticAlgebra.im_smul,
      QuadraticAlgebra.re_one,QuadraticAlgebra.im_one] at hr hi ⊢
    all_goals first | exact Units.ext hr | exact (t.ne_zero hi.symm).elim | exact (s.ne_zero hi).elim |
      exact ⟨mul_left_cancel₀ s.ne_zero (by simpa [←hi] using hr),Units.ext hi⟩
  · rintro ⟨q,hq⟩
    by_cases hi : q.im=0
    · have hr : q.re≠0 := fun h => hq (QuadraticAlgebra.ext h hi)
      refine ⟨⟨none,Units.mk0 q.re hr⟩,Subtype.ext ?_⟩
      apply QuadraticAlgebra.ext <;> simp [f,point,QuadraticAlgebra.re_smul,QuadraticAlgebra.im_smul,
        QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,hi]
    · refine ⟨⟨some (q.re/q.im),Units.mk0 q.im hi⟩,Subtype.ext ?_⟩
      apply QuadraticAlgebra.ext <;> simp [f,point]
      field_simp

/-- The quadratic coefficient of the upper index form at offset r. -/
def upperIndexStart (R : Type*) [CommRing R] (r : ℕ) : QuadraticAlgebra R 1 1 :=
  ⟨(lucasFibonacciSum (r+1):R)-lucasFibonacciSum r,lucasFibonacciSum r⟩

private theorem upper_start_ne_zero {p : ℕ} [Fact p.Prime] (r : ℕ) :
    upperIndexStart (ZMod p) r ≠ 0 := by
  have nonzero (r : ℕ) : ¬((lucasFibonacciSum r : ZMod p)=0 ∧ (lucasFibonacciSum (r+1):ZMod p)=0) := by
    induction r with
    | zero => simp [lucas_fibonacci_sum_zero]
    | succ r ih =>
      rintro ⟨h₁,h₂⟩
      rw [show r+1+1=r+2 by omega,lucas_fibonacci_sum_recurrence,Nat.cast_add,h₁,zero_add] at h₂
      exact ih ⟨h₂,h₁⟩
  intro h
  have h₁ := congrArg QuadraticAlgebra.im h
  have h₂ := congrArg QuadraticAlgebra.re h
  change (lucasFibonacciSum r : ZMod p)=0 at h₁
  change (lucasFibonacciSum (r+1):ZMod p)-lucasFibonacciSum r=0 at h₂
  exact nonzero r ⟨h₁,(sub_eq_zero.mp h₂).trans h₁⟩

private theorem form_at_point {p : ℕ} [Fact p.Prime] (z : Option (ZMod p)) (r d : ℕ) :
    upperIndexForm (upperIndexChart z).1 (upperIndexChart z).2 d r =
      (upperIndexStart (ZMod p) r * (point z)^d).im := by
  rw [upperIndexForm_power]
  have he : (⟨(upperIndexChart z).1,(upperIndexChart z).2⟩ : QP (ZMod p))=point z := by
    cases z <;> rfl
  rw [he,QuadraticAlgebra.im_mul]
  simp only [upperIndexStart]
  ring

/-- Inert-prime root count from one power in the quadratic algebra over the residue field. -/
theorem upperProjectiveRootCount_inert {p : ℕ} [Fact p.Prime]
    (hi : ∀ x : ZMod p, x^2≠1+1*x) (r d : ℕ) :
    let g := (p+1).gcd d
    let e := (p+1)/g
    upperProjectiveRootCount p r d =
      if ((upperIndexStart (ZMod p) r)^e).im=0 then g else 0 := by
  classical
  let : Fact (∀ x : ZMod p, x^2≠1+1*x) := ⟨hi⟩
  let K := QP (ZMod p)
  let : Finite K := Finite.of_equiv _ (QuadraticAlgebra.equivProd (1:ZMod p) 1).symm
  let : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  let T : Kˣ := Units.mk0 _ (upper_start_ne_zero r)
  let n := p-1
  let g := (p+1).gcd d
  let e := (p+1)/g
  have hn : 0<n := by have := (Fact.out : p.Prime).two_le; dsimp [n]; omega
  have cardK : Nat.card Kˣ=(p+1)*n := by
    rw [Nat.card_units,Nat.card_congr (QuadraticAlgebra.equivProd (1:ZMod p) 1),Nat.card_prod,Nat.card_zmod]
    dsimp [n]
    have hp := (Fact.out : p.Prime).ne_zero
    obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    simp
    rw [show (q+1)*(q+1)=(q+1+1)*q+1 by ring]
    omega
  have scalar (z : Kˣ) : (z:K).im=0 ↔ z^n=1 := by
    have hfix : (z:K).im=0 ↔ (z:K)^p=(z:K) := by
      rw [←Subfield.mem_bot_iff_pow_eq_self K p,mem_bot_iff_intCast p K]
      constructor
      · intro h
        obtain ⟨m,hm⟩ := ZMod.intCast_surjective (z:K).re
        exact ⟨m,QuadraticAlgebra.ext hm h.symm⟩
      · rintro ⟨m,he⟩
        rw [←he]
        rfl
    have he : p=n+1 := by dsimp [n]; omega
    rw [hfix,show (z:K)^p=(z:K)^n*(z:K) from (congrArg (fun i : ℕ => (z:K)^i) he).trans (pow_succ ..),
      mul_eq_right₀ z.ne_zero,←Units.val_inj]
    simp
  let f : Option (ZMod p) × (ZMod p)ˣ ≃ Kˣ := projectiveScaleEquiv.trans unitsEquivNeZero.symm
  let good (z : Option (ZMod p)) := upperIndexForm (upperIndexChart z).1 (upperIndexChart z).2 d r=0
  let target := (T^n)⁻¹
  have hit (v : Option (ZMod p) × (ZMod p)ˣ) : good v.1 ↔ f v ^ (d*n)=target := by
    have scale : ((f v):K)=(v.2:ZMod p) • point v.1 := rfl
    have h₁ : good v.1 ↔ ((T * f v ^ d : Kˣ):K).im=0 := by
      change upperIndexForm _ _ _ _=0 ↔ (((T:K)*((f v):K)^d):K).im=0
      rw [form_at_point,scale,smul_pow,mul_smul_comm,QuadraticAlgebra.im_smul]
      simp only [smul_eq_mul,mul_eq_zero,pow_ne_zero _ v.2.ne_zero,false_or]
      rfl
    rw [h₁,scalar,mul_pow,←pow_mul,eq_inv_iff_mul_eq_one,mul_comm]
  have prodEquiv : {z : Option (ZMod p) // good z} × (ZMod p)ˣ ≃
      {u : Kˣ // u^(d*n)=target} := by
    let S : {z : Option (ZMod p) // good z} × (ZMod p)ˣ ≃
        {v : Option (ZMod p) × (ZMod p)ˣ // good v.1} :=
      { toFun := fun v => ⟨(v.1.val,v.2),v.1.property⟩
        invFun := fun v => (⟨v.val.1,v.property⟩,v.val.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact S.trans (f.subtypeEquiv hit)
  have count := Nat.card_congr prodEquiv
  rw [Nat.card_prod,cyclic_power_fiber_card,cardK,Nat.gcd_mul_right,Nat.mul_div_mul_right _ _ hn] at count
  have ht : target^e=1 ↔ ((upperIndexStart (ZMod p) r)^e).im=0 := by
    rw [show ((upperIndexStart (ZMod p) r)^e).im=((T^e : Kˣ):K).im from rfl,scalar]
    simp only [target,inv_pow,inv_eq_one,←pow_mul,Nat.mul_comm n e]
  have cr : Nat.card {z // good z}=upperProjectiveRootCount p r d := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  rw [cr,Nat.card_units,Nat.card_zmod] at count
  dsimp only
  by_cases hh : target^((p+1)/(p+1).gcd d)=1
  · simp only [if_pos hh] at count
    rw [if_pos (ht.mp hh)]
    exact Nat.mul_right_cancel hn count
  · simp only [if_neg hh] at count
    rw [if_neg (ht.not.mp hh)]
    exact (Nat.mul_eq_zero.mp count).resolve_right hn.ne'

#print axioms upperProjectiveRootCount_inert

end Arxiv.«2211.10788»
