import Green33SingerProjectiveOverlap
import Mathlib.Analysis.Complex.Basic

/-! Multiplicative convolution on a scalar quotient and hyper-Kloosterman sums. -/

open Finset
open scoped BigOperators Pointwise

namespace Green33SingerKloosterman

variable {G H : Type*} [CommGroup G] [Fintype G] [CommGroup H] [Fintype H]

/-- Multiplicative, unnormalized convolution. -/
noncomputable def conv (f g : G→ℂ) (z : G) : ℂ := ∑ x : G, f x * g (z/x)

/-- Positive convolution powers, starting at power one. -/
noncomputable def iter (f : G→ℂ) : ℕ→G→ℂ
  | 0 => f
  | r+1 => conv f (iter f r)

noncomputable def push (π : G→*H) (f : G→ℂ) (z : H) : ℂ := by
  classical exact ∑ x : G, if π x=z then f x else 0

private theorem test_push (π : G→*H) (f : G→ℂ) (g : H→ℂ) :
    ∑ z : H, push π f z*g z=∑ x : G, f x*g (π x) := by
  classical
  unfold push
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,if_true]

theorem push_conv (π : G→*H) (f g : G→ℂ) (c : H) :
    push π (conv f g) c=conv (push π f) (push π g) c := by
  classical
  unfold conv
  rw [test_push]
  unfold push
  simp only [ite_sum_zero,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  calc
    (∑ z : G, if π z=c then f x*g (z/x) else 0) =
        ∑ y : G, if π (x*y)=c then f x*g ((x*y)/x) else 0 :=
      (Equiv.sum_comp (Equiv.mulLeft x) (fun z => if π z=c then f x*g (z/x) else 0)).symm
    _ = _ := by
      apply sum_congr rfl
      intro y _
      rw [map_mul,mul_div_cancel_left,mul_ite,mul_zero]
      simp only [eq_div_iff_mul_eq',mul_comm (π x) (π y)]

theorem push_iter (π : G→*H) (f : G→ℂ) (r : ℕ) (c : H) :
    push π (iter f r) c=iter (push π f) r c := by
  induction r generalizing c with
  | zero => rfl
  | succ r ih => rw [iter,push_conv,iter,show push π (iter f r)=_ from funext ih]

private theorem div_sum (g : G→ℂ) (z : G) : (∑ x : G, g (z/x))=∑ y : G,g y := by
  let e : G≃G := (Equiv.inv G).trans (Equiv.mulLeft z)
  simp only [div_eq_mul_inv]
  exact Equiv.sum_comp e g

private theorem mass_conv (f g : G→ℂ) :
    ∑ z : G,conv f g z=(∑ x : G,f x)*(∑ x : G,g x) := by
  unfold conv
  rw [sum_comm,sum_mul]
  apply sum_congr rfl
  intro x _
  rw [← mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.divRight x) g

private theorem mass_iter (f : G→ℂ) (r : ℕ) : (∑ z : G,iter f r z)=(∑ x : G,f x)^(r+1) := by
  induction r with
  | zero => simp [iter]
  | succ r ih => rw [iter,mass_conv,ih,pow_succ];ring

private theorem iter_shift (f g : G→ℂ) (d : ℂ) (hd : ∀ x, f x=g x+d) (r : ℕ) :
    ∃ e : ℂ, ∀ x, iter f r x=iter g r x+e := by
  induction r with
  | zero => exact ⟨d,hd⟩
  | succ r ih =>
    obtain ⟨e,he⟩ := ih
    refine ⟨(∑ x : G,g x)*e+d*(∑ x : G,iter g r x)+Fintype.card G*(d*e),?_⟩
    intro z
    simp only [iter,conv,hd,he,add_mul,mul_add,sum_add_distrib,← mul_sum,← sum_mul,div_sum,
      sum_const,card_univ,nsmul_eq_mul]
    ring

/-- A constant difference between the one-step kernels changes every centered
convolution power by zero. This version also determines the discarded mean. -/
theorem iter_shift_mass (f g : G→ℂ) (d : ℂ) (hd : ∀ x, f x=g x+d) (r : ℕ) (z : G) :
    Fintype.card G*(iter f r z-iter g r z)=
      (∑ x : G,f x)^(r+1)-(∑ x : G,g x)^(r+1) := by
  obtain ⟨e,he⟩ := iter_shift f g d hd r
  have m := sum_congr (s₁:=univ) rfl (fun x _ => he x)
  simp only [sum_add_distrib,mass_iter,sum_const,card_univ,nsmul_eq_mul] at m
  rw [he];linear_combination -m

open Green33SingerProjectiveOverlap

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
variable [DecidableEq F] [DecidableEq K]
noncomputable local instance : Fintype (Plane F K) := Fintype.ofFinite _

noncomputable abbrev proj : Kˣ →* Plane F K := QuotientGroup.mk' (scalars F K)
private abbrev scalar := Units.map (algebraMap F K).toMonoidHom

private theorem proj_fiber (f : Kˣ→ℂ) (w : Kˣ) :
    push (proj (F:=F) (K:=K)) f (proj (F:=F) w)=∑ s : Fˣ,f (scalar s*w) := by
  classical
  unfold push
  trans ∑ z ∈ univ.filter (fun x : Kˣ => proj (F:=F) x=proj (F:=F) w),f z
  · rw [sum_filter]
    apply sum_congr rfl
    intro z _
    by_cases h : proj (F:=F) z=proj (F:=F) w <;> simp only [h,if_true,if_false]
  symm
  apply sum_bij (fun (s : Fˣ) _ => scalar s*w)
  · intro s _
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [map_mul,show proj (F:=F) (scalar s : Kˣ)=1 from
      (QuotientGroup.eq_one_iff _).mpr ⟨s,rfl⟩,one_mul]
  · intro a _ b _ eq
    exact Units.ext ((algebraMap F K).injective (congrArg (fun z : Kˣ => (z:K)) (mul_right_cancel eq)))
  · intro z hz
    obtain ⟨s,hs⟩ := QuotientGroup.eq_iff_div_mem.mp (mem_filter.mp hz).2
    exact ⟨s,mem_univ _,(eq_div_iff_mul_eq').mp hs⟩
  · intros;rfl

private theorem units_sum (f : F→ℂ) : (∑ s : Fˣ,f (s:F))+f 0 = ∑ s : F,f s := by
  classical
  rw [← sum_erase_add _ _ (mem_univ (0:F))]
  congr 1
  apply sum_bij (fun (s : Fˣ) _ => (s:F))
  · intro s _;exact mem_erase.mpr ⟨s.ne_zero,mem_univ _⟩
  · intro a _ b _ e;exact Units.ext e
  · intro z hz;exact ⟨Units.mk0 z (mem_erase.mp hz).1,mem_univ _,rfl⟩
  · intros;rfl

/-- The radial average of an additive phase on a scalar orbit has two levels,
separated by exactly q. This holds in every characteristic. -/
theorem orbit_phase (L : K→ₗ[F] F) (ψ : AddChar F ℂ) (nt : ψ≠0) (w : Kˣ) :
    push (proj (F:=F) (K:=K)) (fun z : Kˣ => ψ (L (z:K))) (proj (F:=F) w)=
      (if L (w:K)=0 then (Fintype.card F:ℂ) else 0)-1 := by
  classical
  rw [proj_fiber]
  have scale (s : Fˣ) : L ((scalar s*w : Kˣ):K)=(s:F)*L (w:K) := by
    change L ((algebraMap F K) (s:F)*(w:K))=_
    rw [← Algebra.smul_def,map_smul,smul_eq_mul]
  simp only [scale]
  have e := units_sum (fun s : F => ψ (s*L (w:K)))
  simp only [zero_mul,AddChar.map_zero_eq_one] at e
  by_cases h : L (w:K)=0
  · simpa [h] using eq_sub_of_add_eq e
  · have z : (∑ s : F, ψ (s*L (w:K)))=0 :=
      (Equiv.sum_comp (Equiv.mulRight₀ _ h) ψ).trans (AddChar.sum_eq_zero_iff_ne_zero.mpr nt)
    rw [z] at e
    simpa only [if_neg h] using eq_sub_of_add_eq e

/-- Projective points of the hyperplane of a linear functional. -/
noncomputable def hyperplane (L : K→ₗ[F] F) : Finset (Plane F K) := by
  classical exact univ.filter fun c => ∃ w : Kˣ, proj (F:=F) w=c ∧ L (w:K)=0

omit [Fintype F] in
private theorem mem_hyperplane (L : K→ₗ[F] F) (w : Kˣ) :
    proj (F:=F) w∈hyperplane L ↔ L (w:K)=0 := by
  classical
  constructor
  · intro h
    obtain ⟨z,hz,hL⟩ := (mem_filter.mp h).2
    obtain ⟨s,hs⟩ := QuotientGroup.eq_iff_div_mem.mp hz.symm
    have mul : scalar s*z=w := (eq_div_iff_mul_eq').mp hs
    rw [← mul]
    change L (algebraMap F K (s:F)*(z:K))=0
    rw [← Algebra.smul_def,map_smul,hL,smul_zero]
  · intro h
    exact mem_filter.mpr ⟨mem_univ _,w,rfl,h⟩

noncomputable def mark {G : Type*} [DecidableEq G] (D : Finset G) (c : G) : ℂ :=
  if c∈D then 1 else 0

private theorem iter_smul (a : ℂ) (f : G→ℂ) (r : ℕ) (c : G) :
    iter (fun x => a*f x) r c=a^(r+1)*iter f r c := by
  induction r generalizing c with
  | zero => simp [iter]
  | succ r ih =>
    simp only [iter,conv,ih]
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    ring

private theorem mass_mark {G : Type*} [Fintype G] [DecidableEq G] (D : Finset G) :
    ∑ x : G,mark D x=(D.card:ℂ) := by
  unfold mark
  rw [← sum_filter];simp

omit [Fintype F] [DecidableEq F] in
private theorem full_phase_zero (L : K→ₗ[F] F) (onto : Function.Surjective L)
    (ψ : AddChar F ℂ) (nt : ψ≠0) : (∑ x : Kˣ, ψ (L (x:K))) = -1 := by
  let χ := ψ.compAddMonoidHom L.toAddMonoidHom
  have nontriv : χ≠0 := by
    intro hz
    apply nt
    ext a
    obtain ⟨x,rfl⟩ := onto a
    exact DFunLike.congr_fun hz x
  have zero := AddChar.sum_eq_zero_iff_ne_zero.mpr nontriv
  have all := units_sum (fun z : K => ψ (L z))
  change (∑ z : K, ψ (L z))=0 at zero
  rw [zero,map_zero,AddChar.map_zero_eq_one] at all
  linear_combination all

/-- The unnormalized rank-(r+1) hyper-Kloosterman sum with additive phase
ψ∘L. Convolution fixes the product of all nonzero input variables. -/
noncomputable def kloosterman (L : K→ₗ[F] F) (ψ : AddChar F ℂ) (r : ℕ) : Kˣ→ℂ :=
  iter (fun x : Kˣ => ψ (L (x:K))) r

/-- Exact reduction in arbitrary characteristic, for every positive rank.
The summed constant is determined by the two total masses. -/
theorem hyperplane_identity [DecidableEq (Plane F K)] (L : K→ₗ[F] F) (onto : Function.Surjective L)
    (ψ : AddChar F ℂ) (nt : ψ≠0) (r : ℕ) (c : Plane F K) :
    (Fintype.card (Plane F K):ℂ) *
      ((Fintype.card F:ℂ)^(r+1)*iter (mark (hyperplane L)) r c -
        push (proj (F:=F) (K:=K)) (kloosterman L ψ r) c) =
    ((Fintype.card F:ℂ)*(hyperplane L).card)^(r+1) - (-1:ℂ)^(r+1) := by
  classical
  let f := fun z : Plane F K => (Fintype.card F:ℂ)*mark (hyperplane L) z
  let g : Plane F K→ℂ := push (H:=Plane F K) (proj (F:=F) (K:=K)) (fun x : Kˣ => ψ (L (x:K)))
  have diff (x : Plane F K) : f x=g x+1 := by
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (scalars F K) x
    dsimp only [f,g]
    rw [orbit_phase L ψ nt]
    change (Fintype.card F:ℂ)*(if proj (F:=F) w∈hyperplane L then 1 else 0)=_
    by_cases h : L (w:K)=0
    · rw [if_pos ((mem_hyperplane L w).mpr h),if_pos h,mul_one,sub_add_cancel]
    · rw [if_neg (fun hz => h ((mem_hyperplane L w).mp hz)),if_neg h,mul_zero,sub_add_cancel]
  have mf : (∑ z,f z)=(Fintype.card F:ℂ)*(hyperplane L).card := by
    dsimp only [f];rw [← mul_sum,mass_mark]
  have mg : (∑ z,g z)=-1 := by
    have e := test_push (H:=Plane F K) (proj (F:=F) (K:=K)) (fun x : Kˣ => ψ (L (x:K))) (fun _ => 1)
    simpa only [mul_one,full_phase_zero L onto ψ nt] using e
  have iden := iter_shift_mass f g 1 diff r c
  rw [mf,mg] at iden
  simpa only [f,g,iter_smul,kloosterman,push_iter] using iden

#print axioms hyperplane_identity

omit [DecidableEq F] in
/-- Scalar orbits of nonzero vectors in a simultaneous vanishing set. -/
private theorem count_orbits (T : Finset (Plane F K)) (S : Finset K) (zero : 0∈S)
    (mem : ∀ w : Kˣ, proj (F:=F) w∈T ↔ (w:K)∈S) :
    S.card=(Fintype.card F-1)*T.card+1 := by
  classical
  let U := (QuotientGroup.mk (s:=scalars F K) ⁻¹' (T:Set (Plane F K)) : Set Kˣ)
  let e : U ≃ (S.erase 0 : Finset K) := {
    toFun := fun x => ⟨(x.val:K),mem_erase.mpr ⟨x.val.ne_zero,(mem x.val).mp x.property⟩⟩
    invFun := fun x => ⟨Units.mk0 x.val (mem_erase.mp x.property).1,
      (mem _).mpr (mem_erase.mp x.property).2⟩
    left_inv := fun _ => Subtype.ext (Units.ext rfl)
    right_inv := fun _ => Subtype.ext rfl }
  have eq : Nat.card U=(S.erase 0).card := (Nat.card_congr e).trans (by rw [Nat.card_eq_fintype_card,Fintype.card_coe])
  have h : Nat.card U=Nat.card (scalars F K)*Nat.card (T : Set (Plane F K)) := QuotientGroup.card_preimage_mk _ _
  rw [← card_erase_add_one zero,← eq,h,scalar_card]
  congr 2
  exact Nat.card_eq_fintype_card.trans (Fintype.card_coe T)

omit [Fintype F] [DecidableEq F] [DecidableEq K] in
private theorem kernel_count {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    (L : K→ₗ[F] V) (onto : Function.Surjective L) :
    Fintype.card K=Fintype.card V*Nat.card L.ker := by
  let e := LinearMap.quotKerEquivOfSurjective L onto
  have eq := L.ker.toAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
  change Nat.card K=Nat.card (K ⧸ L.ker)*Nat.card L.ker at eq
  rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at eq
  exact eq

omit [Fintype F] in
/-- Multiplication by a nonscalar gives a second independent linear condition. -/
private theorem pair_onto (L : K→ₗ[F] F) (onto : Function.Surjective L) (w : Kˣ)
    (ns : proj (F:=F) w≠1) :
    Function.Surjective (L.prod (L.comp (Algebra.lmul F K (w:K)))) := by
  obtain ⟨a,ha⟩ := onto 1
  let M := L.comp (Algebra.lmul F K (w:K))
  have pick : ∃ b : K, L b=0 ∧ M b≠0 := by
    by_contra! h
    have eq (x : K) : M x=L x*M a := by
      have z : L (x-(L x) • a)=0 := by simp [ha]
      have t := h (x-(L x) • a) z
      rw [map_sub,map_smul,smul_eq_mul,sub_eq_zero] at t
      exact t
    have scalarEq : (w:K)=algebraMap F K (M a) := by
      by_contra different
      let g := (w:K)-algebraMap F K (M a)
      have gn : g≠0 := sub_ne_zero.mpr different
      have vanish (x : K) : L (g*x)=0 := by
        change L (((w:K)-algebraMap F K (M a))*x)=0
        rw [sub_mul,map_sub,← Algebra.smul_def,map_smul,smul_eq_mul]
        change M x-M a*L x=0
        rw [eq x,mul_comm,sub_self]
      have atA := vanish (g⁻¹*a)
      rw [← mul_assoc,mul_inv_cancel₀ gn,one_mul,ha] at atA
      exact one_ne_zero atA
    have nz : M a≠0 := fun h => w.ne_zero (by rw [scalarEq,h,map_zero])
    exact ns ((QuotientGroup.eq_one_iff _).mpr ⟨Units.mk0 _ nz,Units.ext scalarEq.symm⟩)
  obtain ⟨b,hb,hM⟩ := pick
  intro y
  refine ⟨y.1 • a+((y.2-y.1*M a)/M b) • b,Prod.ext ?_ ?_⟩
  · change L _=y.1
    simp [ha,hb]
  · change M _=y.2
    simp only [map_add,map_smul,smul_eq_mul,div_mul_cancel₀ _ hM]
    ring

omit [Fintype F] [DecidableEq F] [DecidableEq K] in
private theorem zeros_count {V : Type*} [AddCommGroup V] [Module F V] [Fintype V] [DecidableEq V]
      (f : K→ₗ[F] V) (sur : Function.Surjective f) :
      Fintype.card K=Fintype.card V*(univ.filter fun x : K => f x=0).card := by
    have e := kernel_count f sur
    convert e using 2
    symm
    let b : f.ker ≃ (univ.filter fun x : K => f x=0 : Finset K) := {
      toFun := fun x => ⟨x.val,mem_filter.mpr ⟨mem_univ _,x.property⟩⟩
      invFun := fun x => ⟨x.val,(mem_filter.mp x.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr b).trans (Nat.card_eq_fintype_card.trans (Fintype.card_coe _))

/-- The cubic line is perfect in every characteristic. These parameters are
proved for the kernel of any surjective linear functional. -/
theorem cubic_parameters [DecidableEq (Plane F K)] (L : K→ₗ[F] F) (onto : Function.Surjective L)
    (cubic : Fintype.card K=(Fintype.card F)^3) :
    (hyperplane L).card=Fintype.card F+1 ∧ ∀ w : Plane F K, w≠1 →
      ((hyperplane L).filter fun z => w*z∈hyperplane L).card=1 := by
  classical
  let q := Fintype.card F
  have qp : 1<q := Fintype.one_lt_card
  have pos : 0<q-1 := by omega
  constructor
  · let S := univ.filter fun x : K => L x=0
    have e := count_orbits (hyperplane L) S (by simp [S]) (fun w => (mem_hyperplane L w).trans (by simp only [S,mem_filter,mem_univ,true_and]))
    have ks := cubic.symm.trans (zeros_count L onto)
    change q^3=q*S.card at ks
    have sc : S.card=q^2 := Nat.eq_of_mul_eq_mul_left (by omega : 0<q) (ks.symm.trans (by ring))
    change (hyperplane L).card=q+1
    change S.card=(q-1)*(hyperplane L).card+1 at e
    apply Nat.eq_of_mul_eq_mul_left pos
    have h := Nat.sub_add_cancel (show 1≤q by omega)
    nlinarith only [e,sc,congrArg (fun x => x*(q+1)) h]
  · intro w hw
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (scalars F K) w
    let f := L.prod (L.comp (Algebra.lmul F K (u:K)))
    let S := univ.filter fun x : K => f x=0
    let T := (hyperplane L).filter fun z => proj (F:=F) u*z∈hyperplane L
    have e := count_orbits T S (by simp [S]) (fun x => by
      simp only [T,S,mem_filter,mem_univ,true_and,← map_mul (proj (F:=F) (K:=K)),mem_hyperplane]
      change L (x:K)=0 ∧ L ((u:K)*(x:K))=0 ↔ (_,_)=((0:F),(0:F))
      simp only [Prod.mk.injEq]
      rfl)
    have k := cubic.symm.trans (zeros_count f (pair_onto L onto u hw))
    change q^3=Fintype.card (F×F)*S.card at k
    rw [Fintype.card_prod] at k
    have sc : S.card=q := Nat.eq_of_mul_eq_mul_left (by positivity : 0<q*q) (k.symm.trans (by dsimp [q];ring))
    change T.card=1
    change S.card=(q-1)*T.card+1 at e
    apply Nat.eq_of_mul_eq_mul_left pos
    omega

/-- Finite error after supplying a pointwise bound B for the ordinary
unnormalized hyper-Kloosterman sum. The exact identity above has no such input. -/
theorem rank_error [DecidableEq (Plane F K)] (L : K→ₗ[F] F) (onto : Function.Surjective L)
    (ψ : AddChar F ℂ) (nt : ψ≠0) (r : ℕ) (B : ℝ)
    (bound : ∀ x : Kˣ, ‖kloosterman L ψ r x‖≤B) (c : Plane F K) :
    ‖iter (mark (hyperplane L)) r c-((hyperplane L).card:ℂ)^(r+1)/Fintype.card (Plane F K)‖ ≤
      (((Fintype.card F:ℝ)-1)*B+1/Fintype.card (Plane F K))/(Fintype.card F:ℝ)^(r+1) := by
  classical
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (scalars F K) c
  let v := Fintype.card (Plane F K)
  let q := Fintype.card F
  let k := (hyperplane L).card
  let p := iter (mark (hyperplane L)) r (proj (F:=F) w)
  let S := push (proj (F:=F) (K:=K)) (kloosterman L ψ r) (proj (F:=F) w)
  have h := hyperplane_identity L onto ψ nt r (proj (F:=F) w)
  change (v:ℂ)*((q:ℂ)^(r+1)*p-S)=((q:ℂ)*k)^(r+1)-(-1)^(r+1) at h
  have vn : 0<v := Fintype.card_pos
  have qn : 0<q := Fintype.card_pos
  have vc : (v:ℂ)≠0 := by exact_mod_cast vn.ne'
  have qc : (q:ℂ)≠0 := by exact_mod_cast qn.ne'
  have iden : p-(k:ℂ)^(r+1)/v=(S-(-1:ℂ)^(r+1)/v)/(q:ℂ)^(r+1) := by
    field_simp [vc,qc]
    rw [mul_pow] at h
    linear_combination h
  have orbit : ‖S‖≤((q:ℝ)-1)*B := by
    dsimp only [S]
    rw [proj_fiber]
    refine (norm_sum_le ..).trans ((sum_le_sum fun x _ => bound _).trans_eq ?_)
    simp only [sum_const,card_univ,nsmul_eq_mul,Fintype.card_units,Nat.cast_sub
      (by exact Nat.succ_le_of_lt Fintype.card_pos : 1≤Fintype.card F),Nat.cast_one,q]
  change ‖p-(k:ℂ)^(r+1)/v‖≤_
  rw [iden,norm_div,norm_pow,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  refine (norm_sub_le ..).trans (add_le_add orbit ?_)
  simp [norm_pow,v]

#print axioms cubic_parameters
#print axioms rank_error

/-- Convolution agrees with the usual constrained tuple definition, over
units, with an unnormalized sum and a fixed product. -/
private theorem iter_as_tuples [DecidableEq G] (f : G→ℂ) (r : ℕ) (c : G) :
    iter f r c=∑ x : Fin (r+1)→G, if ∏ i,x i=c then ∏ i,f (x i) else 0 := by
  classical
  induction r generalizing c with
  | zero =>
    change f c=∑ x : Fin 1→G, if ∏ i,x i=c then ∏ i,f (x i) else 0
    simp only [Fin.prod_univ_one]
    let e := Equiv.funUnique (Fin 1) G
    calc
      f c = ∑ a : G, if a=c then f a else 0 := by simp
      _ = _ := (Equiv.sum_comp e (fun a => if a=c then f a else 0)).symm
  | succ r ih =>
    let S (x : Fin (r+1+1)→G) := if ∏ i,x i=c then ∏ i,f (x i) else 0
    let e : G × (Fin (r+1)→G) ≃ (Fin (r+1+1)→G) := Fin.consEquiv (fun _ : Fin (r+1+1) => G)
    change conv f (iter f r) c=∑ x,S x
    rw [← Equiv.sum_comp e S,Fintype.sum_prod_type]
    unfold conv
    apply sum_congr rfl
    intro x _
    rw [ih,mul_sum]
    apply sum_congr rfl
    intro y _
    change _=(if ∏ i,Fin.cons (α:=fun _ : Fin (r+1+1) => G) x y i=c then ∏ i,f (Fin.cons (α:=fun _ : Fin (r+1+1) => G) x y i) else 0)
    simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_ite,mul_zero,eq_div_iff_mul_eq'']

omit [Fintype F] [DecidableEq F] in
theorem kloosterman_tuples (L : K→ₗ[F] F) (ψ : AddChar F ℂ) (r : ℕ) (w : Kˣ) :
    kloosterman L ψ r w=∑ x : Fin (r+1)→Kˣ with ∏ i,x i=w, ψ (L (∑ i,(x i:K))) := by
  classical
  rw [kloosterman,iter_as_tuples,sum_filter]
  apply sum_congr rfl
  intro x _
  have ep (s : Finset (Fin (r+1))) : ψ (∑ i ∈ s,L (x i:K))=∏ i ∈ s,ψ (L (x i:K)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [sum_insert hi,prod_insert hi,AddChar.map_add_eq_mul,ih]
  simp only [map_sum,ep]

#print axioms kloosterman_tuples

end Green33SingerKloosterman
