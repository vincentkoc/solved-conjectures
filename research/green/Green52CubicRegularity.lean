import Mathlib

/-! # A bounded sumset containing the span of a dense set of binary directions -/
open Finset
open scoped Pointwise
namespace Green52CubicDirections
local notation "𝔽" => ZMod 2
variable {U : Type*} [AddCommGroup U] [Module 𝔽 U] [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
private theorem twice (x : U) : x+x=0 := by rw [←two_smul 𝔽,show (2:𝔽)=0 by decide,zero_smul]

omit [Fintype U] in
/-- Once the fourfold sum has fewer than twice as many points as A,
every triple sum is already a double sum. -/
private theorem triple_reduce (A : Finset U) (hz : 0 ∈ A)
    (h : (A+A+(A+A)).card < 2*A.card) {v : U} (hv : v ∈ A+A+A) : v ∈ A+A := by
  classical
  let E := A.map (Equiv.addLeft v).toEmbedding
  have le : A ∪ E ⊆ A+A+(A+A) := by
    intro z hz'
    rcases mem_union.mp hz' with hz'|hz'
    · simpa using add_mem_add (add_mem_add hz' hz) (add_mem_add hz hz)
    · obtain ⟨x,hx,rfl⟩ := mem_map.mp hz'
      change v+x ∈ A+A+(A+A)
      obtain ⟨b,hb,c,hc,rfl⟩ := mem_add.mp hv
      rw [add_assoc b c x]
      exact add_mem_add hb (add_mem_add hc hx)
  have nondis : ¬ Disjoint A E := by
    intro dis
    have hc := card_le_card le
    rw [card_union_of_disjoint dis] at hc
    have he : E.card=A.card := card_map _
    omega
  obtain ⟨z,hzA,hzE⟩ := Finset.not_disjoint_iff.mp nondis
  obtain ⟨y,hy,eq⟩ := mem_map.mp hzE
  change v+y=z at eq
  have vv : z+y=v := by rw [←eq,add_assoc,twice,add_zero]
  exact vv ▸ add_mem_add hzA hy

private theorem slow_step (a : ℕ → ℕ) {D N : ℕ} (h₀ : 0<a 0)
    (hN : ∀ i, a i ≤ N) (dense : N ≤ 2^D * a 0) :
    ∃ j ≤ D, a (j+1) < 2*a j := by
  by_contra! h
  have growth (j : ℕ) (hj : j ≤ D+1) : 2^j*a 0 ≤ a j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have g := ih (by omega)
      have s := h j (by omega)
      rw [pow_succ]; nlinarith
  have big := growth (D+1) le_rfl
  rw [pow_succ] at big
  have pos : 0 < 2^D * a 0 := by positivity
  nlinarith [hN (D+1)]

/-- If B has density at least 2⁻ᴰ and contains zero, its linear span lies in
a (2·4ᴰ)-fold sum of B and has codimension at most D. -/
theorem dense_span (B : Finset U) (hz : 0 ∈ B) (D : ℕ)
    (dense : Fintype.card U ≤ 2^D * B.card) :
    ∃ H : Submodule 𝔽 U, (B : Set U) ⊆ H ∧
      (H : Set U) ⊆ ↑((2*4^D) • B) ∧ Module.finrank 𝔽 U ≤ Module.finrank 𝔽 H + D := by
  classical
  let A (j : ℕ) : Finset U := (4^j) • B
  have zero (j : ℕ) : 0 ∈ A j := zero_mem_nsmul hz
  have four (j : ℕ) : A (j+1) = A j+A j+(A j+A j) := by
    change (4^(j+1)) • B = _
    rw [pow_succ,Nat.mul_comm _ 4,mul_smul]
    change (4:ℕ) • A j = _
    rw [show 4=(2:ℕ)+2 by decide,add_nsmul,two_nsmul]
  obtain ⟨j,hj,slow⟩ := slow_step (fun j => (A j).card) (D:=D) (by simpa [A] using card_pos.mpr ⟨0,hz⟩)
    (fun j => (A j).card_le_univ) (by simpa [A] using dense)
  rw [four] at slow
  let C := A j + A j
  have closed {x y : U} (hx : x ∈ C) (hy : y ∈ C) : x+y ∈ C := by
    obtain ⟨b,hb,c,hc,rfl⟩ := mem_add.mp hy
    rw [←add_assoc]
    exact triple_reduce _ (zero j) slow (add_mem_add (triple_reduce _ (zero j) slow (add_mem_add hx hb)) hc)
  let H : Submodule 𝔽 U :=
    { carrier := (C : Set U)
      zero_mem' := by simpa using add_mem_add (zero j) (zero j)
      add_mem' := fun hx hy => closed hx hy
      smul_mem' := by
        intro c x hx
        fin_cases c
        · change (0:𝔽) • x ∈ C
          simpa using (show (0:U) ∈ C by simpa using add_mem_add (zero j) (zero j))
        · change (1:𝔽) • x ∈ C
          simpa using hx }
  have start : B ⊆ A j := by
    simpa only [one_nsmul] using nsmul_subset_nsmul (Subset.rfl : B ⊆ B) hz (Nat.one_le_pow _ _ (by decide : 0<4))
  have inc : B ⊆ C := fun x hx => by simpa using add_mem_add (start hx) (zero j)
  refine ⟨H,inc,?_,?_⟩
  · change C ⊆ (2*4^D) • B
    change (4^j) • B + (4^j) • B ⊆ _
    rw [←two_nsmul,←mul_smul]
    exact nsmul_subset_nsmul Subset.rfl hz (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) hj))
  · have nh : Fintype.card H = C.card := (Fintype.card_congr (show H ≃ ↥C from Equiv.refl _)).trans (Fintype.card_coe _)
    have cardbound := dense.trans (Nat.mul_le_mul_left _ (card_le_card inc))
    rw [←nh] at cardbound
    rw [Module.card_eq_pow_finrank (K:=𝔽),Module.card_eq_pow_finrank (K:=𝔽) (V:=H)] at cardbound
    have powbound : 2^(Module.finrank 𝔽 U) ≤ 2^(Module.finrank 𝔽 H+D) := by
      simpa [pow_add,Nat.mul_comm] using cardbound
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp powbound
end Green52CubicDirections
#print axioms Green52CubicDirections.dense_span

/-! # Symmetric trilinear forms with bounded contraction rank -/
open Finset
namespace Green52CubicSlices
local notation "𝔽" => ZMod 2
variable {U : Type*} [AddCommGroup U] [Module 𝔽 U] [Fintype U]

/-- If all contractions of a symmetric trilinear form have rank at most R,
there is a subspace of codimension at most R(R+1) on which any two slots annihilate the form. -/
theorem bounded_slices (T : U →ₗ[𝔽] U →ₗ[𝔽] Module.Dual 𝔽 U)
    (swap₁ : ∀ a b, T a b = T b a) (swap₂ : ∀ a b c, T a b c = T a c b)
    (R : ℕ) (hb : ∀ a, Module.finrank 𝔽 (T a).range ≤ R) :
    ∃ H : Submodule 𝔽 U, Module.finrank 𝔽 U ≤ Module.finrank 𝔽 H + R*(R+1) ∧
      ∀ h : H, ∀ x : U, ∀ y : H, T h.val x y.val = 0 := by
  classical
  obtain ⟨a,_,hmax⟩ := exists_max_image (univ : Finset U)
    (fun u => Module.finrank 𝔽 (T u).range) univ_nonempty
  let W := (T a).range
  let r := Module.finrank 𝔽 W
  let e := Module.finBasis 𝔽 W
  choose pre himg using (fun i : Fin r => (e i).property)
  let j : W →ₗ[𝔽] U := e.constr 𝔽 pre
  have hj : (T a).comp j = W.subtype := by
    apply e.ext
    intro i
    simpa [j] using himg i
  have ident (w : W) : T a (j w) = w.val := LinearMap.congr_fun hj w
  let row (i : Fin r) := T (j (e i))
  let Q : U →ₗ[𝔽] (W × ((i : Fin r) → (row i).range)) := (T a).rangeRestrict.prod (LinearMap.pi (fun i : Fin r => (row i).rangeRestrict))
  have first (h : Q.ker) : T a h.val = 0 :=
    congrArg (fun z => ((z.1 : W) : Module.Dual 𝔽 U)) (show Q h.val = 0 from h.property)
  have frozen (h : Q.ker) : (T h.val).comp j = 0 := by
    apply e.ext
    intro i
    change T h.val (j (e i))=0
    rw [swap₁]
    exact congrArg (fun z => ((z.2 i : (row i).range) : Module.Dual 𝔽 U))
      (show Q h.val = 0 from h.property)
  have same (h : Q.ker) : (T (a+h.val)).range = W := by
    symm
    apply Submodule.eq_of_le_of_finrank_le _ (hmax _ (mem_univ _))
    intro w hw
    let v : W := ⟨w,hw⟩
    refine ⟨j v,?_⟩
    have zero : T h.val (j v) = 0 := LinearMap.congr_fun (frozen h) v
    simpa only [map_add,LinearMap.add_apply,zero,add_zero] using ident v
  refine ⟨Q.ker,?_,?_⟩
  · have dim := LinearMap.finrank_range_add_finrank_ker (K:=𝔽) (V:=U) (V₂:=W × ((i : Fin r) → (row i).range)) Q
    let _ (i : Fin r) : Module.Free 𝔽 (row i).range := Module.Free.of_divisionRing (K:=𝔽) (V:=(row i).range)
    let _ : Module.Free 𝔽 ((i : Fin r) → (row i).range) := Module.Free.of_divisionRing (K:=𝔽) (V:=((i : Fin r) → (row i).range))
    have le := Submodule.finrank_le Q.range
    rw [Module.finrank_prod,Module.finrank_pi_fintype] at le
    have sr : ∑ i : Fin r, Module.finrank 𝔽 (row i).range ≤ r*R := by
      calc
        _ ≤ ∑ _ : Fin r, R := Finset.sum_le_sum (fun i _ => hb (j (e i)))
        _ = _ := by simp
    have hr : r≤R := hb a
    change Module.finrank 𝔽 Q.range ≤ r + ∑ i : Fin r, Module.finrank 𝔽 (row i).range at le
    nlinarith [Nat.mul_le_mul_right R hr]
  · intro h x y
    have h₁ : T (a+h.val) x ∈ W := (same h).le (LinearMap.mem_range_self _ _)
    have h₂ : T a x ∈ W := LinearMap.mem_range_self _ _
    have hx : T h.val x ∈ W := by
      simpa only [map_add,LinearMap.add_apply,add_sub_cancel_left] using W.sub_mem h₁ h₂
    obtain ⟨u,hu⟩ := hx
    rw [←hu,swap₂,first y]
    rfl
end Green52CubicSlices
#print axioms Green52CubicSlices.bounded_slices

/-! # Removing a dense set of low-rank contractions -/
open Finset
open scoped Pointwise
namespace Green52CubicRegularity
local notation "𝔽" => ZMod 2
variable {U : Type*} [AddCommGroup U] [Module 𝔽 U] [Fintype U]
abbrev Trilinear (E : Type*) [AddCommGroup E] [Module 𝔽 E] :=
  E →ₗ[𝔽] E →ₗ[𝔽] Module.Dual 𝔽 E

/-- Restrict each of the three arguments to the same subspace. -/
def restrictTri (T : Trilinear U) (H : Submodule 𝔽 U) : Trilinear H where
  toFun h := H.subtype.dualMap.comp ((T h.val).comp H.subtype)
  map_add' := by intro x y; ext a b; simp
  map_smul' := by intro c x; ext a b; simp

theorem rank_restrict (T : Trilinear U) (H : Submodule 𝔽 U) (h : H) :
    Module.finrank 𝔽 ((restrictTri T H) h).range ≤ Module.finrank 𝔽 (T h.val).range := by
  change Module.finrank 𝔽 (H.subtype.dualMap.comp ((T h.val).comp H.subtype)).range ≤ _
  rw [LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))

private theorem rank_sum (T : Trilinear U) (x y : U) :
    Module.finrank 𝔽 (T (x+y)).range ≤ Module.finrank 𝔽 (T x).range + Module.finrank 𝔽 (T y).range := by
  rw [map_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

def cost (D R : ℕ) : ℕ := let L := (2*4^D)*R; D+L*(L+1)

/-- A density of at least 2⁻ᴰ of rank-at-most-R contractions implies vanishing of
the entire trilinear form on a subspace of codimension bounded in D and R alone. -/
theorem dense_low_rank (T : Trilinear U) (swap₁ : ∀ x y, T x y=T y x)
    (swap₂ : ∀ x y z, T x y z=T x z y) (D R : ℕ) (B : Finset U) (zero : 0∈B)
    (dense : Fintype.card U ≤ 2^D * B.card)
    (bounded : ∀ a∈B, Module.finrank 𝔽 (T a).range ≤ R) :
    ∃ E : Submodule 𝔽 U, Module.finrank 𝔽 U ≤ Module.finrank 𝔽 E + cost D R ∧
      ∀ x y z : E, T x.val y.val z.val=0 := by
  classical
  obtain ⟨H,_,cover,dim⟩ := Green52CubicDirections.dense_span B zero D dense
  have sum_bound (n : ℕ) (a : U) (ha : a ∈ n • B) : Module.finrank 𝔽 (T a).range ≤ n*R := by
    induction n generalizing a with
    | zero =>
      have h0 : a=0 := by simpa using ha
      simp [h0]
    | succ n ih =>
      rw [succ_nsmul] at ha
      obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp ha
      exact (rank_sum T _ _).trans (by simpa only [Nat.succ_mul] using Nat.add_le_add (ih x hx) (bounded _ hy))
  let L := (2*4^D)*R
  have all_rank (h : H) : Module.finrank 𝔽 ((restrictTri T H) h).range ≤ L :=
    (rank_restrict T H h).trans (sum_bound _ _ (cover h.property))
  obtain ⟨J,dimJ,vanish⟩ := Green52CubicSlices.bounded_slices (restrictTri T H)
    (fun a b => LinearMap.ext (fun c => LinearMap.congr_fun (swap₁ a.val b.val) c.val))
    (fun a b c => swap₂ _ _ _) L all_rank
  let E := J.map H.subtype
  have de : Module.finrank 𝔽 J = Module.finrank 𝔽 E :=
    (Submodule.equivMapOfInjective H.subtype H.subtype_injective J).finrank_eq
  refine ⟨E,?_,?_⟩
  · change _ ≤ Module.finrank 𝔽 E + (D+L*(L+1))
    omega
  · rintro ⟨_,x,hx,rfl⟩ ⟨_,y,_,rfl⟩ ⟨_,z,hz,rfl⟩
    exact vanish ⟨x,hx⟩ y ⟨z,hz⟩

/-- A simultaneous restriction for a finite family. On the resulting subspace each
form either vanishes or has fewer than a 2⁻ᴰ fraction of rank-at-most-R directions. -/
theorem simultaneous {ι : Type*} [Fintype ι] (T : ι → Trilinear U)
    (swap₁ : ∀ i x y, T i x y=T i y x) (swap₂ : ∀ i x y z, T i x y z=T i x z y)
    (D R : ℕ) :
    ∃ H : Submodule 𝔽 U, Module.finrank 𝔽 U ≤ Module.finrank 𝔽 H + Fintype.card ι * cost D R ∧
      ∀ i, (∀ x y z : H, T i x.val y.val z.val=0) ∨
        2^D * Nat.card {x : H // Module.finrank 𝔽 ((restrictTri (T i) H) x).range ≤ R} < Nat.card H := by
  classical
  let van (H : Submodule 𝔽 U) (i : ι) := ∀ x y z : H, T i x.val y.val z.val=0
  let low (H : Submodule 𝔽 U) := univ.filter (van H)
  let bad (H : Submodule 𝔽 U) (i : ι) := univ.filter (fun x : H =>
    Module.finrank 𝔽 ((restrictTri (T i) H) x).range ≤ R)
  let good (H : Submodule 𝔽 U) := ∀ i, van H i ∨ 2^D*(bad H i).card < Nat.card H
  have step (H : Submodule 𝔽 U) (hh : ¬ good H) :
      ∃ E : Submodule 𝔽 U, E ≤ H ∧ (low H).card < (low E).card ∧
        Module.finrank 𝔽 H ≤ Module.finrank 𝔽 E + cost D R := by
    change ¬ ∀ i, van H i ∨ 2^D*(bad H i).card < Nat.card H at hh
    push Not at hh
    obtain ⟨i,hi,bd⟩ := hh
    have hz : (0:H) ∈ bad H i := by
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rw [map_zero,LinearMap.range_zero,finrank_bot]
      exact Nat.zero_le _
    have hbd (a) (ha : a ∈ bad H i) := (mem_filter.mp ha).2
    obtain ⟨J,dim,zero⟩ := dense_low_rank (restrictTri (T i) H)
      (fun a b => LinearMap.ext (fun c => LinearMap.congr_fun (swap₁ i a.val b.val) c.val))
      (fun a b c => swap₂ _ _ _ _) D R _ hz (by simpa only [Nat.card_eq_fintype_card] using bd) hbd
    let E := J.map H.subtype
    have sub : E ≤ H := by rintro _ ⟨x,_,rfl⟩; exact x.property
    have win : van E i := by
      rintro ⟨_,x,hx,rfl⟩ ⟨_,y,hy,rfl⟩ ⟨_,z,hz',rfl⟩
      exact zero ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz'⟩
    have inc : low H ⊆ low E := by
      intro l hl
      apply mem_filter.mpr
      refine ⟨mem_univ _,fun x y z => ?_⟩
      exact (mem_filter.mp hl).2 ⟨_,sub x.property⟩ ⟨_,sub y.property⟩ ⟨_,sub z.property⟩
    have de := (Submodule.equivMapOfInjective H.subtype H.subtype_injective J).finrank_eq
    refine ⟨E,sub,card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨inc,?_⟩),?_⟩
    · intro eq
      have mem : i∈low E := mem_filter.mpr ⟨mem_univ _,win⟩
      rw [←eq] at mem
      exact hi (mem_filter.mp mem).2
    · exact dim.trans_eq (congrArg (· + cost D R) de)
  have iter (n : ℕ) (H : Submodule 𝔽 U) (fuel : Fintype.card ι ≤ (low H).card+n) :
      ∃ E : Submodule 𝔽 U, Module.finrank 𝔽 H ≤ Module.finrank 𝔽 E + n*cost D R ∧ good E := by
    induction n generalizing H with
    | zero =>
      refine ⟨H,by simp,?_⟩
      by_contra h
      obtain ⟨E,_,grow,_⟩ := step H h
      have := (low E).card_le_univ
      omega
    | succ n ih =>
      by_cases h : good H
      · exact ⟨H,Nat.le_add_right _ _,h⟩
      obtain ⟨J,_,grow,loss⟩ := step H h
      obtain ⟨E,dim,g⟩ := ih J (by omega)
      refine ⟨E,?_,g⟩
      rw [Nat.succ_mul]
      omega
  obtain ⟨E,dim,g⟩ := iter (Fintype.card ι) ⊤ (by omega)
  refine ⟨E,by simpa using dim,fun i => ?_⟩
  simpa only [van,bad,Nat.card_eq_fintype_card,Fintype.card_subtype] using g i

end Green52CubicRegularity
#print axioms Green52CubicRegularity.dense_low_rank
#print axioms Green52CubicRegularity.simultaneous
