import Green51MoorePreimages
import Green51BCHCompression

/-! # Exact kernel threshold for the projected fourth BCH coordinate -/

open Green50Downsets Green51BCH
open scoped Pointwise
namespace Green51BCHCompression
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K]

/-- Vanishing Moore determinants on an input space make its pairs along a fixed
nonzero direction a flat in the projected double. -/
theorem produces_flat {H : Type*} [AddCommGroup H] [Module F H] [Finite K] (L : K →ₗ[F] H) (U : Submodule F K)
    (t : K) (ht : t∈U) (nz:t≠0)
    (kill : ∀ b∈U,∀ c∈U,L (moore t b c)=0) :
    ∃ (p : Space K × H) (W : Submodule F (Space K × H)),
        Module.finrank F W+1=Module.finrank F U ∧
        p +ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L) := by
  let q := fun x : K => L (seventhDerivative t x)
  have add (a b : U) : q (a+b)=q 0+q a+q b := by
    have row := (congrArg L (seventhDerivative_rect t 0 a b)).trans (kill a a.property b b.property)
    simp only [zero_add,map_add] at row
    change (q 0+q a+q b)+q (a+b)=0 at row
    calc q (a+b) = (q 0+q a+q b)+((q 0+q a+q b)+q (a+b)) := by rw [←add_assoc,ZModModule.add_self,zero_add]
         _ = _ := by rw [row,add_zero]
  let f : U →ₗ[F] (Space K × H) :=
    { toFun := fun u => (polar t u.val,q u+q 0)
      map_add' := fun u v => Prod.ext (by simp) (by
        change q (u.val+v.val)+q 0=(q u+q 0)+(q v+q 0)
        rw [add u v]
        abel)
      map_smul' := fun r u => by
        rcases (show ∀ i:F,i=0 ∨ i=1 from by decide) r with rfl|rfl <;> simp [ZModModule.add_self] }
  let u : U := ⟨t,ht⟩
  have un : u≠0 := fun eq => nz (congrArg Subtype.val eq)
  have pk : t∈(polar t).ker := (polar_ker nz).symm ▸ Submodule.subset_span (Set.mem_singleton t)
  have ker : f.ker=Submodule.span F {u} := by
    apply le_antisymm
    · intro w hw
      have hw' : (w:K)∈(polar t).ker := congrArg Prod.fst (show f w=0 from hw)
      rw [polar_ker nz,Submodule.mem_span_singleton] at hw'
      obtain ⟨r,hr⟩ := hw'
      exact Submodule.mem_span_singleton.mpr ⟨r,Subtype.ext hr⟩
    · apply Submodule.span_le.mpr
      apply Set.singleton_subset_iff.mpr
      apply (LinearMap.mem_ker).mpr
      apply Prod.ext (show polar t t=0 from pk)
      change q t+q 0=0
      simp [q,seventhDerivative,CharTwo.add_self_eq_zero,ZModModule.add_self]
  have rank := f.finrank_range_add_finrank_ker
  rw [ker,finrank_span_singleton un] at rank
  refine ⟨(curve t,q 0),f.range,rank,?_⟩
  rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
  have eq : (curve t,q 0)+f v=lifted L v.val+lifted L (v.val+t) := by
    apply Prod.ext (derivative v.val t).symm
    change q 0+(q v+q 0)=L (v.val^7)+L ((v.val+t)^7)
    rw [add_left_comm,ZModModule.add_self,add_zero]
    simp [q,seventhDerivative]
  change (curve t,q 0)+f v ∈ Set.range (lifted L)+Set.range (lifted L)
  rw [eq]
  exact Set.add_mem_add (Set.mem_range_self v.val) (Set.mem_range_self (v.val+t))

private theorem from_minor_table [Finite K] {H : Type*} [AddCommGroup H] [Module F H]
    (L : K →ₗ[F] H) (t a b c : K) (z₁ : L (moore t a b)=0) (z₂ : L (moore t a c)=0)
    (z₃ : L (moore t b c)=0) (n₁ : moore t a b ≠ 0) (n₂ : moore t a c ≠ 0)
    (n₃ : moore t b c ≠ 0) (distinct : moore t a b ≠ moore t a c) :
    ∃ (p : Space K × H) (W : Submodule F (Space K × H)),Module.finrank F W=3 ∧
      p +ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L) := by
  have n₄ : moore t a (b+c) ≠ 0 := by rw [moore_right];exact fun eq => distinct (CharTwo.add_eq_zero.mp eq)
  simp only [moore_prod,mul_ne_zero_iff] at n₁ n₂ n₃ n₄
  rcases n₁ with ⟨⟨⟨⟨⟨⟨nt,na⟩,nb⟩,nta⟩,ntb⟩,nab⟩,ntab⟩
  rcases n₂ with ⟨⟨⟨⟨⟨⟨_,_⟩,nc⟩,_⟩,ntc⟩,nac⟩,ntac⟩
  rcases n₃ with ⟨⟨⟨⟨⟨⟨_,_⟩,_⟩,_⟩,_⟩,nbc⟩,ntbc⟩
  rcases n₄ with ⟨⟨_,nabc⟩,ntabc⟩
  let V := ![t,a,b,c]
  let J : Cube 4 →ₗ[F] K := Fintype.linearCombination F V
  have val (u : Cube 4) : J u=u 0 • t+(u 1 • a+(u 2 • b+u 3 • c)) := by
    simp [J,V,Fintype.linearCombination_apply,Fin.sum_univ_four,add_assoc]
  have inj : Function.Injective J := by
    apply (injective_iff_map_eq_zero J).mpr
    intro u eq
    rw [val] at eq
    have bit (r : F) : r=0 ∨ r=1 := (show ∀ z:F,z=0 ∨ z=1 from by decide) r
    rcases bit (u 0) with h0|h0 <;> rcases bit (u 1) with h1|h1 <;>
      rcases bit (u 2) with h2|h2 <;> rcases bit (u 3) with h3|h3 <;>
      simp [h0,h1,h2,h3,nt,na,nb,nc,nta,ntb,ntc,nab,nac,nbc,←add_assoc,ntab,ntac,ntbc] at eq
    all_goals first
      | exact False.elim (nabc (by simpa only [add_assoc] using eq))
      | exact False.elim (ntabc (by simpa only [add_assoc] using eq))
      | funext i;fin_cases i <;> assumption
  let U := J.range
  have rank : Module.finrank F U=4 := by simpa [Cube] using J.finrank_range_of_inj inj
  have ht : t∈U := ⟨Pi.single 0 1,by simp [val]⟩
  let right (x : K) : K →ₗ[F] K :=
    { toFun := moore t x
      map_add' := moore_right t x
      map_smul' := fun r y => by
        rcases (show ∀ z:F,z=0 ∨ z=1 from by decide) r with rfl|rfl <;> simp [moore_prod] }
  have vanish (i j : Fin 4) : L (moore t (V i) (V j))=0 := by
    have eq (x : K) : moore t t x=0 := by simp [moore_prod,CharTwo.add_self_eq_zero]
    have rev (x : K) : moore t x t=0 := (moore_swap ..).trans (eq _)
    fin_cases i <;> fin_cases j <;>
      simp [V,eq,rev,moore_alternating,z₁,z₂,z₃,moore_swap t c a,moore_swap t b a,moore_swap t c b]
  have kill : ∀ u∈U,∀ v∈U,L (moore t u v)=0 := by
    rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩
    have each (i : Fin 4) : L (moore t (V i) (J v))=0 := by
      change L (right (V i) (J v))=0
      simp only [J,Fintype.linearCombination_apply,map_sum,map_smul]
      exact Finset.sum_eq_zero fun j _ => by rw [show L (right (V i) (V j))=0 from vanish i j,smul_zero]
    rw [moore_swap]
    change L (right (J v) (J u))=0
    rw [show J u=∑ i, u i • V i by simp [J,Fintype.linearCombination_apply]]
    simp only [map_sum,map_smul]
    exact Finset.sum_eq_zero fun i _ => by rw [show L (right (J v) (V i))=0 from (congrArg L (moore_swap ..)).trans (each i),smul_zero]
  obtain ⟨p,W,d,sub⟩ := produces_flat L U t ht nt kill
  exact ⟨p,W,by omega,sub⟩

/-- Three discarded dimensions force a flat whenever every codimension-three
linear test meets the nonzero seventh powers. -/
theorem three_iff_of_meeting [Fintype K] {H : Type*} [AddCommGroup H] [Module F H] (L : K →ₗ[F] H)
    (meets : Green51BCHOptimality.MeetsSeventhPowers K) :
    (∃ (p : Space K × H) (W : Submodule F (Space K × H)),Module.finrank F W=3 ∧
      p +ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L)) ↔
    3≤Module.finrank F L.ker := by
  constructor
  · rintro ⟨p,W,rank,sub⟩
    by_contra! small
    have := excludes_three L (by omega) p W sub
    omega
  · intro big
    obtain ⟨j,inj⟩ := finrank_le_iff_exists_linearMap.mp
      (show Module.finrank F (Cube 3) ≤ Module.finrank F L.ker by simpa [Cube] using big)
    let J := L.ker.subtype.comp j
    have ji : Function.Injective J := L.ker.subtype_injective.comp inj
    let e : Fin 3 → Cube 3 := fun i => Pi.single i 1
    have nonzero (u : Cube 3) (nu:u≠0) : J u≠0 := fun eq => nu (ji (eq.trans J.map_zero.symm))
    have sqr : Function.Surjective (fun a : K => a^2) := Finite.surjective_of_injective fun a b h => by
      have z : (a+b)^2=0 := by rw [CharTwo.add_sq,h,CharTwo.add_self_eq_zero]
      exact CharTwo.add_eq_zero.mp ((pow_eq_zero_iff (by decide : 2≠0)).mp z)
    obtain ⟨u,hu⟩ := sqr (J (e 0))
    obtain ⟨v,hv⟩ := sqr (J (e 1))
    obtain ⟨w,hw⟩ := sqr (J (e 2))
    change u^2=J (e 0) at hu
    change v^2=J (e 1) at hv
    change w^2=J (e 2) at hw
    have non : moore u v w≠0 := by
      simp only [moore_prod,mul_ne_zero_iff]
      repeat' apply And.intro
      all_goals intro eq; have z := congrArg (fun x : K => x^2) eq
      all_goals simp only [CharTwo.add_sq,hu,hv,hw,zero_pow (by decide : 2≠0),←map_add] at z
      all_goals exact nonzero _ (by decide +kernel) z
    obtain ⟨t,a,b,c,_,ab,ac,bc⟩ := realize_minors_of_meeting u v w non meets
    apply from_minor_table L t a b c
    · rw [bc,hw];exact (j (e 2)).property
    · rw [ac,hv];exact (j (e 1)).property
    · rw [ab,hu];exact (j (e 0)).property
    · rw [bc,hw];exact nonzero _ (by decide +kernel)
    · rw [ac,hv];exact nonzero _ (by decide +kernel)
    · rw [ab,hu];exact nonzero _ (by decide +kernel)
    · rw [bc,ac,hw,hv];exact fun eq => (by decide +kernel : e 2≠e 1) (ji eq)

/-- For fields of binary dimension at least ten, and for smaller fields
meeting the seventh-power coprimality condition, discarding three binary
coordinates always produces an affine three-space. -/
theorem three_iff [Fintype K] {H : Type*} [AddCommGroup H] [Module F H] (L : K →ₗ[F] H)
    (large : 10 ≤ Module.finrank F K ∨ 4 ≤ Module.finrank F K ∧ (Nat.card Kˣ).Coprime 7) :
    (∃ (p : Space K × H) (W : Submodule F (Space K × H)),Module.finrank F W=3 ∧
      p +ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L)) ↔
    3≤Module.finrank F L.ker :=
  three_iff_of_meeting L (Green51BCHOptimality.meets_of_large large)

end Green51BCHCompression

#print axioms Green51BCHCompression.produces_flat
#print axioms Green51BCHCompression.three_iff_of_meeting
#print axioms Green51BCHCompression.three_iff
