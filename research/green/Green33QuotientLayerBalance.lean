import Green33OddRowSlides
import Green33FourierStability
import Green33TailEnergy
import Green33BaerQuadraticRetention

/-! Fourier inversion for the sizes of arbitrary finite quotient fibres. -/
open Finset
open scoped BigOperators
namespace Green33LayerSlides
variable {G C : Type*} [AddCommGroup G] [AddCommGroup C] [Fintype C] [DecidableEq C]

theorem fiber_inversion (π:G→+C) (T:Finset G) (c:C) :
    ∑ χ : AddChar C ℂ, χ (-c)*∑ a∈T,χ (π a) =
      (Fintype.card C:ℂ)*(layer π T c).card := by
  classical
  simp only [mul_sum,←AddChar.map_add_eq_mul]
  rw [sum_comm]
  simp only [AddChar.sum_apply_eq_ite]
  have pt (a:G) : -c+π a=0 ↔ π a=c := by rw [add_comm,←sub_eq_add_neg,sub_eq_zero]
  simp_rw [pt]
  rw [←sum_filter]
  simp [layer,mul_comm]
#print axioms fiber_inversion

theorem fiber_character_bound (π:G→+C) (T:Finset G) (c:C) (K:ℝ) (hK:0≤K)
    (bound : ∀ χ:AddChar C ℂ,χ≠0 → ‖∑ a∈T,χ (π a)‖≤K) :
    |(Fintype.card C:ℝ)*(layer π T c).card-T.card| ≤ (Fintype.card C:ℝ)*K := by
  classical
  let L:= (univ:Finset (AddChar C ℂ)).erase 0
  let w (χ:AddChar C ℂ):ℂ := χ (-c)*∑ a∈T,χ (π a)
  have eq:=sum_erase_add (univ:Finset (AddChar C ℂ)) w (mem_univ 0)
  have main:∑ χ:AddChar C ℂ,w χ=(Fintype.card C:ℂ)*(layer π T c).card := fiber_inversion π T c
  have zero:w 0=(T.card:ℂ) := by simp [w]
  rw [zero,main] at eq
  change ∑ χ∈L,w χ + _ = _ at eq
  have sm : (Fintype.card C:ℂ)*(layer π T c).card-T.card=∑ χ∈L,w χ := by
    rw [←eq];ring
  have ab : |(Fintype.card C:ℝ)*(layer π T c).card-T.card| = ‖(Fintype.card C:ℂ)*(layer π T c).card-T.card‖ := by
    change ‖((Fintype.card C:ℝ)*(layer π T c).card-T.card:ℝ)‖=_
    rw [←Complex.norm_real]
    push_cast
    rfl
  rw [ab,sm]
  have B:=norm_sum_le L w
  have b:=sum_le_sum (s:=L) fun χ hχ => show ‖w χ‖≤K by
    simpa [w,norm_mul] using bound χ (mem_erase.mp hχ).1
  apply (B.trans b).trans
  rw [sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hK
  exact_mod_cast (card_le_univ L).trans_eq AddChar.card_eq
#print axioms fiber_character_bound

open Filter
open scoped Topology Pointwise
theorem quotient_balance {ι:Type*} {l:Filter ι} (n:ι→ℕ+) (T:∀ i,Finset (ZMod (n i)))
    (π:∀ i,ZMod (n i)→+C) (onto:∀ i,Function.Surjective (π i)) (c:ι→C)
    (grow:Tendsto (fun i => (n i).val) l atTop) (full:∀ i,T i+T i=univ)
    (crit:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => ((layer (π i) (T i) (c i)).card:ℝ)/Real.sqrt (n i)) l
      (𝓝 (Real.sqrt 2/Fintype.card C)) := by
  let d:ℝ:=Fintype.card C
  let N (i:ι):ℝ:=n i
  let k (i:ι):ℝ:=(T i).card
  let b (i:ι):ℝ:=(layer (π i) (T i) (c i)).card
  let K (i:ι):ℝ:=Real.sqrt (k i^2+2*k i-2*N i)
  have pos (i:ι):0<N i:=by dsimp [N];exact_mod_cast (n i).pos
  have dp:0<d:=by dsimp [d];positivity
  have estimate (i:ι) : |d*b i-k i|≤d*K i := by
    apply fiber_character_bound _ _ _ _ (Real.sqrt_nonneg _)
    intro χ hχ
    have nz:χ.compAddMonoidHom (π i)≠0 := by
      intro eq
      apply hχ
      refine AddChar.ext _ _ (fun x => ?_)
      obtain ⟨a,rfl⟩:=(onto i) x
      exact congrArg (fun f:AddChar (ZMod (n i)) ℂ => f a) eq
    have h:=Green33Fourier.character_norm_sq_bound (T i) (full i) _ nz
    rw [ZMod.card] at h
    apply Real.le_sqrt_of_sq_le
    change ‖∑ a∈T i,χ ((π i) a)‖^2+2*N i≤k i^2+2*k i at h
    linarith
  obtain ⟨lin,quad⟩:=Green33TailEnergy.card_limits n (fun i => (T i).card) grow crit
  have raw:Tendsto (fun i => (k i^2+2*k i-2*N i)/N i) l (𝓝 0) := by
    have eq (i:ι):(k i^2+2*k i-2*N i)/N i=k i^2/N i+2*(k i/N i)-2:=by field_simp [(pos i).ne']
    simp_rw [eq]
    simpa using (quad.add (lin.const_mul 2)).sub_const 2
  have small:Tendsto (fun i => K i/Real.sqrt (N i)) l (𝓝 0):=by
    simpa only [Real.sqrt_div' _ (pos _).le,Real.sqrt_zero,K] using raw.sqrt
  have err:Tendsto (fun i => (d*b i-k i)/Real.sqrt (N i)) l (𝓝 0):=by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero,Real.norm_eq_abs,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply squeeze_zero (fun i => by positivity) _ (by simpa using small.const_mul d)
    intro i
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (estimate i) (Real.sqrt_nonneg _)
  have total := (err.add crit).div_const d
  simp only [zero_add] at total
  apply total.congr
  intro i
  change (((d*b i-k i)/Real.sqrt (N i)+k i/Real.sqrt (N i))/d)=b i/Real.sqrt (N i)
  field_simp [dp.ne',(Real.sqrt_pos.mpr (pos i)).ne']
  ring
#print axioms quotient_balance
end Green33LayerSlides

open Finset
open scoped Pointwise
namespace Green33LayerSlides
variable {G:Type*} [AddCommGroup G] [DecidableEq G]

/-- Each collision between sums from two disjoint blocks uses an ambient surplus pair. -/
theorem mixed_pair_budget (T E B:Finset G) (incE:E⊆T) (incB:B⊆T) (sep:Disjoint E B) :
    (T+T).card+E.card*B.card ≤ (T.card+1).choose 2+(E+B).card := by
  classical
  let f (p:G×G) := Sym2.mk p.1 p.2
  let Q := (E×ˢB).image f
  let s : Sym2 G→G := Sym2.lift ⟨(·+·),add_comm⟩
  have bij:Q.card=E.card*B.card := by
    rw [show Q=(E×ˢB).image f from rfl,card_image_of_injOn,card_product]
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd eq
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rfl
    · exact (Finset.disjoint_left.mp sep (mem_product.mp hab).1 (mem_product.mp hcd).2).elim
  have sub:Q⊆T.sym2 := by
    intro p hp
    obtain ⟨⟨a,b⟩,hab,rfl⟩:=mem_image.mp hp
    exact mk_mem_sym2_iff.mpr ⟨incE (mem_product.mp hab).1,incB (mem_product.mp hab).2⟩
  have cover:T+T⊆((T.sym2\Q).image s)∪(E+B) := by
    intro z hz
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hz
    by_cases h:Sym2.mk a b∈Q
    · obtain ⟨⟨c,d⟩,hcd,eq⟩:=mem_image.mp h
      have val:c+d=a+b:=congrArg s eq
      exact mem_union_right _ (val ▸ add_mem_add (mem_product.mp hcd).1 (mem_product.mp hcd).2)
    · exact mem_union_left _ (mem_image.mpr ⟨Sym2.mk a b,mem_sdiff.mpr ⟨mk_mem_sym2_iff.mpr ⟨ha,hb⟩,h⟩,rfl⟩)
  have count:=((card_le_card cover).trans (card_union_le _ _)).trans (Nat.add_le_add_right card_image_le _)
  have sz:=card_sdiff_add_card_eq_card sub
  rw [card_sym2,bij] at sz
  omega
#print axioms mixed_pair_budget

open Filter
open scoped Topology
variable {ι:Type*} {l:Filter ι}

/-- The normalized unordered-pair budget is determined by the square-root scale. -/
theorem choose_limit (n:ι→ℕ+) (k:ι→ℕ) {x:ℝ} (grow:Tendsto (fun i => (n i).val) l atTop)
    (size:Tendsto (fun i => (k i:ℝ)/Real.sqrt (n i)) l (𝓝 x)) :
    Tendsto (fun i => (((k i+1).choose 2:ℕ):ℝ)/(n i:ℝ)) l (𝓝 (x^2/2)) := by
  have hs:=Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow)
  have sq (i:ι):Real.sqrt (n i)^2=(n i:ℝ):=Real.sq_sqrt (by positivity)
  have lin:=size.div_atTop hs
  simp only [Function.comp_apply,div_div,Real.mul_self_sqrt (show (0:ℝ)≤(_ : ℕ+) by positivity)] at lin
  have quad:=size.pow 2
  simp only [div_pow,sq] at quad
  have hh:=(quad.add lin).div_const 2
  simp only [add_zero] at hh
  apply hh.congr
  intro i
  rw [Nat.cast_choose_two,Nat.cast_add_one]
  ring

/-- Sum supports of a retained block, and of two disjoint retained blocks,
asymptotically attain their respective unordered-pair budgets. -/
theorem support_limits (n:ι→ℕ+) (T E B:∀ i,Finset (ZMod (n i))) {x y:ℝ}
    (grow:Tendsto (fun i => (n i).val) l atTop) (full:∀ i,T i+T i=univ)
    (critical:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2)))
    (incE:∀ i,E i⊆T i) (incB:∀ i,B i⊆T i) (sep:∀ i,Disjoint (E i) (B i))
    (left:Tendsto (fun i => ((E i).card:ℝ)/Real.sqrt (n i)) l (𝓝 x))
    (right:Tendsto (fun i => ((B i).card:ℝ)/Real.sqrt (n i)) l (𝓝 y)) :
    Tendsto (fun i => ((E i+E i).card:ℝ)/(n i:ℝ)) l (𝓝 (x^2/2)) ∧
    Tendsto (fun i => ((E i+B i).card:ℝ)/(n i:ℝ)) l (𝓝 (x*y)) := by
  have pos (i:ι):(0:ℝ)<(n i:ℝ):=by exact_mod_cast (n i).pos
  have amb:=choose_limit n _ grow critical
  norm_num at amb
  have ex:=amb.sub_const 1
  simp only [sub_self] at ex
  have ee:=choose_limit n _ grow left
  have eb:=left.mul right
  simp only [div_mul_div_comm,Real.mul_self_sqrt (pos _).le] at eb
  constructor
  · have lo:=ee.sub ex
    simp only [sub_zero] at lo
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le lo ee
    · intro i
      have b:=Green33BaerQuadratic.retained_pair_budget (T i) (E i) (incE i)
      rw [full,card_univ,ZMod.card] at b
      have r:(n i:ℝ)+(((E i).card+1).choose 2:ℕ)≤(((T i).card+1).choose 2:ℕ)+((E i+E i).card:ℝ):=by exact_mod_cast b
      dsimp only
      field_simp [(pos i).ne']; linarith
    · intro i
      apply div_le_div_of_nonneg_right _ (pos i).le
      have cap:=Green33BaerQuadratic.retained_pair_budget (E i) ∅ (empty_subset _)
      exact_mod_cast (by simpa using cap : (E i+E i).card≤((E i).card+1).choose 2)
  · have lo:=eb.sub ex
    simp only [sub_zero] at lo
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le lo eb
    · intro i
      have b:=mixed_pair_budget (T i) (E i) (B i) (incE i) (incB i) (sep i)
      rw [full,card_univ,ZMod.card] at b
      have r:(n i:ℝ)+((E i).card:ℝ)*(B i).card≤(((T i).card+1).choose 2:ℕ)+((E i+B i).card:ℝ):=by exact_mod_cast b
      dsimp only
      field_simp [(pos i).ne']; linarith
    · intro i
      apply div_le_div_of_nonneg_right _ (pos i).le
      exact_mod_cast (card_add_le (s:=E i) (t:=B i))
#print axioms choose_limit
#print axioms support_limits
end Green33LayerSlides
