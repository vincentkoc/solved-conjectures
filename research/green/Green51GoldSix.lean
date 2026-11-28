import Green51GoldCoefficient
import Green51GoldSmall

/-! # Exact count of scalar BCH projections admitting a four-flat in dimension six -/

open Green51BCHCompression Green51BCHOptimality Green51GoldForms
open scoped Pointwise
namespace Green51GoldSix
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

/-- The nonzero vectors of a nonzero polar radical satisfy a cubic equation. -/
theorem root_criterion (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    {b r : K} (nb : b≠0) (nr : r≠0) : r∈(bracketForm Q b).ker ↔ b*r^3=1 := by
  rw [radical Q nq sq]
  rw [show b^2*r^4+b*r=(b*r)*(b*r^3+1) from by ring,mul_eq_zero]
  simp only [mul_ne_zero nb nr,false_or,CharTwo.add_eq_zero]

private theorem radical_line (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    {b r : K} (nb : b≠0) (nr : r≠0) (br : b*r^3=1) (a:K) :
    a*r∈(bracketForm Q b).ker ↔ a^4=a := by
  rw [radical Q nq sq]
  have f : b^2*(a*r)^4+b*(a*r)=(b*r)*(a^4+a) := calc
    _=(b*r)*((b*r^3)*a^4+a) := by ring
    _=_ := by rw [br,one_mul]
  rw [f,mul_eq_zero]
  simp only [mul_ne_zero nb nr,false_or,CharTwo.add_eq_zero]

open Green51BCH in
/-- An explicit polynomial in the trace coefficient detects every four-flat in dimension six. -/
theorem four_flat_iff (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ x,Q x=0 ↔ x∈(artinSchreier (K:=K)).range)
    {c:K} (nc : c≠0) (l:K →ₗ[F] F) (rep : ∀ z,l z=Q (c*z)) (size : Module.finrank F K=6) :
    (∃ (p : Space K × F) (W : Submodule F (Space K × F)), 4 ≤ Module.finrank F W ∧
      p+ᵥ (W:Set _) ⊆ Set.range (lifted l)+Set.range (lifted l)) ↔ c^9=1 ∨ (c^9)^3+c^9+1=0 := by
  rw [four_in_six_iff Q nq sq c nc l rep size,←coefficient_test size nc]
  constructor
  · rintro ⟨t,nt,dim,sub⟩
    let b := c*t^7
    have nb : b≠0 := mul_ne_zero nc (pow_ne_zero _ nt)
    have ne : (bracketForm Q b).ker≠⊥ := by
      intro h
      have zero : Module.finrank F (bracketForm Q b).ker=0 := by rw [h,finrank_bot]
      change Module.finrank F (bracketForm Q b).ker=2 at dim
      omega
    obtain ⟨r,hr,nr⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ne
    have br := (root_criterion Q nq sq nb nr).mp hr
    have tr := (line_in_trace Q nq sq size r).mp (fun a ha =>
      (test _).mpr (sub ((radical_line Q nq sq nb nr br a).mpr ha)))
    have t63 := pow_sixty_three size nt
    have eq : (c*r^3)^9*t^63=(b*r^3)^9 := by dsimp only [b];ring
    rw [br,one_pow,t63,mul_one] at eq
    exact ⟨r,nr,tr,eq⟩
  · rintro ⟨r,nr,trace,good⟩
    let t := (c*r^3)^5
    let b := c*t^7
    have nt : t≠0 := pow_ne_zero _ (mul_ne_zero nc (pow_ne_zero _ nr))
    have nb : b≠0 := mul_ne_zero nc (pow_ne_zero _ nt)
    have br : b*r^3=1 := by rw [show b*r^3=((c*r^3)^9)^4 from by dsimp only [b,t];ring,good,one_pow]
    have line := radical_line Q nq sq nb nr br
    refine ⟨t,nt,?_,?_⟩
    · let E := GaloisField 2 2
      let _ : Fintype E := Fintype.ofFinite E
      have dim : Module.finrank F E=2 := GaloisField.finrank 2 (by decide)
      obtain ⟨j⟩ := (FiniteField.nonempty_algHom_of_finrank_dvd
        (show Module.finrank F E∣Module.finrank F K by rw [dim,size];decide) : Nonempty (E →ₐ[F] K))
      have card : Fintype.card E=4 := by rw [←Nat.card_eq_fintype_card];exact GaloisField.card 2 2 (by decide)
      let f := (LinearMap.mulLeft F r).comp j.toLinearMap
      have inj : Function.Injective f := fun _ _ h => j.injective (mul_left_cancel₀ nr h)
      have sub : f.range≤(bracketForm Q b).ker := by
        rintro _ ⟨x,rfl⟩
        change r*j x ∈ _
        rw [mul_comm]
        apply (line _).mpr
        rw [←map_pow,←card,FiniteField.pow_card]
      have two : Module.finrank F f.range=2 := (f.finrank_range_of_inj inj).trans dim
      have lo := Submodule.finrank_mono sub
      rw [two] at lo
      exact le_antisymm (radical_bound Q nq sq nb) lo
    · intro x hx
      have hz : (x/r)*r=x := div_mul_cancel₀ _ nr
      have inRad : (x/r)*r∈(bracketForm Q b).ker := by rw [hz];exact hx
      have a := (line (x/r)).mp inRad
      have z := (line_in_trace Q nq sq size r).mpr trace (x/r) a
      rw [hz] at z
      exact (test _).mp z


open Green51BCH in
def HasFour (l : K →ₗ[F] F) : Prop :=
  ∃ (p : Space K × F) (W : Submodule F (Space K × F)), 4 ≤ Module.finrank F W ∧
    p+ᵥ (W:Set _) ⊆ Set.range (lifted l)+Set.range (lifted l)

open Finset in
/-- Of the 63 nonzero scalar projections, 36 give a four-flat and 27 exclude every four-flat. -/
theorem scalar_counts (size : Module.finrank F K=6) :
    Nat.card {l : K →ₗ[F] F // l≠0 ∧ HasFour l}=36 ∧
    Nat.card {l : K →ₗ[F] F // l≠0 ∧ ¬ HasFour l}=27 := by
  classical
  obtain ⟨Q,nq,sq,test⟩ := trace_functional (K:=K)
  let T := (Algebra.lmul F K).toLinearMap.compr₂ Q
  have sur : Function.Surjective T := by
    intro l
    obtain ⟨c,eq⟩ := represent Q nq l
    exact ⟨c,LinearMap.ext (fun x => (eq x).symm)⟩
  have dim : Module.finrank F K=Module.finrank F (K →ₗ[F] F) := by simp
  let e := LinearEquiv.ofBijective T ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mpr sur,sur⟩
  let good (c:K) := c^9=1 ∨ (c^9)^3+c^9+1=0
  have nz : ¬good 0 := by simp [good]
  have ne (c:K) : e c≠0 ↔ c≠0 := by simp
  have criterion (c:K) (nc:c≠0) : HasFour (e c) ↔ good c :=
    four_flat_iff Q nq sq test nc (e c) (fun _ => rfl) size
  have a (c:K) : good c ↔ e c≠0 ∧ HasFour (e c) := by
    by_cases h : c=0
    · simp [h,nz,good]
    · exact ⟨fun g => ⟨(ne c).mpr h,(criterion c h).mpr g⟩,fun g => (criterion c h).mp g.2⟩
  have b (c:K) : (c≠0 ∧ ¬good c) ↔ e c≠0 ∧ ¬HasFour (e c) := by
    by_cases h : c=0
    · simp [h]
    · exact ⟨fun g => ⟨(ne c).mpr h,fun z => g.2 ((criterion c h).mp z)⟩,
        fun g => ⟨h,fun z => g.2 ((criterion c h).mpr z)⟩⟩
  have ca := Nat.card_congr (e.toEquiv.subtypeEquiv (p:=good) (q:=fun l => l≠0 ∧ HasFour l) a)
  have cb := Nat.card_congr (e.toEquiv.subtypeEquiv (p:=fun c => c≠0 ∧ ¬good c) (q:=fun l => l≠0 ∧ ¬ HasFour l) b)
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at ca cb
  have cardgood : (univ.filter good).card=36 := count_coefficients size
  have same : (univ.erase (0:K)).filter good=univ.filter good := by
    ext c
    by_cases h:c=0 <;> simp [h,nz]
  have rest : (univ.erase (0:K)).filter (fun c => ¬good c)=univ.filter (fun c => c≠0 ∧ ¬good c) := by
    ext c;simp
  have split := card_filter_add_card_filter_not (s:=univ.erase (0:K)) (p:=good)
  rw [same,rest,card_erase_of_mem (mem_univ _),card_univ,Module.card_eq_pow_finrank (K:=F),
    ZMod.card,size,cardgood] at split
  change (univ.filter good).card=_ at ca
  exact ⟨ca.symm.trans cardgood,by omega⟩

open Green51BCH Green51LocalFlats in
/-- The coefficient test computes the greatest affine dimension in the original doubled set. -/
theorem maximum_at_six (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ x,Q x=0 ↔ x∈(artinSchreier (K:=K)).range)
    {c:K} (nc : c≠0) (l:K →ₗ[F] F) (rep : ∀ z,l z=Q (c*z)) (size : Module.finrank F K=6)
    [DecidableEq K] :
    maxCosetDim F (Space K × F) (Set.range (lifted l)+Set.range (lifted l)) =
      if c^9=1 ∨ (c^9)^3+c^9+1=0 then 4 else 3 := by
  have nl : l≠0 := by
    intro h
    apply nq
    ext y
    have eq := rep (c⁻¹*y)
    simpa [h,←mul_assoc,nc] using eq.symm
  let A := Set.range (lifted l)+Set.range (lifted l)
  let d := maxCosetDim F (Space K × F) A
  have hi : d≤4 := by
    by_contra! large
    obtain ⟨W,p,dim,sub⟩ := (le_iff_coset (by decide : 0<5) A).mp large
    have h := half_bound l nl p W sub (by omega)
    omega
  have lo : 3≤d := by
    obtain ⟨p,W,dim,sub⟩ := scalar_lower l
    have rank : 0<Module.finrank F W := by omega
    have bound := (le_iff_coset rank A).mpr ⟨W,p,rfl,sub⟩
    change Module.finrank F W≤d at bound
    omega
  have f : 4≤d ↔ HasFour l := by
    constructor
    · intro ok
      obtain ⟨W,p,rank,sub⟩ := (le_iff_coset (by decide : 0<4) A).mp ok
      exact ⟨p,W,rank.ge,sub⟩
    · rintro ⟨p,W,rank,sub⟩
      exact rank.trans ((le_iff_coset (by omega : 0<Module.finrank F W) A).mpr ⟨W,p,rfl,sub⟩)
  have check : HasFour l ↔ c^9=1 ∨ (c^9)^3+c^9+1=0 := four_flat_iff Q nq sq test nc l rep size
  change d=_
  split_ifs with good
  · have ok := f.mpr (check.mpr good);omega
  · have no : ¬4≤d := fun h => good (check.mp (f.mp h));omega

open Green50Downsets Green51BCH Green51SparseBounds Green51LocalFlats Finset in
/-- Choosing one of the 27 projections without a four-flat puts 64 labels
in 19 coordinates with no affine four-space in their double. -/
theorem nineteen {α : ℝ} (density : α ≤ 64/(2:ℝ)^19) :
    Green51.guaranteedMaxCosetDim 19 α≤3 := by
  classical
  let E := GaloisField 2 6
  let _ : Fintype E := Fintype.ofFinite E
  have sz : Module.finrank F E=6 := GaloisField.finrank 2 (by decide)
  have count := (scalar_counts sz).2
  have pos : 0<Nat.card {l:E →ₗ[F] F // l≠0 ∧ ¬HasFour l} := by omega
  obtain ⟨⟨l,_,free⟩⟩ := Nat.card_pos_iff.mp pos |>.1
  let j : (Space E × F) ≃ₗ[F] Cube 19 := LinearEquiv.ofFinrankEq _ _ (by simp [Space,Cube,sz])
  obtain ⟨A,card,bound⟩ := transport_dimension (d:=3) l j (fun p W sub => by
    by_contra! big;exact free ⟨p,W,big,sub⟩)
  have cardE : Fintype.card E=64 := by rw [←Nat.card_eq_fintype_card];exact GaloisField.card 2 6 (by decide)
  have adm : α≤(A.dens:ℝ) := by
    rw [Finset.nnratCast_dens,card,cardE]
    norm_num [Cube] at density ⊢
    exact density
  have upper : Green51.guaranteedMaxCosetDim 19 α ≤ maxCosetDim F (𝔽₂ 19) ↑(A+A) :=
    csInf_le (OrderBot.bddBelow _) ⟨A,adm,rfl⟩
  apply upper.trans
  by_contra! hi
  obtain ⟨W,p,rank,sub⟩ := (le_iff_coset (by decide : 0<4) _).mp hi
  exact (by decide : ¬(4:ℕ)≤3) (rank.symm.trans_le (bound W p sub))

end Green51GoldSix
#print axioms Green51GoldSix.root_criterion
#print axioms Green51GoldSix.nineteen
#print axioms Green51GoldSix.maximum_at_six
#print axioms Green51GoldSix.four_flat_iff
#print axioms Green51GoldSix.scalar_counts
