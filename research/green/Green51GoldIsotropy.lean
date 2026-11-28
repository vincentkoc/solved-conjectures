import Green51GoldForms
import Green50QuadraticDescent

/-! # Flat construction from isotropic spaces in the absolute trace hyperplane -/

open Green51BCH Green51BCHCompression Green51BCHOptimality Finset
open scoped Pointwise
namespace Green51GoldForms
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

private theorem scaled_radical {E : Type*} [Field E] [Algebra F E] [Fintype E]
    (j : E →ₐ[F] K) (fourth : ∀ a:E,a^4=a) (small : Module.finrank F E≤3)
    (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ x,Q x=0 ↔ x∈(artinSchreier (K:=K)).range)
    {c : K} (nc : c≠0) (meets : MeetsSeventhPowers K) :
    ∃ t : K, t≠0 ∧ ∃ R : Submodule F K, Module.finrank F R=Module.finrank F E ∧
      R≤(artinSchreier (K:=K)).range ∧ R≤(bracketForm Q (c*t^7)).ker := by
  let P := (((Algebra.lmul F K).toLinearMap.compl₂ j.toLinearMap).compr₂ Q).comp (LinearMap.mulLeft F (c^2))
  obtain ⟨e,ie⟩ := finrank_le_iff_exists_linearMap.mp
    (show Module.finrank F (E →ₗ[F] F)≤Module.finrank F (Green50Downsets.Cube 3) by
      simpa [Green50Downsets.Cube,Module.finrank_linearMap] using small)
  obtain ⟨s,ns,zero⟩ := meets (e.comp P)
  have z : P (s^7)=0 := (e.map_eq_zero_iff ie).mp zero
  let r := c^2*s^7
  let t := (c*s^3)⁻¹
  let f := (LinearMap.mulLeft F r).comp j.toLinearMap
  have nr : r≠0 := mul_ne_zero (pow_ne_zero _ nc) (pow_ne_zero _ ns)
  have inj : Function.Injective f := fun _ _ h => j.injective (mul_left_cancel₀ nr h)
  refine ⟨t,inv_ne_zero (mul_ne_zero nc (pow_ne_zero _ ns)),f.range,f.finrank_range_of_inj inj,?_,?_⟩
  · rintro _ ⟨a,rfl⟩
    exact (test _).mp (LinearMap.congr_fun z a)
  · rintro _ ⟨a,rfl⟩
    apply (radical Q nq sq _ _).mpr
    have h4 : (j a)^4=j a := by rw [←map_pow,fourth]
    change (c*t^7)^2*(r*j a)^4+c*t^7*(r*j a)=0
    rw [mul_pow r (j a) 4,h4]
    apply CharTwo.add_eq_zero.mpr
    dsimp only [t,r]
    field_simp

private theorem isotope_in_trace (Q : K →ₗ[F] F) (c : K) (R : Submodule F K)
    (sub : R≤(artinSchreier (K:=K)).range) (rad : R≤(bracketForm Q c).ker) :
    ∃ A : Submodule F K, A≤(artinSchreier (K:=K)).range ∧
      (∀ x∈A,∀ y∈A,Q (c*bracket x y)=0) ∧
      Module.finrank F K+Module.finrank F R≤2*Module.finrank F A+1 := by
  classical
  let B := bracketForm Q c
  let T := (artinSchreier (K:=K)).range
  let _ := Fintype.ofFinite T
  have sz := (artinSchreier (K:=K)).finrank_range_add_finrank_ker
  rw [artinSchreier_ker,finrank_span_singleton one_ne_zero] at sz
  change Module.finrank F T+1=Module.finrank F K at sz
  have alt : (B.restrict T).IsAlt := fun a => by change Q (c*bracket (a:K) (a:K))=0;simp [bracket,CharTwo.add_self_eq_zero]
  obtain ⟨A,iso,dim⟩ := Green50QuadraticDescent.isotropic_half_rank (B.restrict T) alt
  let S := A.map T.subtype
  have sr : Module.finrank F S=Module.finrank F A := T.finrank_map_subtype_eq A
  let embed := R.subtype.codRestrict T (fun a => sub a.property)
  have ei : Function.Injective embed := fun _ _ h => Subtype.ext (congrArg (fun x:T => (x:K)) h)
  have er := embed.finrank_range_of_inj ei
  have le : embed.range≤(B.restrict T).ker := by
    rintro _ ⟨a,rfl⟩
    apply LinearMap.ext
    intro b
    exact LinearMap.congr_fun (show B a.val=0 from rad a.property) b.val
  have rk := (B.restrict T).finrank_range_add_finrank_ker
  have ek := Submodule.finrank_mono le
  have ar := Submodule.finrank_le A
  refine ⟨S,?_,?_,by omega⟩
  · rintro _ ⟨a,_,rfl⟩;exact a.property
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    exact iso a ha b hb

private theorem flat_from_isotropic (l Q : K →ₗ[F] F) (c t : K) (nt : t≠0)
    (rep : ∀ z,l z=Q (c*z)) (A : Submodule F K) (inTrace : A≤(artinSchreier (K:=K)).range)
    (iso : ∀ x∈A,∀ y∈A,Q ((c*t^7)*bracket x y)=0) :
    ∃ (p : Space K × F) (W : Submodule F (Space K × F)), Module.finrank F W=Module.finrank F A ∧
      p+ᵥ (W:Set _) ⊆ Set.range (lifted l)+Set.range (lifted l) := by
  apply Green51BracketRank.flat_of_trace_space l t nt A inTrace
  intro x hx y hy
  rw [rep,←mul_assoc]
  exact iso x hx y hy

/-- Seventh powers meeting every three binary linear tests align a polar radical with the trace hyperplane. -/
theorem maximal_of_meeting (l : K →ₗ[F] F) (nl : l≠0) (meets : MeetsSeventhPowers K) :
    ∃ (p : Space K × F) (W : Submodule F (Space K × F)), Module.finrank F K/2+1≤Module.finrank F W ∧
      p+ᵥ (W:Set _) ⊆ Set.range (lifted l)+Set.range (lifted l) := by
  obtain ⟨Q,nq,sq,test⟩ := trace_functional (K:=K)
  obtain ⟨c,rep⟩ := represent Q nq l
  have nc : c≠0 := by intro h;apply nl;ext x;simp [rep x,h]
  let m := Module.finrank F K
  let d := if 2∣m then 2 else 1
  have pos : 0<d := by dsimp [d];split <;> decide
  let E := GaloisField 2 d
  let _ := Fintype.ofFinite E
  have sz : Module.finrank F E=d := GaloisField.finrank 2 (by omega)
  have dv : d∣m := by dsimp [d];split <;> simp_all
  have emb : Nonempty (E →ₐ[F] K) := FiniteField.nonempty_algHom_of_finrank_dvd (by rw [sz];exact dv)
  obtain ⟨j⟩ := emb
  have card : Fintype.card E=2^d := by rw [←Nat.card_eq_fintype_card];exact GaloisField.card 2 d (by omega)
  have fourth (a:E) : a^4=a := by
    have z := FiniteField.pow_card a
    rw [card] at z
    by_cases h : 2∣m
    · simpa [d,h] using z
    · have z2 : a^2=a := by simpa [d,h] using z
      rw [show (4:ℕ)=2*2 from rfl,pow_mul,z2,z2]
  obtain ⟨t,nt,R,rr,sub,rad⟩ := scaled_radical j fourth (by rw [sz];dsimp [d];split <;> decide)
    Q nq sq test nc meets
  obtain ⟨A,trace,iso,dim⟩ := isotope_in_trace Q (c*t^7) R sub rad
  obtain ⟨p,W,wr,inside⟩ := flat_from_isotropic l Q c t nt rep A trace iso
  refine ⟨p,W,?_,inside⟩
  rw [rr,sz] at dim
  change m+d≤2*Module.finrank F A+1 at dim
  change m/2+1≤Module.finrank F W
  dsimp only [d] at dim
  split at dim <;> omega

/-- In dimension six an affine four-space occurs exactly when the absolute
trace hyperplane contains a full two-dimensional polar radical at some shift. -/
theorem four_in_six_iff (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (c : K) (nc : c≠0) (l : K →ₗ[F] F) (rep : ∀ z,l z=Q (c*z))
    (size : Module.finrank F K=6) :
    (∃ (p : Space K × F) (W : Submodule F (Space K × F)), 4≤Module.finrank F W ∧
        p+ᵥ (W:Set _) ⊆ Set.range (lifted l)+Set.range (lifted l)) ↔
    ∃ t : K, t≠0 ∧ Module.finrank F (bracketForm Q (c*t^7)).ker=2 ∧
        (bracketForm Q (c*t^7)).ker≤(artinSchreier (K:=K)).range := by
  constructor
  · rintro ⟨p,W,large,inside⟩
    obtain ⟨t,nt,A,dim,sub,zero⟩ := Green51BracketRank.trace_space_of_flat l p W inside (by omega)
    let B := bracketForm Q (c*t^7)
    have rb : Module.finrank F B.ker≤2 := radical_bound Q nq sq (mul_ne_zero nc (pow_ne_zero _ nt))
    have iso : A≤B.orthogonal A := by
      intro y hy x hx
      have eq := zero x hx y hy
      rw [rep,←mul_assoc] at eq
      exact eq
    have le := Submodule.finrank_mono iso
    have sz := B.finrank_add_finrank_orthogonal' A
    have rk := Submodule.finrank_mono (show A ⊓ B.ker ≤ B.ker from inf_le_right)
    have eq : A ⊓ B.ker=B.ker := Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
    refine ⟨t,nt,?_,?_⟩
    · change Module.finrank F B.ker=2
      omega
    · exact (eq ▸ (show A ⊓ B.ker ≤ A from inf_le_left)).trans sub
  · rintro ⟨t,nt,dim,sub⟩
    let B := bracketForm Q (c*t^7)
    obtain ⟨A,trace,iso,rank⟩ := isotope_in_trace Q (c*t^7) B.ker sub le_rfl
    obtain ⟨p,W,wr,inside⟩ := flat_from_isotropic l Q c t nt rep A trace iso
    change Module.finrank F B.ker=2 at dim
    exact ⟨p,W,by omega,inside⟩

/-- With an arbitrary scalar projection the trace hyperplane always supplies
a flat of dimension at least floor(m/2), including in dimension six. -/
theorem scalar_lower (l : K →ₗ[F] F) :
    ∃ (p : Space K × F) (W : Submodule F (Space K × F)), Module.finrank F K/2 ≤ Module.finrank F W ∧
      p+ᵥ (W:Set _) ⊆ Set.range (lifted l)+Set.range (lifted l) := by
  obtain ⟨Q,nq,_,_⟩ := trace_functional (K:=K)
  obtain ⟨c,rep⟩ := represent Q nq l
  obtain ⟨A,trace,iso,dim⟩ := isotope_in_trace Q (c*1^7) ⊥ bot_le bot_le
  obtain ⟨p,W,wr,inside⟩ := flat_from_isotropic l Q c 1 one_ne_zero rep A trace iso
  exact ⟨p,W,by omega,inside⟩

end Green51GoldForms
#print axioms Green51GoldForms.scalar_lower
#print axioms Green51GoldForms.maximal_of_meeting
#print axioms Green51GoldForms.four_in_six_iff
