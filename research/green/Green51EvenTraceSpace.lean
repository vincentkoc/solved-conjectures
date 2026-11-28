import Green51PencilChains
import Green51PencilCoefficients
import Green51GoldPencils
import Green51TraceScaling

/-! # The forced quartic multiples for an even-degree trace pencil -/

namespace Green51EvenChains
open Green51GoldForms Green51BCHCompression
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
theorem normalized_radical (Q : K →ₗ[F] F) (nQ : Q≠0) (sq : ∀ x,Q (x^2)=Q x)
    {k : ℕ} (dim : Module.finrank F K=2*k) : Module.finrank F (bracketForm Q 1).ker=2 := by
  classical
  have three : 3∣Fintype.card Kˣ := by
    rw [Fintype.card_units,Module.card_eq_pow_finrank (K:=F),ZMod.card,dim,pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨w,hw⟩ := exists_prime_orderOf_dvd_card (G:=Kˣ) 3 three
  have cube : (w:K)^3=1 := congrArg (fun u:Kˣ => (u:K)) (hw ▸ pow_orderOf_eq_one w : w^3=1)
  have nw : (w:K)≠1 := by intro eq;have one : w=1 := Units.ext eq;simp [one] at hw
  let R := (bracketForm Q 1).ker
  let e : R := ⟨1,(radical_cube_iff Q nQ sq one_ne_zero one_ne_zero).mpr (by simp)⟩
  let f : R := ⟨w,(radical_cube_iff Q nQ sq one_ne_zero w.ne_zero).mpr (by simpa using cube)⟩
  have nf : f≠0 := fun eq => w.ne_zero (congrArg Subtype.val eq)
  have ne : e≠0 := fun eq => one_ne_zero (congrArg Subtype.val eq)
  have ef : e≠f := fun eq => nw (congrArg Subtype.val eq.symm)
  let _ := Fintype.ofFinite R
  have cnt := Finset.card_le_univ ({0,e,f} : Finset R)
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm ne,Ne.symm nf]),Finset.card_insert_of_notMem (by simp [ef]),
      Finset.card_singleton,Module.card_eq_pow_finrank (K:=F),ZMod.card] at cnt
  have bound := radical_bound Q nQ sq (one_ne_zero : (1:K)≠0)
  change Module.finrank F R≤2 at bound
  change Module.finrank F R=2
  by_contra h
  have low : Module.finrank F R≤1 := by omega
  have := Nat.pow_le_pow_right (by decide : 0<2) low
  omega

open Green51BCH Green51BCHOptimality Green51LocalFlats
open scoped Pointwise

theorem scaled_flat_iff (Q : K →ₗ[F] F) (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z)
    (nQ : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    {k : ℕ} (degree : Module.finrank F K=2*k) {d : ℕ} (hd : 3≤d) (full : k+1≤d)
    {a : K} (na : a ≠ 0) (b : K) :
    let L := twoTraces Q a (a*b)
    d ≤ maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L)) ↔
    ∃ U : Submodule F K, Module.finrank F U=d ∧
      (∀ x∈U,∀ y∈U,Q (bracket x y)=0 ∧ Q (b*bracket x y)=0) ∧
      ∃ h : K, h≠0 ∧ ∀ x∈U,Q ((a^2*h^7)*x)=0 := by
  apply Green51TraceScaling.scaled_flat_iff_of_cube Q test hd na b
  intro t nt A dim iso
  have nc := mul_ne_zero na (pow_ne_zero 7 nt)
  have rank := (Green51TwoGold.saturated_radical Q nQ sq nc A (by omega) iso).1
  obtain ⟨r,mem,nr⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (show (bracketForm Q (a*t^7)).ker ≠ ⊥ by intro zero; rw [zero,finrank_bot] at rank; omega)
  have eq := (radical_cube_iff Q nQ sq nc nr).mp mem
  exact ⟨r⁻¹,by field_simp;linear_combination -eq⟩
end Green51EvenChains

namespace Green51EvenChains
open Green51GoldForms Green51PencilWindows Green51BCHCompression Green51PencilChains
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
abbrev Quartic (K : Type*) [Field K] := {x : K // x^4=x}

noncomputable def entry (l : ℕ) (b : K) (w : Quartic K) (j : ℕ) : K :=
  w.val * term l b j
noncomputable def space (l : ℕ) (b : K) : Submodule F K := chainSpace l (entry l b)

theorem chain_relations (Q : K →ₗ[F] F) (sq : ∀ x,Q (x^2)=Q x) (l : ℕ) (b : K)
    (period : orbit b l=b) :
    let A := bracketForm Q 1
    let B := bracketForm Q b
    let c := entry l b
    (∀ w y,A (c w 0) y=0) ∧ (∀ w i,i<l → ∀ y,A (c w (i+1)) y=B (c w i) y) ∧
      (∀ w y,B (c w l) y=0) := by
  intro A B c
  have first (w : Quartic K) (j : ℕ) (y : K) :
      A (c w j) y = Q ((w.val*((term l b j)^4 + term l b j))*y^2) := by
    dsimp only [A,c,entry]
    rw [bracketForm_apply_squared Q sq,mul_pow,w.property,one_pow,one_mul,one_mul,mul_add]
  have second (w : Quartic K) (j : ℕ) (y : K) :
      B (c w j) y = Q ((w.val*(b^2*(term l b j)^4+b*term l b j))*y^2) := by
    dsimp only [B,c,entry]
    rw [bracketForm_apply_squared Q sq,mul_pow,w.property]
    congr 1; ring
  exact ⟨fun w y => by rw [first,term_zero];simp [CharTwo.add_self_eq_zero],
    fun w i hi y => by rw [first,second,Green51PencilWindows.term_step_of_period b period i hi],
    fun w y => by rw [second,Green51PencilWindows.term_end_of_period b period];simp⟩

theorem in_hyperplane_iff (Q : K →ₗ[F] F) (nQ : Q≠0) (sq : ∀ x,Q (x^2)=Q x)
    {k : ℕ} (degree : Module.finrank F K=2*k) (l : ℕ) (b : K) (period : orbit b l=b)
    (f : K →ₗ[F] F) :
    (∃ U : Submodule F K, Module.finrank F U=k+1 ∧ U≤f.ker ∧
      ∀ x∈U,∀ y∈U,Q (bracket x y)=0 ∧ Q (b*bracket x y)=0) ↔ space l b≤f.ker := by
  let A := bracketForm Q 1
  let B := bracketForm Q b
  let D := space l b
  have sym (v x y : K) : bracketForm Q v x y=bracketForm Q v y x := by
    change Q (v*bracket x y)=Q (v*bracket y x)
    congr 2;unfold bracket;ring
  have alt (v : K) : (bracketForm Q v).IsAlt := fun x => by
    change Q (v*bracket x x)=0
    simp [bracket,CharTwo.add_self_eq_zero]
  obtain ⟨start,step,last⟩ := chain_relations Q sq l b period
  have rad : A.ker≤D := by
    intro x hx
    have eq := (radical Q nQ sq 1 x).mp hx
    simp only [one_pow,one_mul] at eq
    have gen := @generators F K _ _ _ _ l (entry l b) (⟨x,CharTwo.add_eq_zero.mp eq⟩ : Quartic K) 0 (by omega)
    simpa only [entry,term_zero,mul_one,D,space] using gen
  have rankR : Module.finrank F A.ker=2 := normalized_radical Q nQ sq degree
  constructor
  · rintro ⟨U,size,ker,iso⟩
    have ua : U≤A.orthogonal U := fun y hy x hx => by
      change Q (1*bracket x y)=0;simpa using (iso x hx y hy).1
    have ub : U≤B.orthogonal U := fun y hy x hx => (iso x hx y hy).2
    have orth := A.finrank_add_finrank_orthogonal' U
    have low := Submodule.finrank_mono (show U⊓A.ker≤A.ker from inf_le_right)
    have eq := Submodule.eq_of_le_of_finrank_le ua (by omega)
    exact (forced A B l (entry l b) (sym 1) (sym b) start step U eq ub).trans ker
  · intro kill
    obtain ⟨aa,bb,ab⟩ := orthogonals A B l (entry l b) (sym 1) (sym b) start step last
    have rd : Module.finrank F (D⊓A.ker : Submodule F K)=2 := by rwa [inf_eq_right.mpr rad]
    have half : Module.finrank F D≤k+1 := by
      have bound:=A.finrank_add_finrank_orthogonal' D
      have incl:=Submodule.finrank_mono aa
      change Module.finrank F D≤Module.finrank F (A.orthogonal D) at incl
      omega
    obtain ⟨U,_,zero,size,ua,ub⟩ := Green51PencilHyperplanes.of_radical_dimension A B (alt 1) (alt b)
      D half (by omega) aa bb ab f kill
    exact ⟨U,size,zero,fun x hx y hy => ⟨by simpa [A,bracketForm] using ua hy x hx,ub hy x hx⟩⟩
end Green51EvenChains

#print axioms Green51EvenChains.normalized_radical
#print axioms Green51EvenChains.scaled_flat_iff
#print axioms Green51EvenChains.chain_relations
#print axioms Green51EvenChains.in_hyperplane_iff
