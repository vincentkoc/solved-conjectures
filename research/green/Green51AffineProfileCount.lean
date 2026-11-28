import Green51RowInventory

/-! # Six-frequency profiles and the quotient of the dense doubles -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51MissingMasks Green51Hyperplane
open scoped Classical Pointwise

abbrev Profile := (Fin 3 → ℕ) × Multiset ℕ

def profile (h : RowKind→ℕ) : Profile :=
  ⟨fun j => h (.inl j), (univ : Finset Direction).val.map (fun j => h (.inr j))⟩

def raw {V : Type*} (B : Finset V) (row : V→Finset Four) : RowKind→ℕ :=
  frequency (fun i : B => kind (row i.val))

def Valid (g k : ℕ) (p : Profile) : Prop :=
  ∃ h : RowKind→ℕ, (∑ t,h t)=g ∧ (∑ t,h t*sizeOfKind t)=k ∧ profile h=p

private theorem value_count {I : Type*} [Fintype I] (v : I→ℕ) (n : ℕ) :
    ((univ : Finset I).val.map v).count n=frequency v n := by
  classical
  simp [Multiset.count_map, ←Finset.filter_val,frequency,Fintype.card_subtype,eq_comm]

theorem profile_eq {h h' : RowKind→ℕ} : profile h=profile h' ↔
    (∀ j : Fin 3,h (.inl j)=h' (.inl j)) ∧
    ∀ n : ℕ,frequency (fun d : Direction => h (.inr d)) n =
      frequency (fun d : Direction => h' (.inr d)) n := by
  constructor
  · intro eq
    refine ⟨fun j => congrFun (congrArg Prod.fst eq) j,fun n => ?_⟩
    simpa only [profile,value_count] using congrArg (fun p : Profile => p.2.count n) eq
  · rintro ⟨l,r⟩
    refine Prod.ext (funext l) (Multiset.ext.mpr (fun n => ?_))
    simpa only [profile,value_count] using r n

variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

def affineSetoid (T : Finset (Finset G)) : Setoid ↥T where
  r S U := AffineRelated S.val U.val
  iseqv := ⟨fun S => ⟨LinearEquiv.refl F G,0,by simp⟩,
    fun h => h.symm,fun a b => a.trans b⟩

/-- Two affine classes of dense doubles coincide precisely when their occupied-row profiles agree. -/
theorem count_profiles {s k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^2 < 8*k) :
    Nat.card (Quotient (affineSetoid (countedDoubles (2*(s+1)+2) k (threshold (2*s))))) =
      Nat.card {p : Profile // Valid (2*s+3) k p} := by
  classical
  let D := countedDoubles (2*(s+1)+2) k (threshold (2*s))
  obtain ⟨B,ref,size,full⟩ := spanning_reference s (by omega)
  choose R live number pres using fun (S : D) => present_counted hs near ref size full S.property
  have existsProfile (S : D) : Valid (2*s+3) k (profile (raw B (R S))) := by
    obtain ⟨n,w⟩ := (inventory_iff B k (raw B (R S))).mp ⟨R S,live S,number S,fun _ => rfl⟩
    exact ⟨_,n.trans size,w,rfl⟩
  let f (S : D) : {p : Profile // Valid (2*s+3) k p} := ⟨_,existsProfile S⟩
  have compare {A T : Finset (𝔽₂ (2*(s+1)+2))} (x y : 𝔽₂ (2*(s+1))→Finset Four)
      (hx : ∀ i∈B,(x i).Nonempty) (hy : ∀ i∈B,(y i).Nonempty) (nx : (layers B x).card=k)
      (ny : (layers B y).card=k) (a : Presents B x A) (b : Presents B y T) :
      AffineRelated A T ↔ profile (raw B x)=profile (raw B y) :=
    ((presented_equivalence near ref size full hx hy nx ny a b).trans
      (signature_iff (fun i : B => x i.val) (fun i : B => y i.val)
        (fun i => hx _ i.property) (fun i => hy _ i.property))).trans profile_eq.symm
  have related (S T : D) : AffineRelated S.val T.val ↔ f S=f T :=
    (compare _ _ (live S) (live T) (number S) (number T) (pres S) (pres T)).trans
      ⟨fun eq => Subtype.ext eq,fun eq => congrArg Subtype.val eq⟩
  let L : Quotient (affineSetoid D) → {p : Profile // Valid (2*s+3) k p} :=
    Quotient.lift f (fun S T h => (related S T).mp h)
  apply Nat.card_congr (Equiv.ofBijective L ⟨?_,?_⟩)
  · intro x y
    induction x using Quotient.inductionOn with | _ S =>
      induction y using Quotient.inductionOn with | _ T =>
        exact fun eq => Quotient.sound ((related S T).mpr eq)
  · rintro ⟨p,h,n,w,rfl⟩
    obtain ⟨row,occ,sz,freq⟩ := (inventory_iff B k h).mpr ⟨n.trans size.symm,w⟩
    obtain ⟨S,hS,H⟩ := realize_rows hs near ref size full row occ sz
    let z : D := ⟨S,hS⟩
    have refl : AffineRelated S S := (affineSetoid D).iseqv.refl z
    have agree := (compare _ _ (live z) occ (number z) sz (pres z) H).mp refl
    refine ⟨Quotient.mk (affineSetoid D) z,Subtype.ext ?_⟩
    exact agree.trans (congrArg profile (funext freq))

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.profile_eq
#print axioms Green51FrameIsomorphisms.count_profiles
