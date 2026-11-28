import Erdos722MinimumTripleOrder
import Erdos722SymmetricPairPlane
import Erdos722DerivedAffine

/-!
# The exceptional minimum orders

The only undecided equality case in rank three would extend a projective
plane of order ten. In higher ranks the arithmetic gives exactly the two
parameters of the derived and full large Witt design.
-/

namespace Erdos722.MinimumOrder
open Configuration

/-- Existence in the projective-plane convention of Erdős 723. -/
def PlaneOfOrder (q : ℕ) : Prop :=
  ∃ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L)
    (pp : ProjectivePlane P L), pp.order=q

/-- Derive at one point and use the symmetric pair design as the plane. -/
theorem order_ten_of_extension (h : 112 ∈ orders 3 12) : PlaneOfOrder 10 := by
  obtain ⟨_,H,hH⟩ := h
  obtain ⟨G,hG⟩ := Cyclotomy.derive_design (n:=111) (r:=2) (k:=11) hH
  exact projective_plane_of_symmetric_pairs (by decide : 2≤10) hG

/-- The four attained parameter triples at the exterior-point bound. -/
def attained (r k v : ℕ) : Prop :=
  (r=3 ∧ k=4 ∧ v=8) ∨ (r=3 ∧ k=6 ∧ v=22) ∨ (r=4 ∧ k=7 ∧ v=23) ∨ (r=5 ∧ k=8 ∧ v=24)

theorem equality_cases {r k v : ℕ} (hr : 3≤r) (hrk : r<k) (hkv : k<v)
    (he : v=(k-r+1)*(k-r+2)+(r-1)) (h : v∈orders r k) :
    attained r k v ∨ (r=3 ∧ k=12 ∧ v=112 ∧ PlaneOfOrder 10) := by
  obtain ⟨_,H,hH⟩ := h
  rcases boundary_or_square hr hrk hkv hH with hbig|(h|h|h|h|h)
  · have e : (k-r+2)^2=(k-r+1)*(k-r+2)+(k-r+2) := by ring
    rw [e] at hbig
    omega
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  · obtain ⟨rfl,rfl,rfl⟩ := h
    exact Or.inr ⟨rfl,rfl,rfl,order_ten_of_extension ⟨hkv,H,hH⟩⟩

private theorem twelve_at_122 : 122∈orders 3 12 := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact ⟨by decide,Sublines.exists_prime_power_subline_design 11 1 2 (by decide) (by decide)⟩

/-- The unresolved formal input at block size twelve is confined to
order 112. The prime-power construction attains 122 unconditionally. -/
theorem twelve_minimum_alternatives :
    (IsLeast (orders 3 12) 112 ∧ PlaneOfOrder 10) ∨ IsLeast (orders 3 12) 122 := by
  by_cases h112 : 112∈orders 3 12
  · left
    refine ⟨⟨h112,?_⟩,order_ten_of_extension h112⟩
    rintro v ⟨hv,H,hH⟩
    have h := boundary_or_square (by decide : 3≤3) (by decide : 3<12) hv hH
    norm_num at h
    omega
  · right
    refine ⟨twelve_at_122,?_⟩
    intro v hv
    obtain ⟨hkv,H,hH⟩ := hv
    have h := boundary_or_square (by decide : 3≤3) (by decide : 3<12) hkv hH
    have hv' : v≠112 := fun e => h112 (e ▸ (show v∈orders 3 12 from ⟨hkv,H,hH⟩))
    norm_num at h
    omega

#print axioms order_ten_of_extension
#print axioms equality_cases
#print axioms twelve_minimum_alternatives
end Erdos722.MinimumOrder
