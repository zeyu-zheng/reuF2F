import Mathlib

/-!
# Deficiency of chemical reaction networks: the effect of operations that preserve multistationarity and periodic orbits

Authors: Awildo Gutierrez, Elijah Leake, Caelyn Rivas-Sobie, Jordy Lopez Garcia, and Anne Shiu.
Origin: [MSRI-UP 2022](https://arxiv.org/abs/2305.19410v2).
Reference: A. Gutierrez, E. Leake, C. Rivas-Sobie, J. Lopez Garcia, and A. Shiu, *Deficiency of
chemical reaction networks: the effect of operations that preserve multistationarity and periodic
orbits*, Discrete Contin. Dyn. Syst. B **30** (2025), no. 5, 1745–1761.
-/

noncomputable section

namespace Gutierrez2025Deficiency

/-- A finite nonempty set of nontrivial reactions between nonnegative integer complexes
(Definition 2.1). -/
structure Network (n : ℕ) where
  /-- The reactions, as (reactant complex, product complex) pairs. -/
  reactions : Finset ((Fin n → ℕ) × (Fin n → ℕ))
  nonempty : reactions.Nonempty
  nontrivial : ∀ r ∈ reactions, r.1 ≠ r.2

/-- The real span of the reaction vectors (Definition 2.3). -/
def Network.stoichiometric {n : ℕ} (N : Network n) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range fun r : N.reactions ↦
    fun i ↦ (r.val.2 i : ℝ) - (r.val.1 i : ℝ))

/-- The mass-action species-formation vector field, with one rate constant per reaction. -/
def Network.vectorField {n : ℕ} (N : Network n) (κ : N.reactions → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  ∑ r : N.reactions, (κ r * ∏ i, x i ^ r.val.1 i) •
    (fun i ↦ (r.val.2 i : ℝ) - (r.val.1 i : ℝ))

/-- A positive nonconstant periodic orbit whose trivial Floquet multiplier is simple on its
stoichiometric subspace (Banaji, arXiv:2201.13105v3, p. 3). -/
structure Network.NondegeneratePeriodicOrbit {n : ℕ} (N : Network n)
    (κ : N.reactions → ℝ) where
  /-- The positive period of the orbit. -/
  period : ℝ
  period_pos : 0 < period
  /-- The positive periodic solution of the mass-action system. -/
  trajectory : ℝ → (Fin n → ℝ)
  positive : ∀ t i, 0 < trajectory t i
  nonconstant : ∃ t, trajectory t ≠ trajectory 0
  periodic : Function.Periodic trajectory period
  solution : IsIntegralCurve trajectory (fun _ ↦ N.vectorField κ)
  /-- The fundamental solution of the variational equation on the stoichiometric subspace. -/
  fundamental : ℝ → (N.stoichiometric →L[ℝ] N.stoichiometric)
  initial : fundamental 0 = ContinuousLinearMap.id ℝ N.stoichiometric
  variational : ∀ t (v : N.stoichiometric),
    HasDerivAt (fun u ↦ ((fundamental u v : N.stoichiometric) : Fin n → ℝ))
      (fderiv ℝ (N.vectorField κ) (trajectory t)
        ((fundamental t v : N.stoichiometric) : Fin n → ℝ)) t
  multiplier_one : (fundamental period).toLinearMap.charpoly.eval 1 = 0
  multiplier_simple : (fundamental period).toLinearMap.charpoly.derivative.eval 1 ≠ 0

/-- **Remark 3.2** (preprint Remark 3.3). Partial flow additions satisfying
Cappelletti–Feliu–Wiuf Theorem 8 preserve the capacity for positive nondegenerate periodic orbits.

Capacity is existential in mass-action rates on both networks, and nondegeneracy means a simple
Floquet multiplier `1`, not hyperbolicity or stability. -/
theorem partial_flow_inherits_periodic_orbit {n : ℕ} (hn : 0 < n)
    (N N' : Network n) (I O : Finset (Fin n))
    (hin : ∀ i ∈ I, (0, Pi.single i 1) ∉ N.reactions)
    (hout : ∀ i ∈ O, (Pi.single i 1, 0) ∉ N.reactions)
    (hext : N'.reactions = N.reactions ∪
      I.image (fun i ↦ (0, Pi.single i 1)) ∪
      O.image (fun i ↦ (Pi.single i 1, 0))) :
    let WO : Set (Module.Dual ℝ (Fin n → ℝ)) :=
      {w | w ∈ N.stoichiometric.dualAnnihilator ∧ ∀ i ∉ O, w (Pi.single i 1) = 0}
    let conserved := fun x : Fin n → ℝ ↦ fun w : {w // w ∈ WO} ↦ w.val x
    (∀ i ∈ I, i ∉ O → Pi.single i 1 ∈ N.stoichiometric) →
    (∀ w ∈ N.stoichiometric.dualAnnihilator, ∃ a ∈ WO,
      ∃ b ∈ ({v | v ∈ N.stoichiometric.dualAnnihilator ∧ ∀ i ∈ O, v (Pi.single i 1) = 0} :
      Set (Module.Dual ℝ (Fin n → ℝ))), w = a + b) →
    conserved '' {x | ∀ i, 0 < x i} =
      conserved '' {x | (∀ i ∈ I, 0 < x i) ∧ (∀ i ∉ I, x i = 0)} →
    (∃ κ : N.reactions → ℝ, (∀ r, 0 < κ r) ∧
      Nonempty (N.NondegeneratePeriodicOrbit κ)) →
    ∃ κ' : N'.reactions → ℝ, (∀ r, 0 < κ' r) ∧
      Nonempty (N'.NondegeneratePeriodicOrbit κ') := by sorry

end Gutierrez2025Deficiency
