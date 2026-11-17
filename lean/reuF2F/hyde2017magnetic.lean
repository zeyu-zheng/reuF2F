import Mathlib

/-!
# Magnetic Laplacians of locally exact forms on the Sierpinski Gasket

Authors: Jessica Hyde, Daniel Kelleher, Jesse Moeller, Luke G. Rogers, and Luis Seda.
Origin: [University of Connecticut REU
2013](https://mathreu.uconn.edu/2016/04/21/spectrum-of-the-magnetic-laplacian-on-the-sierpinski-gasket/).
Reference: J. Hyde, D. Kelleher, J. Moeller, L. G. Rogers, and L. Seda, *Magnetic Laplacians of
locally exact forms on the Sierpinski Gasket*, Commun. Pure Appl. Anal. **16** (2017), no. 6,
2299–2319; doi:10.3934/cpaa.2017113; arXiv:1604.01340v1.
-/

noncomputable section
open scoped Topology

namespace Hyde2017Magnetic

/-- The ordered vertices of the equilateral boundary triangle. -/
def boundary (i : Fin 3) : EuclideanSpace ℝ (Fin 2) :=
  if i = 0 then WithLp.toLp 2 ![0, 0]
  else if i = 1 then WithLp.toLp 2 ![1, 0]
  else WithLp.toLp 2 ![(1 : ℝ) / 2, √3 / 2]

/-- The contraction `F_i(x) = (x + p_i) / 2`. -/
def contraction (i : Fin 3) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  (1 / 2 : ℝ) • (x + boundary i)

/-- The cell map `F_w`, with the first word letter outermost. -/
def cellMap {m : ℕ} (w : Fin m → Fin 3) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  (List.ofFn w).foldr contraction x

/-- The finite vertex sets `V_m` of the graph approximations. -/
def vertices : ℕ → Finset (EuclideanSpace ℝ (Fin 2))
  | 0 => Finset.univ.image boundary
  | m + 1 => Finset.univ.biUnion fun i ↦ (vertices m).image (contraction i)

/-- The Sierpinski gasket, as the closure of its finite-level vertices. -/
def gasket : Set (EuclideanSpace ℝ (Fin 2)) :=
  closure (⋃ m : ℕ, (vertices m : Set (EuclideanSpace ℝ (Fin 2))))

/-- The weighted finite pairing of cell potentials, with each edge counted once. -/
def formPairing (m : ℕ) (a b : (Fin m → Fin 3) → Fin 3 → ℝ) : ℝ :=
  (5 / 3 : ℝ) ^ m *
    ∑ w : Fin m → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
      if i < j then (a w j - a w i) * (b w j - b w i) else 0

/-- Harmonic refinement of mean-zero cell potentials, recentered in each child. -/
def refine (m : ℕ) (q : (Fin m → Fin 3) → Fin 3 → ℝ)
    (v : Fin (m + 1) → Fin 3) (j : Fin 3) : ℝ :=
  let w : Fin m → Fin 3 := fun k ↦ v k.castSucc
  let i := v (Fin.last m)
  if j = i then 3 * q w i / 5 else (q w j - q w i) / 5

/-- The renormalized nonmagnetic graph energy ((A2)). -/
def graphEnergy (m : ℕ) (f : EuclideanSpace ℝ (Fin 2) → ℂ) : ℝ :=
  (5 / 3 : ℝ) ^ m *
    ∑ w : Fin m → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
      if i < j then ‖f (cellMap w (boundary j)) - f (cellMap w (boundary i))‖ ^ 2
      else 0

/-- The unrenormalized magnetic graph energy (3.1), with `a(e_xy) = a(y) - a(x)`. -/
def magneticGraphEnergy (m : ℕ) (a : (Fin m → Fin 3) → Fin 3 → ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) : ℝ :=
  ∑ w : Fin m → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
    if i < j then
      ‖f (cellMap w (boundary i)) - f (cellMap w (boundary j)) *
        Complex.exp (Complex.I * ((a w j - a w i : ℝ) : ℂ))‖ ^ 2
    else 0

/-- **Remark 3.9**. The renormalized magnetic graph energies converge to the continuum magnetic
quadratic form for every real one-form and every complex finite-energy function.

Mean-zero compatible bounded-energy sequences represent all one-forms by Theorem 2.2, with
compatibility read as weighted adjoint compatibility (canonical cellwise projection); each cell
edge is counted once with the factor `(5 / 3) ^ m`, and the right side is the squared norm of
`∂f + i f a`; no local Coulomb gauge, convergence premise or local-exactness restriction is added.
Ambient values off the gasket are irrelevant. -/
theorem magnetic_energy_convergence
    (a : (m : ℕ) → (Fin m → Fin 3) → Fin 3 → ℝ)
    (ha_mean : ∀ (m : ℕ) (w : Fin m → Fin 3), ∑ i : Fin 3, a m w i = 0)
    (ha_bound : BddAbove (Set.range fun m : ℕ ↦ formPairing m (a m) (a m)))
    (ha_compat : ∀ (m : ℕ) (q : (Fin m → Fin 3) → Fin 3 → ℝ),
      (∀ w : Fin m → Fin 3, ∑ i : Fin 3, q w i = 0) →
      formPairing m (a m) q = formPairing (m + 1) (a (m + 1)) (refine m q))
    (f : EuclideanSpace ℝ (Fin 2) → ℂ)
    (hf_cont : ContinuousOn f gasket)
    (hf_bound : BddAbove (Set.range fun m : ℕ ↦ graphEnergy m f)) :
    Filter.Tendsto (fun m : ℕ ↦ (5 / 3 : ℝ) ^ m * magneticGraphEnergy m (a m) f)
      Filter.atTop
      (𝓝 (Filter.limUnder Filter.atTop (fun m : ℕ ↦
        (5 / 3 : ℝ) ^ m *
          ∑ w : Fin m → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
            if i < j then
              ‖(f (cellMap w (boundary j)) - f (cellMap w (boundary i))) +
                Complex.I * f (cellMap w (boundary 0)) *
                  ((a m w j - a m w i : ℝ) : ℂ)‖ ^ 2
            else 0))) := by
  sorry

end Hyde2017Magnetic
