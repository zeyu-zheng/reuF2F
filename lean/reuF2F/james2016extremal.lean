import Mathlib

/-!
# Extremal Primes for Elliptic Curves

Authors: Kevin James, Brandon Tran, Minh-Tam Trinh, Phil Wertheimer, and Dania Zantout.
Origin: [Clemson University REU
2012](https://www.math.clemson.edu/~kevja/PAPERS/ExtremalPrimes-FinalVersion.pdf).
Reference: K. James, B. Tran, M.-T. Trinh, P. Wertheimer, and D. Zantout, *Extremal primes for
elliptic curves*, J. Number Theory **164** (2016), 282-298.
-/

noncomputable section

namespace James2016Extremal

open scoped Topology
open Finset

open scoped Classical in
/-- The number of good-reduction primes below `X` whose Frobenius trace attains either integer
endpoint of the Hasse interval, `π_E⁺(X) + π_E⁻(X)` (Section 3). -/
def extremalPrimeCount (W : WeierstrassCurve ℚ) (X : ℝ) : ℕ :=
  #{p ∈ Finset.range (Nat.ceil X) |
    if hp : p.Prime then
      letI : Fact p.Prime := ⟨hp⟩
      let Wp := (W.map (algebraMap ℚ (Padic p))).minimal (PadicInt p)
      let R := (Wp.reduction (PadicInt p)).map
        (PadicInt.residueField (p := p)).toRingHom
      Wp.HasGoodReduction (PadicInt p) ∧
        |(p : ℤ) + 1 - (Nat.card R.toAffine.Point : ℤ)| =
          Int.floor (2 * √(p : ℝ))
    else False}

/-- **Conjecture 3.3** (author manuscript p. 4). Every non-CM rational elliptic curve has
asymptotically `C_E X ^ (1 / 4) / log X` extremal primes, for some `C_E > 0`.

Non-CM is expressed through the complete list of rational CM `j`-invariants. -/
theorem conjecture_3_3 (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (h_nonCM : W.j ∉ ({-262537412640768000, -147197952000, -884736000,
      -12288000, -884736, -32768, -3375, 0, 1728, 8000, 54000,
      287496, 16581375} : Finset ℚ)) :
    ∃ C > (0 : ℝ),
      Filter.Tendsto
        (fun X : ℝ ↦ (extremalPrimeCount W X : ℝ) /
          (C * X ^ (1 / 4 : ℝ) / Real.log X))
        Filter.atTop (𝓝 1) := by sorry

end James2016Extremal
