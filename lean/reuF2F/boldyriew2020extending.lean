import Mathlib

/-!
# Extending Zeckendorf's Theorem to a Non-constant Recurrence and the Zeckendorf Game

Authors: Elzbieta Boldyriew, Anna Cusenza, Linglong Dai, Pei Ding, Aidan Dunkelberg,
John Haviland, Kate Huffman, Dianhui Ke, Daniel Kleber, Jason Kuretski, John Lentfer,
Tianhao Luo, Steven J. Miller, Clayton Mizgerd, Vashisth Tiwari, Jingkai Ye,
Yunhao Zhang, Xiaoyan Zheng, and Weiduo Zhu.
Origin: [Polymath Jr.](https://arxiv.org/abs/2009.12475).
Reference: E. Boldyriew, A. Cusenza, L. Dai, P. Ding, A. Dunkelberg, J. Haviland, K. Huffman,
D. Ke, D. Kleber, J. Kuretski, J. Lentfer, T. Luo, S. J. Miller, C. Mizgerd, V. Tiwari, J. Ye,
Y. Zhang, X. Zheng, and W. Zhu, *Extending Zeckendorf's theorem to a non-constant recurrence and
the Zeckendorf game on this non-constant recurrence relation*, Fibonacci Quart. **58** (2020),
no. 5, 55-76.
-/

noncomputable section

namespace Boldyriew2020Extending

open Filter MeasureTheory
open scoped Topology Real
open Finset

/-- The non-constant recurrence `a_1 = 1`, `a_2 = 2`, `a_{n+1} = n a_n + a_{n-1}` for `n ≥ 2`.
The zeroth value is a junk value. -/
def seqA : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => (n + 2) * seqA (n + 2) + seqA (n + 1)

/-- A legal decomposition of `N`, as a finite-support coefficient function (Definition 1.1). The
condition `s 0 = 0` records that source indices start at `1`. -/
def IsLegalDecomposition (s : ℕ → ℕ) (N : ℕ) : Prop :=
  s 0 = 0 ∧
    (∀ i ≥ 1, s i ≤ i) ∧
      (∀ i ≥ 2, s i = i → s (i - 1) = 0) ∧
        ∃ m : ℕ, (∀ i : ℕ, m < i → s i = 0) ∧
          ∑ i ∈ Finset.Icc 1 m, s i * seqA i = N

open scoped Classical in
/-- The legal decomposition of `N`, chosen classically. The source proves it exists and is
unique; the fallback when none exists is a junk value. -/
def legalDecomposition (N : ℕ) : ℕ → ℕ :=
  if h : ∃ s : ℕ → ℕ, IsLegalDecomposition s N then Classical.choose h else fun _ ↦ 0

/-- **Unnumbered conjecture** (Section 5 (Gaussianity), p. 6). The distribution of the number of
summands in legal decompositions of integers `m` in `[a_n, a_{n+1})` converges to a Gaussian as
`n → ∞`. -/
theorem conjecture_gaussian_summand_distribution :
    (∀ᶠ n in atTop,
      let summandCount : ℕ → ℕ := fun m ↦
        ∑ i ∈ Finset.Icc 1 n, legalDecomposition m i
      0 <
        (∑ m ∈ Finset.Ico (seqA n) (seqA (n + 1)),
            ((summandCount m : ℝ) -
              (∑ k ∈ Finset.Ico (seqA n) (seqA (n + 1)), (summandCount k : ℝ)) /
                #(Finset.Ico (seqA n) (seqA (n + 1)))) ^ 2) /
          #(Finset.Ico (seqA n) (seqA (n + 1)))) ∧
      ∀ a b : ℝ, a < b →
        Tendsto (fun n : ℕ ↦
          let summandCount : ℕ → ℕ := fun m ↦
            ∑ i ∈ Finset.Icc 1 n, legalDecomposition m i
          let μ :=
            (∑ m ∈ Finset.Ico (seqA n) (seqA (n + 1)), (summandCount m : ℝ)) /
              #(Finset.Ico (seqA n) (seqA (n + 1)))
          let σ := √((∑ m ∈ Finset.Ico (seqA n) (seqA (n + 1)),
                ((summandCount m : ℝ) - μ) ^ 2) /
              #(Finset.Ico (seqA n) (seqA (n + 1))))
          ((#{m ∈ Finset.Ico (seqA n) (seqA (n + 1)) |
            a ≤ ((summandCount m : ℝ) - μ) / σ ∧
              ((summandCount m : ℝ) - μ) / σ ≤ b} : ℝ) /
            #(Finset.Ico (seqA n) (seqA (n + 1))))) atTop
          (𝓝 (∫ x in a..b, (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2))) := by
  sorry

end Boldyriew2020Extending
