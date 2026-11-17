import Mathlib

/-!
# Activated random walk on the comb

Authors: Matthew Junge, Josh Meisel, and Aldo Morelli.
Origin: [NYC Discrete Math REU 2025](https://arxiv.org/abs/2508.14977v2).
Reference: M. Junge, J. Meisel, and A. Morelli, *Activated random walk on the comb*,
arXiv:2508.14977v2 (2025), 16 pp.
-/

noncomputable section

namespace Junge2025Activated

open Filter
open scoped ENNReal NNReal Topology

open scoped Classical in
/-- **Unnumbered conjecture** (Section 1.3). For every positive sleep rate, the limiting
stationary densities on the teeth and spine exist and are strictly ordered below the interval
density.

Stationarity is sampled by stabilizing one active particle per nonsink site, with the terminal
law given by absorbing-event probabilities; densities are normalized by the spine length, and
`r` is the source's sleep rate `λ`. -/
theorem section_1_3_density_order (r : ℝ≥0) (hr : 0 < r) :
    let density : ℕ → Bool → Bool → ℝ := fun n withTeeth countTeeth ↦
      let V := Fin (n + 2) ⊕ Fin (if withTeeth then n else 0)
      let G : SimpleGraph V := SimpleGraph.fromRel fun v w ↦
        match v, w with
        | .inl i, .inl j => (SimpleGraph.pathGraph (n + 2)).Adj i j
        | .inl i, .inr j => i.val = j.val + 1
        | _, _ => False
      let sink : V → Prop := fun v ↦
        match v with
        | .inl i => i.val = 0 ∨ i.val = n + 1
        | .inr _ => False
      let State := V → Option ℕ
      let step : State → PMF State := fun s ↦
        (PMF.uniformOfFintype V).bind fun v ↦
          if sink v then PMF.pure s else
            match s v with
            | none => PMF.pure s
            | some 0 => PMF.pure s
            | some (a + 1) =>
              let jump : PMF State :=
                if h : (G.neighborFinset v).Nonempty then
                  (PMF.uniformOfFinset (G.neighborFinset v) h).map fun w ↦
                    if sink w then Function.update s v (some a) else
                      Function.update (Function.update s v (some a)) w
                        (some (match s w with | none => 2 | some b => b + 1))
                else PMF.pure s
              if a = 0 then
                (PMF.ofFintype (fun b : Bool ↦
                    if b then (r / (1 + r) : ℝ≥0)
                    else (1 - r / (1 + r) : ℝ≥0))
                  (by
                    simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
                    exact_mod_cast add_tsub_cancel_of_le
                      ((div_le_one (by positivity)).2 (by simp) :
                        r / (1 + r) ≤ 1))).bind fun sleep ↦
                      if sleep then PMF.pure (Function.update s v none) else jump
              else jump
      (∑ v : V,
        if ¬sink v ∧ (match v with | .inl _ => !countTeeth | .inr _ => countTeeth)
        then (⨆ t : ℕ, (((fun μ : PMF State ↦ μ.bind step)^[t])
            (PMF.pure (fun u ↦ some (if sink u then 0 else 1) : State))).toOuterMeasure
              {s | (∀ u, ¬sink u → s u = some 0 ∨ s u = none) ∧ s v = none}).toReal
        else 0) / n
    ∃ teeth spine interval : ℝ,
      Tendsto (fun n ↦ density n true true) atTop (𝓝 teeth) ∧
      Tendsto (fun n ↦ density n true false) atTop (𝓝 spine) ∧
      Tendsto (fun n ↦ density n false false) atTop (𝓝 interval) ∧
      teeth < spine ∧ spine < interval := by
  sorry

end Junge2025Activated
