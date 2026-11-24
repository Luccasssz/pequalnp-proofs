import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.SharedBlockCost

theorem PEqualNP.Outside.R_meta_2685_2
    (hCompress : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
      (C : Circuit),
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (Np + Nl) C →
      (∀ z : Fin (Np + Nl) → Bool, circuitFun (Np + Nl) C z =
        decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧
          z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      (let G : SimpleGraph (Fin (Np + Nl)) := SimpleGraph.fromRel fun x y =>
        ∃ p : Fin Np, ∃ l : Fin Nl,
          ((x = Fin.castAdd Nl p ∧ y = Fin.natAdd Np l) ∨
            (x = Fin.natAdd Np l ∧ y = Fin.castAdd Nl p)) ∧ I p l
       HasSharedBlockCost G C.size))
    (hRealize : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (c : ℕ),
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      (let G : SimpleGraph (Fin (Np + Nl)) := SimpleGraph.fromRel fun x y =>
        ∃ p : Fin Np, ∃ l : Fin Nl,
          ((x = Fin.castAdd Nl p ∧ y = Fin.natAdd Np l) ∨
            (x = Fin.natAdd Np l ∧ y = Fin.castAdd Nl p)) ∧ I p l
       HasSharedBlockCost G c) →
      ∃ (D : Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧
        (∀ y : Fin (Np + Nl) → Bool, circuitFun (Np + Nl) D y =
          decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧
            y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧
        D.size ≤ c ∧
        (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧
          (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧
          (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ L) ∧
        ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
          ∃ a b : ℕ, (gateAt D i).inputs = [a, b] ∧
            ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (Np + Nl) C →
      (∀ z : Fin (Np + Nl) → Bool, circuitFun (Np + Nl) C z =
        decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧
          z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      ∃ (D : Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧
        (∀ y : Fin (Np + Nl) → Bool, circuitFun (Np + Nl) D y =
          decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧
            y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧
        D.size ≤ C.size ∧
        (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧
          (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧
          (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ L) ∧
        ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
          ∃ a b : ℕ, (gateAt D i).inputs = [a, b] ∧
            ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  intro Np Nl I dec C hfour hAO hfun
  have hcost := hCompress Np Nl I C hfour hAO hfun
  obtain ⟨D, P, L, hD, hDfun, hsize, hP, hL, hAnd⟩ :=
    hRealize Np Nl I C.size hfour hcost
  exact ⟨D, P, L, hD, hDfun, hsize, hP, hL, hAnd⟩
