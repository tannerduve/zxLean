import ZxCalculus.SingleQubit.RewriteTerm
import QuantumInfo.Finite.Qubit.Basic


open SingleQubit

/-- Rz(θ): Z-rotation by angle θ·π -/
def Rz (θ : ZMod 8) : ZxDiagram true true := Z θ

-- /-- Rx(θ): X-rotation by angle θ·π -/
def Rx (θ : ZMod 8) : ZxDiagram true true := X θ

/-- T gate: π/4 Z-rotation. Non-Clifford gate required for universality. -/
def T : ZxDiagram true true := Rz 1

/-- S gate: π/2 Z-rotation. Clifford gate. -/
def S : ZxDiagram true true := Rz 2

/--
Pauli Z gate: A Z spider with phase π
-/
def PauliZ : ZxDiagram true true := Rz 4

/--
Paulix X gate: An X spider with phase π
-/
def PauliX : ZxDiagram true true := Rx 4

/-! ### Single–qubit gates -/

noncomputable section

/-- Hadamard gate. -/
def H_gate : 𝐔[Fin 2] := Qubit.H

/-- Pauli `X` gate. -/
def X_gate : 𝐔[Fin 2] := Qubit.X

/-- Pauli `Z` gate. -/
def Z_gate : 𝐔[Fin 2] := Qubit.Z

def S_gate : 𝐔[Fin 2] := Qubit.S

def T_gate : 𝐔[Fin 2] := Qubit.T

/-- Extract the underlying matrix from a unitary. -/
def unitaryToMatrix {d : Type*} [Fintype d] [DecidableEq d] (U : 𝐔[d]) : Matrix d d ℂ :=
  U.val
