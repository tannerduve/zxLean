import ZxCalculus.SingleQubit.RewriteTerm

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
