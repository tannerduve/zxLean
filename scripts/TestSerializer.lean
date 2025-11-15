import ZxCalculus.Parser.QGraph
import ZxCalculus.Gates

/-!
# Test Serializer

Simple test to demonstrate Lean → .qgraph serialization.
-/

open ZxCalculus.Parser
open ZxTerm

def main : IO Unit := do
  IO.println "========================================="
  IO.println "Lean → .qgraph Serialization Test"
  IO.println "=========================================\n"

  -- Test 1: Simple Hadamard
  IO.println "1. Hadamard Gate (1→1):"
  let hadamard := H
  let qgraph1 := serializeToQGraph hadamard
  IO.println s!"   Vertices: {qgraph1.vertices.size}"
  IO.println s!"   Edges: {qgraph1.edges.size}"
  IO.println s!"   Inputs: {qgraph1.inputs}"
  IO.println s!"   Outputs: {qgraph1.outputs}"
  saveZxTermAsQGraph ⟨"test_hadamard_lean.qgraph"⟩ hadamard
  IO.println "   ✓ Saved to test_hadamard_lean.qgraph\n"

  -- Test 2: Identity
  IO.println "2. Identity (1→1):"
  let identity := ZxTerm.id
  let qgraph2 := serializeToQGraph identity
  IO.println s!"   Vertices: {qgraph2.vertices.size}"
  IO.println s!"   Edges: {qgraph2.edges.size}"
  saveZxTermAsQGraph ⟨"test_identity_lean.qgraph"⟩ identity
  IO.println "   ✓ Saved to test_identity_lean.qgraph\n"

  -- Test 3: Z spider with phase
  IO.println "3. Z Spider with phase π/4 (1→1):"
  let zspi := Z (1/4) 1 1
  let qgraph3 := serializeToQGraph zspi
  IO.println s!"   Vertices: {qgraph3.vertices.size}"
  IO.println s!"   Edges: {qgraph3.edges.size}"
  -- Print vertices to show phase
  for v in qgraph3.vertices do
    if v.vtype == .z then
      IO.println s!"   Z vertex: phase = {v.phase}"
  saveZxTermAsQGraph ⟨"test_z_spider_lean.qgraph"⟩ zspi
  IO.println "   ✓ Saved to test_z_spider_lean.qgraph\n"

  -- Test 4: Composition (H ; Z π/2)
  IO.println "4. Hadamard then Z-phase (composition):"
  let comp := H ; Z (1/2) 1 1
  let qgraph4 := serializeToQGraph comp
  IO.println s!"   Vertices: {qgraph4.vertices.size}"
  IO.println s!"   Edges: {qgraph4.edges.size}"
  saveZxTermAsQGraph ⟨"test_composition_lean.qgraph"⟩ comp
  IO.println "   ✓ Saved to test_composition_lean.qgraph\n"

  -- Test 5: Tensor (H ⊗ id) - 2 qubits
  IO.println "5. Hadamard on qubit 0, identity on qubit 1 (tensor):"
  let tens := H ⊗ ZxTerm.id
  let qgraph5 := serializeToQGraph tens
  IO.println s!"   Vertices: {qgraph5.vertices.size}"
  IO.println s!"   Edges: {qgraph5.edges.size}"
  IO.println s!"   Inputs: {qgraph5.inputs.size} qubits"
  saveZxTermAsQGraph ⟨"test_tensor_lean.qgraph"⟩ tens
  IO.println "   ✓ Saved to test_tensor_lean.qgraph\n"

  IO.println "========================================="
  IO.println "✓ All serialization tests complete!"
  IO.println "========================================="
  IO.println "\nGenerated files:"
  IO.println "  - test_hadamard_lean.qgraph"
  IO.println "  - test_identity_lean.qgraph"
  IO.println "  - test_z_spider_lean.qgraph"
  IO.println "  - test_composition_lean.qgraph"
  IO.println "  - test_tensor_lean.qgraph"
  IO.println "\nYou can load these in PyZX with:"
  IO.println "  import pyzx as zx"
  IO.println "  g = zx.Graph.from_json(open('test_hadamard_lean.qgraph').read())"
