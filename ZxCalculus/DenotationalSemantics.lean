import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import ZxCalculus.AST

open Matrix Complex

/-- The space of n qubits is represented as 2^n × 1 column vectors -/
abbrev Qubits (n : ℕ) := Matrix (Fin (2^n)) (Fin 1) ℂ

/-- Linear maps between qubit spaces are matrices -/
abbrev LinMap (n m : ℕ) := Matrix (Fin (2^m)) (Fin (2^n)) ℂ

noncomputable section

/-- The swap matrix for 2 qubits (4×4) -/
def swap_2x2 : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![1, 0, 0, 0],
    ![0, 0, 1, 0],
    ![0, 1, 0, 0],
    ![0, 0, 0, 1]]

/-- General swap for n and m qubits -/
def swap_gen (n m : ℕ) : LinMap (n + m) (m + n) :=
  Matrix.of fun (i : Fin (2^(m+n))) (j : Fin (2^(n+m))) =>
    let m_out := i.val / (2^n)
    let n_out := i.val % (2^n)
    let n_in := j.val / (2^m)
    let m_in := j.val % (2^m)
    if m_out = m_in && n_out = n_in then 1 else 0

/-- Ket: column vector -/
def ket {n : ℕ} (v : Qubits n) : LinMap 0 n := v

/-- Bra: row vector (conjugate transpose) -/
def bra {n : ℕ} (v : Qubits n) : LinMap n 0 := vᴴ

/-- Interpret ZX generators as matrices -/
def interpGen {n m : ℕ} (g : Generator n m) : LinMap n m :=
  match g with
  | .empty => 1  -- 1×1 identity
  | .id => 1     -- 2×2 identity
  | .swap n m => swap_gen n m
  | .H => ((1:ℂ)/√2) • ![![1, 1],
                       ![1, -1]]  -- Hadamard
  | .Z α n m => sorry -- Z spider
  | .X α n m => sorry -- X spider
  | .cup => sorry     -- Bell state
  | .cap => sorry     -- Bell effect

/-- Interpret ZX diagrams as matrices -/
def interp {n m : ℕ} : ZxTerm n m → LinMap n m
  | .gen g => interpGen g
  | f ; g => interp g * interp f  -- Matrix multiplication
  | f ⊗ g =>
    Matrix.of fun i j =>
      let i_prod := finProdFinEquiv.symm (i.cast (by ring))
      let j_prod := finProdFinEquiv.symm (j.cast (by ring))
      kronecker (interp f) (interp g) i_prod j_prod
