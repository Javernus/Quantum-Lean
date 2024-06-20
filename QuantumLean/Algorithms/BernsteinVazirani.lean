-- Import the gates
import «QuantumLean».Data.Circuits.Qubits
import «QuantumLean».Gates.Hadamard
import «QuantumLean».Gates.Pauli

open Circuits
open Gates
open Equivalences


namespace BernsteinVazirani


def Oracle (sᵢ : Bool) : nMatrix 1 := Z ^ sᵢ.toNat
def Oracleₛ (s : ℕ -> Bool) : (i : ℕ) -> nMatrix 1 := fun i => Oracle (s i)
def Outcome (s : ℕ -> Bool) : (i : ℕ) -> Qubit 1 := fun i => QZero * 2 • X ^ (s i).toNat


theorem sᵢ_eq_zero : H * Z ^ Bool.toNat false * H = 2 • X ^ Bool.toNat false := by
  rw [Bool.toNat_false, pow_zero, mul_one, H_Identity, pow_zero, @nsmul_one]


theorem sᵢ_eq_one : (H * Z ^ Bool.toNat true * H) = 2 • X ^ Bool.toNat true := by
  rw [Bool.toNat_true]
  simp only [pow_one]
  exact HZHeqX'


theorem BernsteinVaziraniAlgorithm (s : ℕ -> Bool) : QZeroₙ n * (Hₙ n * (tensor_power n (Oracleₛ s)) * Hₙ n) = tensor_power n (Outcome s) := by
  rw [QZeroₙ, Hₙ, tensor_power_mul, tensor_power_mul, tensor_power_mul]
  induction n with
    | zero => rw [Nat.zero_eq, tensor_power, tensor_power]
    | succ n ih =>
      -- ih : (tensor_power n fun i ↦ QZero * (H * Oracleₛ s i * H)) = tensor_power n (Outcome s)
      rw [tensor_power, tensor_power]
      -- (tensor_power n fun i ↦ QZero * (H * Oracleₛ s i * H)) ⊗ₖ (Oracleₛ s i * H)
      -- = (tensor_power n (Outcome s)) ⊗ₖ (Outcome s (n + 1))
      rw [ih, Oracleₛ, Oracle, Outcome]
      cases (s (n + 1));
      rw [sᵢ_eq_zero]
      rw [sᵢ_eq_one]

end BernsteinVazirani
