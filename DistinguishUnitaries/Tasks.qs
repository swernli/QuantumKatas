// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT license.

namespace Quantum.Kata.DistinguishUnitaries {
    
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Characterization;
    open Microsoft.Quantum.Preparation;
    
    
    //////////////////////////////////////////////////////////////////
    // Welcome!
    //////////////////////////////////////////////////////////////////
    
    // "Distinguishing Unitaries" quantum kata is a series of exercises designed
    // to help you learn to think about unitary transformations in a different way.
    // It covers figuring out ways to distinguish several unitaries from the given list
    // by performing experiments on them.
    
    // Each task is wrapped in one operation preceded by the description of the task.
    // Each task (except tasks in which you have to write a test) has a unit test associated with it,
    // which initially fails. Your goal is to fill in the blank (marked with // ... comment)
    // with some Q# code to make the failing test pass.
    
    // The tasks are given in approximate order of increasing difficulty; harder ones are marked with asterisks.
    

    //////////////////////////////////////////////////////////////////
    // Part I. Single-Qubit Gates
    //////////////////////////////////////////////////////////////////
    
    // Task 1.1. Identity or Pauli X?
    // Input: An operation that implements a single-qubit unitary transformation:
    //        either the identity (I gate)
    //        or the Pauli X gate (X gate).
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the I gate,
    //         1 if the given operation is the X gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants exactly once.
    operation DistinguishIfromX (unitary : (Qubit => Unit is Adj+Ctl)) : Int {
        using (q = Qubit()) {
            unitary(q);
            return M(q) == One ? 1 | 0;
        }
    }
    

    // Task 1.2. Identity or Pauli Z?
    // Input: An operation that implements a single-qubit unitary transformation:
    //        either the identity (I gate)
    //        or the Pauli Z gate (Z gate).
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the I gate,
    //         1 if the given operation is the Z gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants exactly once.
    operation DistinguishIfromZ (unitary : (Qubit => Unit is Adj+Ctl)) : Int {
        using (q = Qubit()) {
            H(q);
            unitary(q);
            return Measure([PauliX], [q]) == One ? 1 | 0;
        }
    }


    // Task 1.3. Z or S?
    // Input: An operation that implements a single-qubit unitary transformation:
    //        either the Pauli Z gate
    //        or the S gate.
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the Z gate,
    //         1 if the given operation is the S gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants at most twice.
    operation DistinguishZfromS (unitary : (Qubit => Unit is Adj+Ctl)) : Int {
        using (q = Qubit()) {
            H(q);
            unitary(q);
            unitary(q);
            return Measure([PauliX], [q]) == One ? 1 | 0;
        }
    }
    

    // Task 1.4. Hadamard or Pauli X?
    // Input: An operation that implements a single-qubit unitary transformation:
    //        either the Hadamard gate
    //        or the Pauli X gate.
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the H gate,
    //         1 if the given operation is the X gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants at most twice.
    operation DistinguishHfromX (unitary : (Qubit => Unit is Adj+Ctl)) : Int {
        using (q = Qubit()) {
            within {
                unitary(q);
            }
            apply {
                X(q);
            }
            return M(q) == One ? 1 | 0;
        }
    }


    // Task 1.5. Z or -Z?
    // Input: An operation that implements a single-qubit unitary transformation:
    //        either the Pauli Z gate
    //        or the minus Pauli Z gate (i.e., a gate -|0〉〈0| + |1〉〈1|).
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the Z gate,
    //         1 if the given operation is the -Z gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants exactly once.
    operation DistinguishZfromMinusZ (unitary : (Qubit => Unit is Adj+Ctl)) : Int {
        using (qs = Qubit[2]) {
            within {
                //ApplyToEachA(H, qs);
                H(qs[0]);
            }
            apply {
                Controlled unitary([qs[0]], qs[1]);
                //Controlled Z([qs[1]], qs[0]);
            }
            //return ResultArrayAsInt(MultiM(qs));
            return M(qs[0]) == One ? 1 | 0;
        }
    }
    

    // Task 1.6. Rz or R1 (arbitrary angle)?
    // Input: An operation that implements a single-qubit unitary transformation:
    //        either the Rz gate 
    //        or the R1 gate.
    // This operation will take two parameters: the first parameter is the rotation angle, in radians, 
    // and the second parameter is the qubit to which the gate should be applied (matching normal Rz and R1 gates in Q#).
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the Rz gate,
    //         1 if the given operation is the R1 gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants exactly once.
    operation DistinguishRzFromR1 (unitary : ((Double, Qubit) => Unit is Adj+Ctl)) : Int {
        using (qs = Qubit[2]) {
            within {
                ApplyToEachA(H, qs);
            }
            apply {
                Controlled unitary([qs[0]], (PI() * 2.0, qs[1]));
                Controlled Adjoint Rz([qs[1]], (PI() * 2.0, qs[0]));
                // H(qs[0]);
            }
            return 3 - ResultArrayAsInt(MultiM(qs));
            // let r = M(qs[0]);
            // Reset(qs[1]);
            // return r == One ? 0 | 1;
        }
    }


    // Task 1.7. Y or XZ?
    // Input: An operation that implements a single-qubit unitary transformation:
    //        either the Pauli Y gate
    //        or the sequence of Pauli Z and Pauli X gates (equivalent to applying the Z gate followed by the X gate).
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the Y gate,
    //         1 if the given operation is the XZ gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants at most twice.
    operation DistinguishYfromXZ (unitary : (Qubit => Unit is Adj+Ctl)) : Int {
        using (qs = Qubit[2]) {
            within {
                ApplyToEachA(H, Most(qs));
            }
            apply {
                Controlled unitary([qs[0]], qs[1]);
                Controlled unitary([qs[0]], qs[1]);
            }
            return ResultArrayAsInt(MultiM(qs));
        }
    }
    

    // Task 1.8. Y, XZ, -Y or -XZ?
    // Input: An operation that implements a single-qubit unitary transformation:
    //        either the Pauli Y gate (possibly with an extra global phase of -1)
    //        or the sequence of Pauli Z and Pauli X gates (possibly with an extra global phase of -1).
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the Y gate,
    //         1 if the given operation is the -XZ gate,
    //         2 if the given operation is the -Y gate,
    //         3 if the given operation is the XZ gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants at most three times.
    operation DistinguishYfromXZWithPhases (unitary : (Qubit => Unit is Adj+Ctl)) : Int {
        let YorXZ = DistinguishYfromXZ(unitary);
        using (qs = Qubit[2]) {
            within {
                ApplyToEachA(H, qs);
            }
            apply {
                if (YorXZ == 0) {
                    Controlled Y([qs[1]], qs[0]);
                }
                else {
                   Controlled X([qs[1]], qs[0]);
                   Controlled Z([qs[1]], qs[0]);
                }
                Controlled Adjoint unitary([qs[1]], qs[0]);
            }
            return ResultArrayAsInt(MultiM(qs)) + YorXZ;
        }
    }


    // Task 1.9. Rz or Ry (fixed angle)?
    // Inputs:
    //      1) An angle θ ∊ [0.01π; 0.99π].
    //      2) An operation that implements a single-qubit unitary transformation:
    //         either the Rz(θ) gate
    //         or the Ry(θ) gate.
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the Rz(θ) gate,
    //         1 if the given operation is the Ry(θ) gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants any number of times.
    operation DistinguishRzFromRy (theta : Double, unitary : (Qubit => Unit is Adj+Ctl)) : Int {
        // mutable count = 0.0;
        // repeat {
        //     set count = count + 1.0;
        // }
        // until ((count + 1.0) * theta > PI() * 1.2 or count * theta == PI());
        // mutable limit = 10;
        // mutable result = Zero;
        // repeat {
        //     using (q = Qubit()) {
        //         for (times in 1..Floor(count)) {
        //             unitary(q);
        //         }
        //         set result = MResetZ(q);
        //     }
        // }
        // until (result == One or limit == 1)
        // fixup {
        //     set limit = limit - 1;
        // }
        // return ResultArrayAsInt([result]);
        return Floor(EstimateOverlapBetweenStates(ApplyToEachA(unitary, _), ApplyToEachA(Ry(theta, _), _), 1, 1000000));
    }


    // Task 1.10*. Rz or R1 (fixed angle)?
    // Inputs:
    //      1) An angle θ ∊ [0.01π; 0.99π].
    //      2) An operation that implements a single-qubit unitary transformation:
    //         either the Rz(θ) gate
    //         or the R1(θ) gate.
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the Rz(θ) gate,
    //         1 if the given operation is the R1(θ) gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants any number of times.
    operation DistinguishRzFromR1WithAngle (theta : Double, unitary : (Qubit => Unit is Adj+Ctl)) : Int {
        // mutable count = 0.0;
        // repeat {
        //     set count = count + 1.0;
        // }
        // until ((count + 1.0) * theta > 2.0 * PI());
        // mutable limit = 100.0 * ((2.0 * PI() / theta) - count);
        // mutable isRz = 0;
        // mutable isR1 = 0;
        // for (looping in 1..Floor(limit)) {
        //     using (qs = Qubit[2]) {
        //         ApplyToEach(H, qs);
        //         for (times in 1..Floor(count)) {
        //             Controlled unitary([qs[0]], qs[1]);
        //         }
        //         // Controlled Rz ?
        //         H(qs[0]);
        //         if (M(qs[0]) == One) {
        //             set isRz = isRz + 1;
        //         }
        //         else {
        //             set isR1 = isR1 + 1;
        //         }
        //         Reset(qs[1]);
        //     }
        // }
        // return isRz > isR1 ? 0 | 1;
        return Floor(EstimateRealOverlapBetweenStates(ApplyToEachA(H, _),ApplyToEachCA(unitary, _), ApplyToEachCA(R1(theta, _), _), 1, 1000000));
    }

    
    // Task 1.11. Distinguish 4 Pauli unitaries
    // Input: An operation that implements a single-qubit unitary transformation:
    //        either the identity (I gate) or one of the Pauli gates (X, Y or Z gate).
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the I gate,
    //         1 if the given operation is the X gate,
    //         2 if the given operation is the Y gate,
    //         3 if the given operation is the Z gate,
    // You are allowed to apply the given operation and its adjoint/controlled variants exactly once.
    operation DistinguishPaulis (unitary : (Qubit => Unit is Adj+Ctl)) : Int {
        using (qs = Qubit[2]) {
            within {
                PrepareEntangledState(Most(qs), Rest(qs));
            }
            apply {
                unitary(Head(qs));
            }
            CNOT(Head(qs), Tail(qs));
            return ResultArrayAsInt(Reversed(MultiM(qs)));
        }
    }


    //////////////////////////////////////////////////////////////////
    // Part II. Multi-Qubit Gates
    //////////////////////////////////////////////////////////////////
    
    // Task 2.1. I ⊗ X or CNOT?
    // Input: An operation that implements a two-qubit unitary transformation:
    //        either I ⊗ X (the X gate applied to the second qubit)
    //        or the CNOT gate with the first qubit as control and the second qubit as target.
    // The operation will accept an array of qubits as input, but it will fail if the array is empty or has one or more than two qubits.
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is I ⊗ X,
    //         1 if the given operation is the CNOT gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants exactly once.
    operation DistinguishIXfromCNOT (unitary : (Qubit[] => Unit is Adj+Ctl)) : Int {
        using (qs = Qubit[2]) {
            unitary(qs);
            return M(qs[1]) == One ? 0 | 1;
        }
    }
    

    // Task 2.2. Figure out the direction of CNOT
    // Input: An operation that implements a two-qubit unitary transformation:
    //        either the CNOT gate with the first qubit as control and the second qubit as target (CNOT₁₂),
    //        or the CNOT gate with the second qubit as control and the first qubit as target (CNOT₂₁).
    // The operation will accept an array of qubits as input, but it will fail if the array is empty or has one or more than two qubits.
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is CNOT₁₂,
    //         1 if the given operation is CNOT₂₁.
    // You are allowed to apply the given operation and its adjoint/controlled variants exactly once.
    operation CNOTDirection (unitary : (Qubit[] => Unit is Adj+Ctl)) : Int {
        using(qs = Qubit[2]) {
            X(qs[1]);
            unitary(qs);
            let r = M(qs[0]);
            X(qs[1]);
            return r == One ? 1 | 0;
        }
    }


    // Task 2.3. CNOT₁₂ or SWAP?
    // Input: An operation that implements a two-qubit unitary transformation:
    //        either the CNOT gate with the first qubit as control and the second qubit as target (CNOT₁₂)
    //        or the SWAP gate.
    // The operation will accept an array of qubits as input, but it will fail if the array is empty or has one or more than two qubits.
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the CNOT₁₂ gate,
    //         1 if the given operation is the SWAP gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants exactly once.
    operation DistinguishCNOTfromSWAP (unitary : (Qubit[] => Unit is Adj+Ctl)) : Int {
        using (qs = Qubit[2]) {
            X(qs[1]);
            unitary(qs);
            return ResultArrayAsInt(Reversed(MultiM(qs))) - 1;
        }
    }


    // Task 2.4. Identity, CNOTs or SWAP?
    // Input: An operation that implements a two-qubit unitary transformation:
    //        either the identity (I ⊗ I gate), 
    //        the CNOT gate with one of the qubits as control and the other qubit as a target, 
    //        or the SWAP gate.
    // The operation will accept an array of qubits as input, but it will fail if the array is empty or has one or more than two qubits.
    // The operation will have Adjoint and Controlled variants defined.
    // Output: 0 if the given operation is the I ⊗ I gate,
    //         1 if the given operation is the CNOT₁₂ gate,
    //         2 if the given operation is the CNOT₂₁ gate,
    //         3 if the given operation is the SWAP gate.
    // You are allowed to apply the given operation and its adjoint/controlled variants at most twice.
    operation DistinguishTwoQubitUnitaries (unitary : (Qubit[] => Unit is Adj+Ctl)) : Int {
        using (qs = Qubit[2]) {
            ApplyToEach(X, qs);
            unitary(qs);
            let i = ResultArrayAsInt(MultiM(qs));
            if (i < 3) {
                return 1 + CNOTDirection(unitary);
            }
            else {
                X(qs[0]);
                unitary(qs);
                if (M(qs[0]) == One) {
                    return 3;
                }
                else {
                    X(qs[1]);
                    return 0;
                }
            }
        }
    }
}
