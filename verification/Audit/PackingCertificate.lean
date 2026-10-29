import SymplecticPacking.Effective.PackingCertificateTarget
import SymplecticPacking.Explicit

/-!
# Finite packing certificates

Axioms of the finite cell, plateau and target checks, their explicitness, and sample
evaluations on small tables.
-/

open SymplecticPacking.Effective.PackingCertificate

#print axioms grid_error
#print axioms exists_time_cell
#print axioms time_error
#print axioms plateauCheck_sound
#print axioms targetCheck_sound
#print axioms outsideCheck_false_of_covered
#print axioms cellCheck_of_covered

#check_explicit error
#check_explicit plateauCheck
#check_explicit sqNorm
#check_explicit targetCheck
#check_explicit outsideCheck
#check_explicit cellCheck

-- A genuine finite table: x'=1 in one coordinate, ten exact Euler steps.
#eval cellCheck 10 (fun i (_ : Fin 1) => (i:ℚ)/10)
  (fun _ => 0) 0 (1/10) 0 2 (11/10)
-- The whole closed source cell cannot be rejected when its centre is covered.
#eval outsideCheck (fun _ : Fin 1 => (0:ℚ)) (fun _ => 0) (1/10) (1/10)
-- A target test touching the boundary must fail (strict open target).
#eval targetCheck (fun _ : Fin 1 => (1:ℚ)) 0 1
